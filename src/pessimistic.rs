use crate::oprecord::{CellId, Time, Value};
use crate::store::{CommitOutcome, Snapshot, Store};
use parking_lot::Mutex;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Default)]
struct Inner {
    data: BTreeMap<CellId, Value>,
    clock: Time,
    cell_holders: HashMap<CellId, String>,
    agent_holds: HashMap<String, HashSet<CellId>>,
}

pub struct PessimisticStore {
    inner: Mutex<Inner>,
    begin_conflicts: AtomicU64,
}

impl PessimisticStore {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(Inner::default()),
            begin_conflicts: AtomicU64::new(0),
        }
    }
}

impl Default for PessimisticStore {
    fn default() -> Self {
        Self::new()
    }
}

impl Store for PessimisticStore {
    fn begin(&self, agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str> {
        let mut g = self.inner.lock();

        for c in cells {
            if let Some(holder) = g.cell_holders.get(c) {
                if holder != agent {
                    self.begin_conflicts.fetch_add(1, Ordering::Relaxed);
                    return Err("conflict on cell");
                }
            }
        }

        for c in cells {
            g.cell_holders.insert(c.clone(), agent.to_string());
            g.agent_holds
                .entry(agent.to_string())
                .or_default()
                .insert(c.clone());
        }

        let values = cells
            .iter()
            .map(|c| {
                (
                    c.clone(),
                    g.data.get(c).cloned().unwrap_or_else(|| "NULL".to_string()),
                )
            })
            .collect();
        Ok(Snapshot {
            values,
            read_time: g.clock,
        })
    }

    fn commit(
        &self,
        agent: &str,
        _snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome {
        let mut g = self.inner.lock();

        let new_writes: Vec<CellId> = writes
            .keys()
            .filter(|c| !g.cell_holders.get(*c).is_some_and(|h| h == agent))
            .cloned()
            .collect();

        for c in &new_writes {
            if g.cell_holders.contains_key(c) {
                return CommitOutcome::AbortedConflict;
            }
        }
        
        for c in &new_writes {
            g.cell_holders.insert(c.clone(), agent.to_string());
            g.agent_holds
                .entry(agent.to_string())
                .or_default()
                .insert(c.clone());
        }

        g.clock += 1;

        let commit_time = g.clock;

        for (k, v) in writes {
            g.data.insert(k.clone(), v.clone());
        }

        CommitOutcome::Committed {
            write_time: commit_time,
        }
    }

    fn tick(&self) -> Time {
        let mut g = self.inner.lock();
        g.clock += 1;
        g.clock
    }

    fn release(&self, agent: &str) {
        let mut g = self.inner.lock();
        if let Some(cells) = g.agent_holds.remove(agent) {
            for c in cells {
                if let Some(holder) = g.cell_holders.get(&c) {
                    if holder == agent {
                        g.cell_holders.remove(&c);
                    }
                }
            }
        }
    }

    fn begin_conflicts(&self) -> u64 {
        self.begin_conflicts.load(Ordering::Relaxed)
    }
}