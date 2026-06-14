use crate::oprecord::{CellId, Time, Value};
use crate::store::{CommitOutcome, Snapshot, Store};
use parking_lot::Mutex;
use std::collections::BTreeMap;

#[derive(Default)]
struct Inner {
    data: BTreeMap<CellId, Value>,
    clock: Time,
}

pub struct VanillaStore {
    inner: Mutex<Inner>,
}

impl VanillaStore {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(Inner::default()),
        }
    }
}

impl Default for VanillaStore {
    fn default() -> Self {
        Self::new()
    }
}

impl Store for VanillaStore {
    fn begin(&self, _agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str> {
        let g = self.inner.lock();
        let values = cells
            .iter()
            .map(|c| (c.clone(), g.data.get(c).cloned().unwrap_or_else(|| "NULL".to_string())))
            .collect();
        Ok(Snapshot {
            values,
            read_time: g.clock,
        })
    }

    fn commit(
        &self,
        _agent: &str,
        _snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome {
        let mut g = self.inner.lock();
        g.clock += 1;
        for (k, v) in writes {
            g.data.insert(k.clone(), v.clone());
        }
        CommitOutcome::Committed {
            write_time: g.clock,
        }
    }

    fn tick(&self) -> Time {
        let mut g = self.inner.lock();
        g.clock += 1;
        g.clock
    }

    fn release(&self, _agent: &str) {}
}
