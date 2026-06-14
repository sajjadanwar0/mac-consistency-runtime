use crate::oprecord::{CellId, Time, Value};
use crate::store::{CommitOutcome, Snapshot, Store};
use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Default)]
struct Inner {
    versions: BTreeMap<CellId, Vec<(Time, Value)>>,
    clock: Time,
}

pub struct SnapshotIsolationStore {
    inner: Mutex<Inner>,
    aborts: AtomicU64,
    pub validate_no_write: bool,
}

impl SnapshotIsolationStore {
    pub fn new() -> Self {
        Self::with_ssi(false)
    }

    pub fn with_ssi(validate_no_write: bool) -> Self {
        Self {
            inner: Mutex::new(Inner::default()),
            aborts: AtomicU64::new(0),
            validate_no_write,
        }
    }
}

impl Default for SnapshotIsolationStore {
    fn default() -> Self {
        Self::new()
    }
}

impl Store for SnapshotIsolationStore {
    fn begin(&self, _agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str> {
        let g = self.inner.lock();
        let read_time = g.clock;
        
        let values = cells
            .iter()
            .map(|c| {
                let v = g.versions.get(c).map_or_else(
                    || "NULL".to_string(),
                    |chain| {
                        let mut latest = "NULL".to_string();
                        for (ct, v) in chain {
                            if *ct <= read_time {
                                latest = v.clone();
                            } else {
                                break;
                            }
                        }
                        latest
                    },
                );
                (c.clone(), v)
            })
            .collect();
        Ok(Snapshot { values, read_time })
    }

    fn commit(
        &self,
        _agent: &str,
        snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome {
        let mut g = self.inner.lock();

        let read_set: Vec<CellId> = snapshot.values.keys().cloned().collect();

        let needs_validation = !writes.is_empty() || self.validate_no_write;
        
        if needs_validation
            && !crate::verified_si::validate_fresh(&g.versions, &read_set, snapshot.read_time)
        {
            self.aborts.fetch_add(1, Ordering::Relaxed);
            return CommitOutcome::AbortedConflict;
        }

        g.clock += 1;
        let commit_time = g.clock;
        for (k, v) in writes {
            g.versions
                .entry(k.clone())
                .or_default()
                .push((commit_time, v.clone()));
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

    fn release(&self, _agent: &str) {}

    fn aborts(&self) -> u64 {
        self.aborts.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn si_default_does_not_abort_no_write_commits() {
        let s = SnapshotIsolationStore::new();

        let snap0 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap0, &btreemap("ticket", "v0"));

        let snap_t = s.begin("tri", &[s_str("ticket")]).unwrap();
        assert_eq!(snap_t.values["ticket"], "v0");

        let snap1 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap1, &btreemap("ticket", "v1"));

        match s.commit("tri", &snap_t, &BTreeMap::new()) {
            CommitOutcome::Committed { .. } => {}
            CommitOutcome::AbortedConflict => panic!("should not abort under SI default"),
        }
    }

    #[test]
    fn ssi_mode_aborts_no_write_commits_with_stale_reads() {
        let s = SnapshotIsolationStore::with_ssi(true);
        let snap0 = s.begin("rep", &[]).unwrap();

        s.commit("rep", &snap0, &btreemap("ticket", "v0"));

        let snap_t = s.begin("tri", &[s_str("ticket")]).unwrap();
        let snap1 = s.begin("rep", &[]).unwrap();

        s.commit("rep", &snap1, &btreemap("ticket", "v1"));

        match s.commit("tri", &snap_t, &BTreeMap::new()) {
            CommitOutcome::Committed { .. } => panic!("SSI should abort"),
            CommitOutcome::AbortedConflict => {}
        }
    }

    fn btreemap(k: &str, v: &str) -> BTreeMap<CellId, Value> {
        let mut m = BTreeMap::new();
        m.insert(k.to_string(), v.to_string());
        m
    }

    fn s_str(s: &str) -> CellId {
        s.to_string()
    }
}