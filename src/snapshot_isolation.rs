//! Snapshot-isolation store.
//!
//! Each cell carries a chain of `(commit_time, value)` versions, oldest
//! first. Reads return the latest version with `commit_time <=
//! snapshot_time`. Writes pass commit-time validation: no version of any
//! cell in the read_set may have `commit_time > snapshot_time`.
//!
//! No-write commits (read-only operations) bypass validation. This is the
//! semantic gap surfaced by the SI/triage 3% finding (§5.5 of the paper).
//! A strengthened SSI variant (read-set serialisation) closes the gap; see
//! the `validate_no_write` flag.
//!
//! Commit-time validation is delegated to `crate::verified_si::validate_fresh`,
//! whose decision logic is the Verus exec-verified `validate`
//! (lib_si_validate_exec.rs, sound + complete against snapshot freshness). The
//! version-map flatten and string interning are the only unverified marshalling
//! and rest on documented correspondences.

use crate::oprecord::{CellId, Time, Value};
use crate::store::{CommitOutcome, Snapshot, Store};
use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Default)]
struct Inner {
    /// Cell -> versions, in commit-time order (oldest first).
    versions: BTreeMap<CellId, Vec<(Time, Value)>>,
    clock: Time,
}

pub struct SnapshotIsolationStore {
    inner: Mutex<Inner>,
    aborts: AtomicU64,
    /// If true, validate even on no-write commits (SSI mode). Closes the
    /// SI/triage gap at the cost of additional aborts.
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

        // Decide whether to validate. SI default: validate only on writes.
        // SSI mode: validate on every commit. The validation predicate itself
        // is the Verus exec-verified gate (sound + complete vs freshness).
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

    /// Reproduce the SI/triage 3% gap: triager reads stale, no writes,
    /// SI without SSI mode does not abort.
    ///
    /// The ordering matters: the triager must begin BETWEEN reporter's two
    /// writes, so its snapshot captures v0 while reporter's second write
    /// (v1) lands before the triager's no-write commit.
    #[test]
    fn si_default_does_not_abort_no_write_commits() {
        let s = SnapshotIsolationStore::new();

        // Reporter writes 'ticket' = v0 (commit_time = 1).
        let snap0 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap0, &btreemap("ticket", "v0"));

        // Triager begins NOW (read_time = 1, sees v0).
        let snap_t = s.begin("tri", &[s_str("ticket")]).unwrap();
        assert_eq!(snap_t.values["ticket"], "v0");

        // Reporter writes 'ticket' = v1 (commit_time = 2) AFTER triager's begin.
        let snap1 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap1, &btreemap("ticket", "v1"));

        // Triager commit with empty writes: SI default does NOT validate,
        // so this succeeds even though the triager's read is now stale
        // relative to reporter's second commit. THIS IS THE GAP.
        match s.commit("tri", &snap_t, &BTreeMap::new()) {
            CommitOutcome::Committed { .. } => {}
            CommitOutcome::AbortedConflict => panic!("should not abort under SI default"),
        }
    }

    /// SSI mode (validate_no_write=true) closes the gap.
    #[test]
    fn ssi_mode_aborts_no_write_commits_with_stale_reads() {
        let s = SnapshotIsolationStore::with_ssi(true);
        let snap0 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap0, &btreemap("ticket", "v0"));
        let snap_t = s.begin("tri", &[s_str("ticket")]).unwrap();
        let snap1 = s.begin("rep", &[]).unwrap();
        s.commit("rep", &snap1, &btreemap("ticket", "v1"));
        // Triager's snap_t.read_time was clock=1; reporter's second commit
        // is at commit_time=2, which is > read_time. SSI should abort.
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