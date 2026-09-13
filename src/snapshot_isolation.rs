use crate::oprecord::{CellId, Time, Value};
use crate::si_concurrent::{SiConcurrent, Snapshot as SiSnapshot};
use crate::store::{CommitOutcome, Snapshot, Store};
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::RwLock as StdRwLock;

// =====================================================================
// Round 4 (13 Sep 2026): the critical section of the deployed
// snapshot-isolation store is the VERIFIED concurrent store
// `si_concurrent::SiConcurrent` (verus-detector/src/lib_si_concurrent.rs,
// compiled here by plain cargo with proofs erased).  Its only access path
// is vstd's verified reader-writer lock carrying the SI safety invariant
// as the lock predicate, so (i) no thread can install a store state that
// violates the invariant, under any interleaving, with nothing assumed
// about the lock, and (ii) a panic inside a critical section cannot leave
// a torn store -- the round-1 gap (parking_lot::Mutex does not poison)
// is closed at the root, not by relabeling.
//
// What did NOT change: the public API (new / with_ssi / Store / aborts),
// the validation decision (the verified `validate` gate, now called
// inside the verified store), and the two modes:
//   default-SI  (new / with_ssi(false)): a no-write commit bypasses
//               validation -- the A_1-admitting path the paper measures
//               (Table 4: 5% edit-review, 8% triage);
//   SSI         (with_ssi(true)): every commit validates its read set.
//
// What is outside the verified store: the string<->id interning of cell
// and value names (a std::sync::RwLock over an append-only dictionary,
// never held across the verified lock) and the abort counter.  Neither
// is safety-bearing: the verified store decides commits over ids, and the
// interner is a bijection maintained under its own lock.
// =====================================================================

const NULL: &str = "NULL";

/// String <-> id bijection for agents, cells, and values.  Id 0 is
/// reserved for the NULL sentinel, so the verified store's "no version"
/// answer (value id 0) and an explicit "NULL" write coincide -- as they
/// did in the pre-round-4 store, which returned the string "NULL" for an
/// unwritten cell.
struct Interner {
    to_id: HashMap<String, usize>,
    from_id: Vec<String>,
}

impl Interner {
    fn new() -> Self {
        let mut i = Interner { to_id: HashMap::new(), from_id: Vec::new() };
        let null = i.intern(NULL);
        debug_assert_eq!(null, 0);
        i
    }

    fn intern(&mut self, s: &str) -> usize {
        if let Some(&id) = self.to_id.get(s) {
            return id;
        }
        let id = self.from_id.len();
        self.from_id.push(s.to_string());
        self.to_id.insert(s.to_string(), id);
        id
    }

    fn name(&self, id: usize) -> &str {
        &self.from_id[id]
    }
}

pub struct SnapshotIsolationStore {
    core: SiConcurrent,
    names: StdRwLock<Interner>,
    aborts: AtomicU64,
    pub validate_no_write: bool,
}

// The Store trait requires Send + Sync (Arc<dyn Store> in the agent
// layer).  SiConcurrent holds vstd::rwlock::RwLock<SiStore, SiPred>, whose
// Send/Sync derive from its fields (PCell, ghost atomics, Ghost/Tracked
// markers).  This never-called function makes a failure of that
// derivation a named compile error here rather than at a use site.
#[allow(dead_code)]
fn assert_store_is_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<SnapshotIsolationStore>();
}

impl SnapshotIsolationStore {
    pub fn new() -> Self {
        Self::with_ssi(false)
    }

    pub fn with_ssi(validate_no_write: bool) -> Self {
        Self {
            core: SiConcurrent::new(),
            names: StdRwLock::new(Interner::new()),
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
    fn begin(&self, agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str> {
        let (agent_id, cell_ids) = {
            let mut n = self.names.write().unwrap();
            let a = n.intern(agent);
            let cs: Vec<usize> = cells.iter().map(|c| n.intern(c)).collect();
            (a, cs)
        };
        // verified: read_time == clock at the read; one (cell, value) per
        // requested cell, value id 0 (NULL) when the cell has no version
        let snap = self.core.begin(agent_id, cell_ids);
        let n = self.names.read().unwrap();
        let values: BTreeMap<CellId, Value> = snap
            .read_values
            .iter()
            .map(|(c, v)| (n.name(*c).to_string(), n.name(*v).to_string()))
            .collect();
        Ok(Snapshot { values, read_time: snap.read_time })
    }

    fn commit(
        &self,
        agent: &str,
        snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome {
        let needs_validation = !writes.is_empty() || self.validate_no_write;
        if !needs_validation {
            // default-SI: a no-write commit ticks the clock without
            // validating the read set.  This is the read-only bypass that
            // admits A_1 by design; SSI mode (validate_no_write) closes it.
            let t = self.core.tick();
            return CommitOutcome::Committed { write_time: t };
        }

        let (agent_id, read_cells, write_pairs) = {
            let mut n = self.names.write().unwrap();
            let a = n.intern(agent);
            let rc: Vec<usize> = snapshot.values.keys().map(|c| n.intern(c)).collect();
            let wp: Vec<(usize, usize)> = writes
                .iter()
                .map(|(c, v)| (n.intern(c), n.intern(v)))
                .collect();
            (a, rc, wp)
        };
        let si_snap = SiSnapshot {
            agent: agent_id,
            read_time: snapshot.read_time,
            read_cells,
            read_values: Vec::new(),
        };
        // verified: validates the read set against every version committed
        // after read_time (the same `validate` gate as before), and on
        // success advances the clock and appends one version per write,
        // all under the verified lock
        let (ok, t) = self.core.commit(si_snap, &write_pairs);
        if ok {
            CommitOutcome::Committed { write_time: t }
        } else {
            self.aborts.fetch_add(1, Ordering::Relaxed);
            CommitOutcome::AbortedConflict
        }
    }

    fn tick(&self) -> Time {
        self.core.tick()
    }

    fn release(&self, _agent: &str) {}

    fn aborts(&self) -> u64 {
        self.aborts.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

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
        assert_eq!(s.aborts(), 1);
    }

    #[test]
    fn unwritten_cell_reads_null_and_written_cell_reads_latest() {
        let s = SnapshotIsolationStore::with_ssi(true);
        let snap = s.begin("a", &[s_str("x")]).unwrap();
        assert_eq!(snap.values["x"], "NULL");
        assert_eq!(snap.read_time, 0);
        match s.commit("a", &snap, &btreemap("x", "one")) {
            CommitOutcome::Committed { write_time } => assert_eq!(write_time, 1),
            _ => panic!("first write must commit"),
        }
        let snap2 = s.begin("b", &[s_str("x")]).unwrap();
        assert_eq!(snap2.values["x"], "one");
        assert_eq!(snap2.read_time, 1);
        match s.commit("b", &snap2, &btreemap("x", "two")) {
            CommitOutcome::Committed { write_time } => assert_eq!(write_time, 2),
            _ => panic!("second write must commit"),
        }
        let snap3 = s.begin("c", &[s_str("x")]).unwrap();
        assert_eq!(snap3.values["x"], "two");
    }

    #[test]
    fn stale_read_set_aborts_and_clock_does_not_advance() {
        let s = SnapshotIsolationStore::with_ssi(true);
        let reader = s.begin("r", &[s_str("x")]).unwrap();
        let writer = s.begin("w", &[]).unwrap();
        s.commit("w", &writer, &btreemap("x", "v"));
        let clock_before = s.tick();
        match s.commit("r", &reader, &btreemap("y", "derived-from-stale-x")) {
            CommitOutcome::AbortedConflict => {}
            _ => panic!("a write to a cell read before an intervening commit must abort"),
        }
        assert_eq!(s.aborts(), 1);
        // an aborted commit leaves the clock where it was (tick advanced it once)
        assert_eq!(s.tick(), clock_before + 1);
    }

    /// The verified lock under real OS threads: no panics, every commit
    /// applied, and the clock equals the number of successful commits.
    #[test]
    fn concurrent_disjoint_writers_all_commit_under_the_verified_lock() {
        let s = Arc::new(SnapshotIsolationStore::with_ssi(true));
        let threads = 8;
        let per = 25;
        let handles: Vec<_> = (0..threads)
            .map(|i| {
                let s = Arc::clone(&s);
                thread::spawn(move || {
                    let cell = format!("cell-{i}");
                    let mut ok = 0;
                    for k in 0..per {
                        let snap = s.begin(&format!("agent-{i}"), &[cell.clone()]).unwrap();
                        match s.commit(&format!("agent-{i}"), &snap, &btreemap(&cell, &format!("v{k}"))) {
                            CommitOutcome::Committed { .. } => ok += 1,
                            CommitOutcome::AbortedConflict => {}
                        }
                    }
                    ok
                })
            })
            .collect();
        let committed: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
        // disjoint cells never conflict, so every commit applies
        assert_eq!(committed, (threads * per) as u64);
        assert_eq!(s.aborts(), 0);
        // clock == commits so far; tick returns clock + 1
        assert_eq!(s.tick(), committed + 1);
    }

    /// Two threads contending on one cell: at most one of any pair of
    /// overlapping commits survives validation; committed + aborted equals
    /// attempts; the clock advances once per committed write.
    #[test]
    fn concurrent_contended_writers_never_both_commit_overlapping_windows() {
        let s = Arc::new(SnapshotIsolationStore::with_ssi(true));
        let attempts_per = 50;
        let handles: Vec<_> = (0..2)
            .map(|i| {
                let s = Arc::clone(&s);
                thread::spawn(move || {
                    let mut ok = 0u64;
                    for k in 0..attempts_per {
                        let snap = s.begin(&format!("t{i}"), &[s_str("hot")]).unwrap();
                        if let CommitOutcome::Committed { .. } =
                            s.commit(&format!("t{i}"), &snap, &btreemap("hot", &format!("t{i}-{k}")))
                        {
                            ok += 1;
                        }
                    }
                    ok
                })
            })
            .collect();
        let committed: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
        assert_eq!(committed + s.aborts(), 2 * attempts_per as u64);
        assert!(committed >= attempts_per as u64, "one writer at a time always succeeds");
        assert_eq!(s.tick(), committed + 1);
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
