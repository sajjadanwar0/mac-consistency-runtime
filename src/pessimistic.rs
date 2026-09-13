use crate::oprecord::{CellId, Time, Value};
use crate::pess_concurrent::{PessConcurrent, Snapshot as PessSnapshot};
use crate::store::{CommitOutcome, Snapshot, Store};
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::RwLock as StdRwLock;

// =====================================================================
// Round 5 (13 Sep 2026): the critical section of the deployed
// pessimistic-locking store is the VERIFIED concurrent store
// `pess_concurrent::PessConcurrent` (verus-detector/src/lib_pess_concurrent.rs,
// compiled here by plain cargo with proofs erased).  Its only access path
// is vstd's verified reader-writer lock carrying the store invariant as
// the lock predicate: exclusive holders, no foreign write to a held cell
// since the hold began, and no cross-agent stale-generation window in the
// emitted trace.  Nothing is assumed about the lock, and a panic inside a
// critical section cannot install a torn store.
//
// With this file and si_concurrent.rs, no deployed store in this crate
// locks with parking_lot::Mutex, and the three RUSTBELT_OBLIGATION stubs
// have no deployed runtime left to cover.
//
// What did NOT change: the public API (new / Store / begin_conflicts),
// the discipline (refuse a begin whose cells are held by another agent;
// refuse a commit whose write cells are held by another agent; release
// drops the agent's holds), and the conflict counter.
//
// Outside the verified store: the string<->id interning of agent, cell,
// and value names (an append-only bijection under its own lock, never
// held across the verified lock) and the conflict counter.  Neither
// decides a begin or a commit.
// =====================================================================

const NULL: &str = "NULL";

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

pub struct PessimisticStore {
    core: PessConcurrent,
    names: StdRwLock<Interner>,
    begin_conflicts: AtomicU64,
}

// Store requires Send + Sync (Arc<dyn Store>).  A failure of the
// derivation for RwLock<PessStore, PessPred> becomes a named compile
// error here rather than at a use site.
#[allow(dead_code)]
fn assert_store_is_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<PessimisticStore>();
}

impl PessimisticStore {
    pub fn new() -> Self {
        Self {
            core: PessConcurrent::new(),
            names: StdRwLock::new(Interner::new()),
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
        let (agent_id, cell_ids) = {
            let mut n = self.names.write().unwrap();
            let a = n.intern(agent);
            let cs: Vec<usize> = cells.iter().map(|c| n.intern(c)).collect();
            (a, cs)
        };
        // verified: refuses if any cell is held by another agent; otherwise
        // holds every cell for this agent from the current clock
        match self.core.begin(agent_id, cell_ids) {
            None => {
                self.begin_conflicts.fetch_add(1, Ordering::Relaxed);
                Err("conflict on cell")
            }
            Some(snap) => {
                let n = self.names.read().unwrap();
                let values: BTreeMap<CellId, Value> = snap
                    .read_values
                    .iter()
                    .map(|(c, v)| (n.name(*c).to_string(), n.name(*v).to_string()))
                    .collect();
                Ok(Snapshot { values, read_time: snap.read_time })
            }
        }
    }

    fn commit(
        &self,
        agent: &str,
        snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome {
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
        let snap = PessSnapshot {
            agent: agent_id,
            read_time: snapshot.read_time,
            read_cells,
            read_values: Vec::new(),
        };
        // verified: refuses unless every read cell is held by this agent
        // since no later than read_time and every write cell is free or
        // held by this agent; otherwise acquires, ticks, appends
        let (ok, t) = self.core.commit(snap, &write_pairs);
        if ok {
            CommitOutcome::Committed { write_time: t }
        } else {
            CommitOutcome::AbortedConflict
        }
    }

    fn tick(&self) -> Time {
        self.core.tick()
    }

    fn release(&self, agent: &str) {
        let agent_id = {
            let mut n = self.names.write().unwrap();
            n.intern(agent)
        };
        self.core.release(agent_id);
    }

    fn begin_conflicts(&self) -> u64 {
        self.begin_conflicts.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn second_agent_is_refused_a_held_cell_until_release() {
        let s = PessimisticStore::new();
        let a = s.begin("a", &[cell("x")]).unwrap();
        assert_eq!(a.values["x"], "NULL");
        assert!(s.begin("b", &[cell("x")]).is_err(), "b must not take a's cell");
        assert_eq!(s.begin_conflicts(), 1);
        s.release("a");
        assert!(s.begin("b", &[cell("x")]).is_ok(), "after release b may take it");
    }

    #[test]
    fn holder_commits_and_the_next_holder_reads_the_new_value() {
        let s = PessimisticStore::new();
        let snap = s.begin("a", &[cell("x")]).unwrap();
        match s.commit("a", &snap, &kv("x", "one")) {
            CommitOutcome::Committed { write_time } => assert_eq!(write_time, 1),
            _ => panic!("the holder's commit must succeed"),
        }
        s.release("a");
        let snap2 = s.begin("b", &[cell("x")]).unwrap();
        assert_eq!(snap2.values["x"], "one");
        assert_eq!(snap2.read_time, 1);
    }

    #[test]
    fn commit_without_holding_the_read_set_is_refused() {
        let s = PessimisticStore::new();
        let snap = s.begin("a", &[cell("x")]).unwrap();
        s.release("a"); // drop the hold before committing
        match s.commit("a", &snap, &kv("x", "v")) {
            CommitOutcome::AbortedConflict => {}
            _ => panic!("a commit whose read set is no longer held must be refused"),
        }
    }

    /// Eight threads on disjoint cells: every begin succeeds, every commit
    /// lands, and the clock equals the number of commits.
    #[test]
    fn concurrent_disjoint_agents_all_commit_under_the_verified_lock() {
        let s = Arc::new(PessimisticStore::new());
        let threads = 8;
        let per = 25;
        let handles: Vec<_> = (0..threads)
            .map(|i| {
                let s = Arc::clone(&s);
                thread::spawn(move || {
                    let agent = format!("agent-{i}");
                    let c = format!("cell-{i}");
                    let mut ok = 0u64;
                    for k in 0..per {
                        let snap = s.begin(&agent, &[c.clone()]).unwrap();
                        if let CommitOutcome::Committed { .. } =
                            s.commit(&agent, &snap, &kv(&c, &format!("v{k}")))
                        {
                            ok += 1;
                        }
                        s.release(&agent);
                    }
                    ok
                })
            })
            .collect();
        let committed: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
        assert_eq!(committed, (threads * per) as u64);
        assert_eq!(s.begin_conflicts(), 0, "disjoint cells must not conflict");
        assert_eq!(s.tick(), committed + 1);
    }

    /// Two threads contending on one cell: a begin either wins the hold or
    /// is refused; every begin that wins commits; refusals are counted; no
    /// attempt is lost.
    #[test]
    fn concurrent_contended_agents_never_share_a_cell() {
        let s = Arc::new(PessimisticStore::new());
        let attempts = 100;
        let handles: Vec<_> = (0..2)
            .map(|i| {
                let s = Arc::clone(&s);
                thread::spawn(move || {
                    let agent = format!("t{i}");
                    let mut committed = 0u64;
                    let mut refused = 0u64;
                    for k in 0..attempts {
                        match s.begin(&agent, &[cell("hot")]) {
                            Err(_) => refused += 1,
                            Ok(snap) => {
                                match s.commit(&agent, &snap, &kv("hot", &format!("t{i}-{k}"))) {
                                    CommitOutcome::Committed { .. } => committed += 1,
                                    CommitOutcome::AbortedConflict => {}
                                }
                                s.release(&agent);
                            }
                        }
                    }
                    (committed, refused)
                })
            })
            .collect();
        let (mut committed, mut refused) = (0u64, 0u64);
        for h in handles {
            let (c, r) = h.join().unwrap();
            committed += c;
            refused += r;
        }
        assert_eq!(committed + refused, 2 * attempts as u64, "no attempt is lost");
        assert_eq!(s.begin_conflicts(), refused, "every refusal is counted once");
        assert_eq!(s.tick(), committed + 1, "the clock counts exactly the commits");
    }

    fn kv(k: &str, v: &str) -> BTreeMap<CellId, Value> {
        let mut m = BTreeMap::new();
        m.insert(k.to_string(), v.to_string());
        m
    }

    fn cell(s: &str) -> CellId {
        s.to_string()
    }
}
