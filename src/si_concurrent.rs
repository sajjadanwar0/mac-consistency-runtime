// lib_si_concurrent.rs
//
// =====================================================================
// A CONCURRENT snapshot-isolation store whose safety is mechanized, not
// relocated.  (12 Sep 2026, post-ICECCS round 3.)
//
// WHAT THIS CLOSES
//   Reviewer 1: "despite the title referencing concurrency, the provided
//   proofs cover only sequential events."  Reviewer 3 (W2): "the verified
//   chain does not reach where the framing suggests."
//
//   Before this file the multi-threaded argument was: sequential
//   refinements (lib_refinement_ssi*.rs) + an atomic-event lift
//   (lib_concurrent_semantics.rs) that is CONDITIONAL on the deployed lock
//   realizing Acquire/Release, with that condition parked in three
//   external_body stubs (lib_rustbelt_interface.rs) -- stated, moreover,
//   over std::sync::Mutex while the shipped runtime locks with
//   parking_lot::Mutex (Cargo.toml).
//
//   Here the critical section IS a verified lock: vstd::rwlock::RwLock,
//   implemented in vstd with atomics and a reference count and verified
//   there.  The lock's predicate is the SI safety invariant `SiStore::inv`
//   (which entails "no stale-generation window in the emitted trace").
//   RwLock::acquire_write ensures the invariant of the value it hands out;
//   WriteHandle::release_write REQUIRES it of the value it takes back.
//   Therefore, for ANY number of threads and ANY interleaving of begin /
//   commit / observe on one SiConcurrent, every state any thread ever
//   observes satisfies `inv`, and its trace has no A_1 window
//   (`SiConcurrent::trace_is_a1_free` states exactly that at a read
//   handle).  Nothing is assumed about the lock: the three
//   RUSTBELT_OBLIGATION stubs are not needed by this file.
//
// WHAT STAYS OUT, STATED NOT HIDDEN
//   * liveness / deadlock-freedom: vstd's RwLock specification does not
//     verify absence of deadlock, and a handle that is never released is
//     not detected by Verus.  Safety only, as everywhere in this paper.
//   * the structural window.  `a1_struct` is Definition 1 without the
//     value-inequality and different-agent conjuncts.  It is STRONGER to
//     exclude: Definition 1 implies a1_struct, so !a1_struct implies !A_1.
//     (Same shape as lib_ssi.rs::inv_no_intervening_write.)
//   * read values: `begin` returns the last recorded version per cell for
//     the caller to emit; the theorem does not depend on which value is
//     returned, only on the read/write times, so no spec is stated for it.
//   * arithmetic: at clock == u64::MAX a commit aborts (returns false)
//     rather than overflow; the invariant is preserved by not changing
//     the store.
//
// REUSE
//   in_set / fresh / contains / validate / fresh_means_no_overwrite are
//   verbatim from mac-consistency-runtime/src/lib_si_validate_exec.rs
//   (the gate the deployed commit already calls), so the validation
//   decision here is the same verified function.
//
// TRUST BASE of this file: Verus + vstd (including vstd's own verified
//   RwLock).  NO axiom, NO assume, NO admit, NO external_body.
//
// ROUND 4 (integration): `commit` returns the commit time so the deployed
//   store can emit it; `tick` advances the clock without validation (the
//   default-SI no-write bypass, which is exactly the A_1-admitting path
//   the paper measures); `clock` reads it.  The same file is compiled by
//   plain cargo as mac-consistency-runtime/src/si_concurrent.rs (proofs
//   erased by the verus! macro), where SnapshotIsolationStore's critical
//   section is this lock -- not parking_lot::Mutex.  The lock is a
//   spinlock (compare-and-swap loop, vstd::rwlock), adequate for the
//   pilot's contention and stated as such in the paper.
//
// VERIFY
//   cd verus-detector && verus --crate-type=lib src/lib_si_concurrent.rs
// =====================================================================

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;
use vstd::rwlock::*;

verus! {

pub type Cell = usize;
pub type Val = usize;
pub type Agent = usize;
pub type Time = u64;

// ---------------------------------------------------------------------
// Section 1: the verified validation gate (verbatim, lib_si_validate_exec)
// ---------------------------------------------------------------------

pub open spec fn in_set(rs: Seq<Cell>, c: Cell) -> bool {
    exists|i: int| 0 <= i < rs.len() && rs[i] == c
}

pub open spec fn fresh(vs: Seq<(Cell, u64, Val)>, rs: Seq<Cell>, rt: u64) -> bool {
    forall|k: int|
        0 <= k < vs.len() ==> (in_set(rs, vs[k].0) ==> vs[k].1 <= rt)
}

pub fn contains(rs: &Vec<Cell>, c: Cell) -> (b: bool)
    ensures b == in_set(rs@, c)
{
    let n = rs.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == rs@.len(),
            forall|t: int| 0 <= t < k ==> rs@[t] != c,
        decreases n - k
    {
        if rs[k] == c {
            assert(rs@[k as int] == c);
            return true;
        }
        k = k + 1;
    }
    false
}

pub fn validate(vs: &Vec<(Cell, u64, Val)>, rs: &Vec<Cell>, rt: u64) -> (ok: bool)
    ensures ok == fresh(vs@, rs@, rt)
{
    let n = vs.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == vs@.len(),
            forall|t: int|
                0 <= t < k ==> (in_set(rs@, vs@[t].0) ==> vs@[t].1 <= rt),
        decreases n - k
    {
        let c = vs[k].0;
        let t = vs[k].1;
        let inset = contains(rs, c);
        if inset && t > rt {
            // Witnesses !fresh at index k.
            assert(in_set(rs@, vs@[k as int].0));
            assert(vs@[k as int].1 > rt);
            return false;
        }

        assert(in_set(rs@, vs@[k as int].0) ==> vs@[k as int].1 <= rt);
        k = k + 1;
    }

    true
}

pub proof fn fresh_means_no_overwrite(
    vs: Seq<(Cell, u64, Val)>, rs: Seq<Cell>, rt: u64, c: Cell, idx: int
)
    requires
        fresh(vs, rs, rt),
        in_set(rs, c),
        0 <= idx < vs.len(),
        vs[idx].0 == c,
    ensures
        vs[idx].1 <= rt,
{
}

// ---------------------------------------------------------------------
// Section 2: trace records and the structural stale-generation window
// ---------------------------------------------------------------------

pub struct Rec {
    pub agent: Agent,
    pub read_cells: Vec<Cell>,
    pub read_time: Time,
    pub write_cells: Vec<Cell>,
    pub write_time: Time,
}

/// Definition 1 minus the value-inequality and different-agent conjuncts:
/// some record j commits a write to a cell inside record i's
/// read-to-commit window.  Definition 1 ==> a1_struct, so excluding this
/// excludes A_1.
pub open spec fn a1_struct(tr: Seq<Rec>) -> bool {
    exists|i: int, j: int, c: Cell|
        0 <= i < tr.len() && 0 <= j < tr.len() && i != j
        && #[trigger] in_set(tr[i].read_cells@, c)
        && #[trigger] in_set(tr[j].write_cells@, c)
        && tr[i].read_time < tr[j].write_time
        && tr[j].write_time < tr[i].write_time
}

// ---------------------------------------------------------------------
// Section 3: the store, its invariant, and the two sequential steps
// ---------------------------------------------------------------------

pub struct SiStore {
    /// flat version chain: (cell, commit time, value)
    pub versions: Vec<(Cell, u64, Val)>,
    pub clock: Time,
    pub trace: Vec<Rec>,
}

pub struct Snapshot {
    pub agent: Agent,
    pub read_time: Time,
    pub read_cells: Vec<Cell>,
    /// last recorded version per requested cell (informational; unspecified)
    pub read_values: Vec<(Cell, Val)>,
}

impl SiStore {
    /// every version was committed at or before the clock
    pub open spec fn inv_versions_le_clock(self) -> bool {
        forall|k: int| 0 <= k < self.versions@.len()
            ==> (#[trigger] self.versions@[k]).1 <= self.clock
    }

    /// every record reads strictly before it writes, and wrote at or before the clock
    pub open spec fn inv_trace_times(self) -> bool {
        forall|i: int| 0 <= i < self.trace@.len()
            ==> (#[trigger] self.trace@[i]).read_time < self.trace@[i].write_time
                && self.trace@[i].write_time <= self.clock
    }

    /// every committed write in the trace is present in the version chain
    /// at its commit time -- the link the validation gate inspects
    pub open spec fn inv_link(self) -> bool {
        forall|i: int, c: Cell|
            0 <= i < self.trace@.len() && #[trigger] in_set(self.trace@[i].write_cells@, c)
            ==> exists|k: int|
                    0 <= k < self.versions@.len()
                    && (#[trigger] self.versions@[k]).0 == c
                    && self.versions@[k].1 == self.trace@[i].write_time
    }

    pub open spec fn inv(self) -> bool {
        &&& self.inv_versions_le_clock()
        &&& self.inv_trace_times()
        &&& self.inv_link()
        &&& !a1_struct(self.trace@)
    }

    pub fn new() -> (s: SiStore)
        ensures
            s.inv(),
            s.trace@.len() == 0,
            s.clock == 0,
    {
        let s = SiStore { versions: Vec::new(), clock: 0, trace: Vec::new() };
        proof {
            assert(s.versions@.len() == 0);
            assert(s.trace@.len() == 0);
            assert(!a1_struct(s.trace@));
        }
        s
    }
}

/// begin: snapshot the clock as read_time and record the requested read
/// set.  The store is not modified.  Values returned are the last
/// recorded version per cell (no specification; see header).
pub fn begin_step(s: &SiStore, agent: Agent, cells: Vec<Cell>) -> (snap: Snapshot)
    ensures
        snap.agent == agent,
        snap.read_time == s.clock,
        snap.read_cells@ == cells@,
{
    let mut read_values: Vec<(Cell, Val)> = Vec::new();
    let n = cells.len();
    let m = s.versions.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == cells@.len(),
            m == s.versions@.len(),
        decreases n - i
    {
        let c = cells[i];
        let mut best_t: u64 = 0;
        let mut best_v: Val = 0;
        let mut k: usize = 0;
        while k < m
            invariant
                k <= m,
                m == s.versions@.len(),
            decreases m - k
        {
            let (vc, vt, vv) = s.versions[k];
            if vc == c && vt >= best_t {
                best_t = vt;
                best_v = vv;
            }
            k = k + 1;
        }
        read_values.push((c, best_v));
        i = i + 1;
    }
    Snapshot { agent, read_time: s.clock, read_cells: cells, read_values }
}

/// commit: validate the snapshot's read set against the version chain
/// (the verified gate); on success advance the clock, append one version
/// per write, and append the trace record.  Returns (store, committed).
/// The store passed in is returned unchanged when the commit aborts.
pub fn commit_step(s: SiStore, snap: Snapshot, writes: &Vec<(Cell, Val)>) -> (r: (SiStore, bool))
    requires
        s.inv(),
    ensures
        r.0.inv(),
        r.1 ==> r.0.trace@.len() == s.trace@.len() + 1,
        r.1 ==> r.0.clock == s.clock + 1,
        !r.1 ==> r.0.trace@ == s.trace@,
        !r.1 ==> r.0.versions@ == s.versions@,
        !r.1 ==> r.0.clock == s.clock,
{
    let ghost s0 = s;
    let mut s = s;

    let agent = snap.agent;
    let read_time = snap.read_time;
    let read_cells = snap.read_cells;
    let ghost rs = read_cells@;

    // A snapshot that claims a read time after the current clock did not
    // come from `begin_step` on this store's past; refuse it rather than
    // trust the caller.  Refuse at the clock ceiling as well.
    if read_time > s.clock || s.clock == u64::MAX {
        return (s, false);
    }

    let ok = validate(&s.versions, &read_cells, read_time);
    if !ok {
        return (s, false);
    }
    // here: fresh(s.versions@, read_cells@, read_time)

    let clock0 = s.clock;
    let new_clock: u64 = clock0 + 1;
    let ghost vs0 = s.versions@;
    let ghost tr0 = s.trace@;

    let mut write_cells: Vec<Cell> = Vec::new();
    let n_w = writes.len();
    let mut i: usize = 0;
    while i < n_w
        invariant
            i <= n_w,
            n_w == writes@.len(),
            s.clock == clock0,
            s.trace@ == tr0,
            write_cells@.len() == i as int,
            forall|t: int| 0 <= t < i ==> write_cells@[t] == writes@[t].0,
            s.versions@.len() == vs0.len() + (i as int),
            forall|k: int| 0 <= k < vs0.len() ==> s.versions@[k] == vs0[k],
            forall|k: int| vs0.len() <= k < s.versions@.len()
                ==> s.versions@[k] == (writes@[k - vs0.len()].0, new_clock, writes@[k - vs0.len()].1),
        decreases n_w - i
    {
        let (c, v) = writes[i];
        s.versions.push((c, new_clock, v));
        write_cells.push(c);
        proof {
            assert(c == writes@[i as int].0);
            assert(v == writes@[i as int].1);
            assert(s.versions@.len() == vs0.len() + (i as int) + 1);
            assert(s.versions@[vs0.len() + (i as int)] == (c, new_clock, v));
            assert(write_cells@[i as int] == c);
        }
        i = i + 1;
    }
    let ghost wcells = write_cells@;

    s.clock = new_clock;
    let rec = Rec {
        agent,
        read_cells,
        read_time,
        write_cells,
        write_time: new_clock,
    };
    let ghost rec0 = rec;
    s.trace.push(rec);

    proof {
        let tr1 = s.trace@;
        let n = tr0.len();
        assert(tr1 == tr0.push(rec0));
        assert(s.trace@ == tr0.push(rec0));
        assert(s.trace@.len() == n + 1);
        assert(s.trace@[n as int] == rec0);
        assert(forall|q: int| 0 <= q < n ==> s.trace@[q] == tr0[q]);
        assert(rec0.read_cells@ == rs);
        assert(rec0.write_cells@ == wcells);
        assert(rec0.read_time == read_time);
        assert(rec0.write_time == new_clock);
        assert(fresh(vs0, rs, read_time));
        assert(s0.versions@ == vs0);
        assert(s0.trace@ == tr0);
        assert(s0.clock == clock0);

        // I1: versions at or before the (new) clock
        assert forall|k: int| 0 <= k < s.versions@.len()
            implies (#[trigger] s.versions@[k]).1 <= s.clock by {
            if k < vs0.len() {
                assert(s.versions@[k] == vs0[k]);
                assert(s0.versions@[k].1 <= clock0);   // s0.inv_versions_le_clock
                assert(vs0[k] == s0.versions@[k]);
            } else {
                assert(s.versions@[k].1 == new_clock);
            }
        }

        // I2: read < write <= clock for every record
        assert forall|q: int| 0 <= q < s.trace@.len()
            implies (#[trigger] s.trace@[q]).read_time < s.trace@[q].write_time
                    && s.trace@[q].write_time <= s.clock by {
            if q < n {
                assert(s.trace@[q] == tr0[q]);
                assert(s0.trace@[q].read_time < s0.trace@[q].write_time);   // s0.inv_trace_times
                assert(s0.trace@[q].write_time <= clock0);
                assert(tr0[q] == s0.trace@[q]);
            } else {
                assert(s.trace@[q] == rec0);
                assert(rec0.read_time <= clock0);
                assert(rec0.write_time == new_clock);
            }
        }

        // I3: every trace write has its version at its commit time
        assert forall|q: int, c: Cell|
            0 <= q < s.trace@.len() && #[trigger] in_set(s.trace@[q].write_cells@, c)
            implies exists|k: int|
                0 <= k < s.versions@.len()
                && (#[trigger] s.versions@[k]).0 == c
                && s.versions@[k].1 == s.trace@[q].write_time by {
            if q < n {
                assert(s.trace@[q] == tr0[q]);
                assert(s0.trace@ == tr0);
                assert(in_set(s0.trace@[q].write_cells@, c));
                let k = choose|k: int|
                    0 <= k < s0.versions@.len()
                    && (#[trigger] s0.versions@[k]).0 == c
                    && s0.versions@[k].1 == s0.trace@[q].write_time;
                assert(s.versions@[k] == vs0[k]);
                assert(0 <= k < s.versions@.len()
                    && s.versions@[k].0 == c
                    && s.versions@[k].1 == s.trace@[q].write_time);
            } else {
                assert(s.trace@[q] == rec0);
                assert(in_set(wcells, c));
                let t = choose|t: int| 0 <= t < wcells.len() && wcells[t] == c;
                assert(wcells[t] == writes@[t].0);
                let k = vs0.len() + t;
                assert(s.versions@[k] == (writes@[k - vs0.len()].0, new_clock, writes@[k - vs0.len()].1));
                assert(s.versions@[k].0 == c);
                assert(s.versions@[k].1 == new_clock);
                assert(0 <= k < s.versions@.len()
                    && s.versions@[k].0 == c
                    && s.versions@[k].1 == s.trace@[q].write_time);
            }
        }

        // I4: no stale-generation window in the extended trace
        assert(!a1_struct(s.trace@)) by {
            if a1_struct(s.trace@) {
                let (i, j, c) = choose|i: int, j: int, c: Cell|
                    0 <= i < s.trace@.len() && 0 <= j < s.trace@.len() && i != j
                    && #[trigger] in_set(s.trace@[i].read_cells@, c)
                    && #[trigger] in_set(s.trace@[j].write_cells@, c)
                    && s.trace@[i].read_time < s.trace@[j].write_time
                    && s.trace@[j].write_time < s.trace@[i].write_time;
                if i < n && j < n {
                    // an old pair: contradicts s0's !a1_struct
                    assert(s.trace@[i] == s0.trace@[i]);
                    assert(s.trace@[j] == s0.trace@[j]);
                    assert(in_set(s0.trace@[i].read_cells@, c));
                    assert(in_set(s0.trace@[j].write_cells@, c));
                    assert(s0.trace@[i].read_time < s0.trace@[j].write_time);
                    assert(s0.trace@[j].write_time < s0.trace@[i].write_time);
                    assert(a1_struct(s0.trace@));
                    assert(false);
                } else if i == n {
                    // the new record reads c; an old record j wrote c inside
                    // its window.  That write is a version at write_time(j)
                    // (I3 on s0); validation passed, so write_time(j) <= read_time.
                    assert(j < n);
                    assert(s.trace@[i] == rec0);
                    assert(s.trace@[j] == s0.trace@[j]);
                    assert(in_set(s0.trace@[j].write_cells@, c));
                    let k = choose|k: int|
                        0 <= k < s0.versions@.len()
                        && (#[trigger] s0.versions@[k]).0 == c
                        && s0.versions@[k].1 == s0.trace@[j].write_time;
                    assert(in_set(rs, c));
                    fresh_means_no_overwrite(vs0, rs, read_time, c, k);
                    assert(vs0[k].1 <= read_time);
                    assert(s0.trace@[j].write_time <= rec0.read_time);
                    assert(false);
                } else {
                    // j == n: the new record wrote at clock0 + 1, but every
                    // old record committed at or before clock0.
                    assert(j == n);
                    assert(i < n);
                    assert(s.trace@[j] == rec0);
                    assert(s.trace@[i] == s0.trace@[i]);
                    assert(s0.trace@[i].write_time <= clock0);
                    assert(rec0.write_time == new_clock);
                    assert(false);
                }
            }
        }

        assert(s.inv_versions_le_clock());
        assert(s.inv_trace_times());
        assert(s.inv_link());
        assert(s.inv());
    }

    (s, true)
}

// ---------------------------------------------------------------------
// Section 4: the lock predicate and the concurrent store
// ---------------------------------------------------------------------

pub struct SiPred;

impl RwLockPredicate<SiStore> for SiPred {
    open spec fn inv(self, v: SiStore) -> bool {
        v.inv()
    }
}

/// A store whose only access path is through a verified reader-writer
/// lock carrying `SiStore::inv` as its predicate.
pub struct SiConcurrent {
    pub lock: RwLock<SiStore, SiPred>,
}

impl SiConcurrent {
    pub fn new() -> (r: SiConcurrent) {
        let store = SiStore::new();
        let lock = RwLock::<SiStore, SiPred>::new(store, Ghost(SiPred));
        SiConcurrent { lock }
    }

    /// begin under a shared lock: many agents may begin concurrently.
    pub fn begin(&self, agent: Agent, cells: Vec<Cell>) -> (snap: Snapshot)
        ensures
            snap.agent == agent,
            snap.read_cells@ == cells@,
    {
        let handle = self.lock.acquire_read();
        let store = handle.borrow();
        let snap = begin_step(store, agent, cells);
        handle.release_read();
        snap
    }

    /// commit under the exclusive lock.  The value handed out satisfies
    /// `inv` (acquire_write's postcondition); commit_step returns a value
    /// satisfying `inv`; release_write requires exactly that.  No thread
    /// can ever install a state violating `inv`.  Returns whether the
    /// commit was applied and the clock afterwards (the commit time when
    /// applied; unchanged when refused).
    pub fn commit(&self, snap: Snapshot, writes: &Vec<(Cell, Val)>) -> (r: (bool, Time)) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let (store2, ok) = commit_step(store, snap, writes);
        assert(store2.inv());
        let t = store2.clock;
        write_handle.release_write(store2);
        (ok, t)
    }

    /// advance the clock by one without validating anything: an empty
    /// snapshot (no read cells, read time 0) always passes the gate, so
    /// this is commit_step's clock bump with an empty record.  It is the
    /// default-SI no-write bypass -- the path that admits A_1 by design
    /// (the record it appends carries no read cells, so the store's own
    /// trace stays A_1-free; the caller's emitted record is what fires).
    /// At the clock ceiling the clock is left unchanged.
    pub fn tick(&self) -> (t: Time) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let empty = Snapshot { agent: 0, read_time: 0, read_cells: Vec::new(), read_values: Vec::new() };
        let no_writes: Vec<(Cell, Val)> = Vec::new();
        let (store2, _ok) = commit_step(store, empty, &no_writes);
        assert(store2.inv());
        let t = store2.clock;
        write_handle.release_write(store2);
        t
    }

    /// the current clock, under a shared read handle.
    pub fn clock(&self) -> (t: Time) {
        let handle = self.lock.acquire_read();
        let store = handle.borrow();
        let t = store.clock;
        handle.release_read();
        t
    }

    /// The concurrent safety statement, at a read handle: whatever state
    /// this thread observes -- after any interleaving of begins and
    /// commits by any number of other threads -- its trace has no
    /// stale-generation window.
    pub fn trace_is_a1_free(&self) {
        let handle = self.lock.acquire_read();
        let store = handle.borrow();
        proof {
            assert(store.inv());
            assert(!a1_struct(store.trace@));
        }
        handle.release_read();
    }
}

// ---------------------------------------------------------------------
// Section 5: non-vacuity -- the excluded window is satisfiable
// ---------------------------------------------------------------------

/// Two records: j (agent 0) commits a write to cell 7 at time 2; i (agent
/// 1) read cell 7 at time 1 and commits at time 3.  a1_struct holds.
pub fn witness_a1_window() {
    let mut wc: Vec<Cell> = Vec::new();
    wc.push(7);
    let rec_j = Rec { agent: 0, read_cells: Vec::new(), read_time: 0, write_cells: wc, write_time: 2 };
    let mut rc: Vec<Cell> = Vec::new();
    rc.push(7);
    let rec_i = Rec { agent: 1, read_cells: rc, read_time: 1, write_cells: Vec::new(), write_time: 3 };
    let mut tr: Vec<Rec> = Vec::new();
    tr.push(rec_j);
    tr.push(rec_i);
    proof {
        assert(tr@.len() == 2);
        assert(tr@[1].read_cells@[0] == 7);
        assert(in_set(tr@[1].read_cells@, 7));
        assert(tr@[0].write_cells@[0] == 7);
        assert(in_set(tr@[0].write_cells@, 7));
        assert(tr@[1].read_time < tr@[0].write_time);
        assert(tr@[0].write_time < tr@[1].write_time);
        assert(a1_struct(tr@));
    }
}

} // verus!
