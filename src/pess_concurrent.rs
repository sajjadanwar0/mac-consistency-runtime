// lib_pess_concurrent.rs
//
// =====================================================================
// A CONCURRENT pessimistic-locking store whose safety is mechanized.
// (13 Sep 2026, post-ICECCS round 5.)  Companion to lib_si_concurrent.rs
// and built the same way: the store's invariant is the predicate of
// vstd's verified reader-writer lock, so every state any thread observes
// -- under any interleaving of begin / commit / release / tick -- satisfies
// it, with nothing assumed about the lock.  With this file the deployed
// pessimistic store (mac-consistency-runtime/src/pessimistic.rs) no longer
// locks with parking_lot::Mutex and the three RUSTBELT_OBLIGATION stubs
// have no deployed runtime left to cover.
//
// THE DISCIPLINE (pessimistic.rs, unchanged semantics)
//   begin(agent, cells)      refuse if any cell is held by another agent;
//                            else hold every cell for `agent` (recording
//                            the clock as the hold's start), snapshot the
//                            latest version per cell, read_time := clock.
//   commit(snapshot, writes) refuse unless every read cell is held by the
//                            snapshot's agent since no later than its
//                            read_time and every write cell is free or
//                            held by that agent; else acquire the write
//                            cells, clock += 1, append one version per
//                            write and the trace record.
//   release(agent)           drop every hold of `agent`.
//   tick()                   clock += 1.
//
// THE INVARIANT (`inv`, the lock predicate)
//   I1  every version's time <= clock;
//   I2  every record reads strictly before it writes, at or before clock;
//   I3  every committed write is a version at its commit time BY ITS AGENT;
//   I4  no stale-generation window in the trace (a1_cross, the structural
//       form of Definition 1; Definition 1 implies it);
//   H1  no cell is held twice (exclusive holders);
//   H2  every hold began at or before the clock;
//   H3  no agent other than the holder has written a held cell since the
//       hold began -- the fact that makes I4 inductive: a reader holds its
//       read cells from read_time to commit, and a write needs the hold.
//
// WHY THIS PROVES NO WINDOW
//   A committed record r read cell c at read_time, held by r's agent since
//   `since <= read_time` (checked at commit).  Any other agent's write to
//   c is a version by that agent (I3); H3 puts its time <= since <=
//   read_time, so it did not land inside r's window.  r's own writes land
//   at clock+1, after every existing record's commit (I2).  Old pairs were
//   already window-free.
//
// SCOPE, STATED
//   * safety, not liveness (vstd's RwLock does not verify deadlock-freedom;
//     an agent that never releases blocks others, as in the deployed store);
//   * the window excluded is Definition 1 without the value-inequality
//     conjunct (cross-agent kept) -- stronger to exclude;
//   * values returned by begin carry no specification.
//
// TRUST BASE: Verus + vstd (incl. vstd's verified RwLock).  No axiom, no
//   assume, no admit, no external_body.
//
// VERIFY:  cd verus-detector && verus --crate-type=lib src/lib_pess_concurrent.rs
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

pub open spec fn in_set(rs: Seq<Cell>, c: Cell) -> bool {
    exists|i: int| 0 <= i < rs.len() && rs[i] == c
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

// ---------------------------------------------------------------------
// records, the structural window, the store
// ---------------------------------------------------------------------

pub struct Rec {
    pub agent: Agent,
    pub read_cells: Vec<Cell>,
    pub read_time: Time,
    pub write_cells: Vec<Cell>,
    pub write_time: Time,
}

/// Definition 1 minus only the value-inequality conjunct: another agent's
/// write lands strictly inside a record's read-to-commit window.
/// Definition 1 implies a1_cross, so excluding it excludes A_1.  (The
/// same-agent case is deliberately not in the predicate: an agent that
/// reads, commits a write, and later commits again under a snapshot it
/// took earlier is a sequential pattern this discipline permits, and
/// Definition 1 does not count it either.)
pub open spec fn a1_cross(tr: Seq<Rec>) -> bool {
    exists|i: int, j: int, c: Cell|
        0 <= i < tr.len() && 0 <= j < tr.len() && i != j
        && tr[i].agent != tr[j].agent
        && #[trigger] in_set(tr[i].read_cells@, c)
        && #[trigger] in_set(tr[j].write_cells@, c)
        && tr[i].read_time < tr[j].write_time
        && tr[j].write_time < tr[i].write_time
}

pub struct PessStore {
    /// (cell, commit time, value, writer)
    pub versions: Vec<(Cell, Time, Val, Agent)>,
    pub clock: Time,
    /// (cell, holder, hold began at)
    pub holds: Vec<(Cell, Agent, Time)>,
    pub trace: Vec<Rec>,
}

pub struct Snapshot {
    pub agent: Agent,
    pub read_time: Time,
    pub read_cells: Vec<Cell>,
    pub read_values: Vec<(Cell, Val)>,
}

impl PessStore {
    pub open spec fn inv_versions_le_clock(self) -> bool {
        forall|k: int| 0 <= k < self.versions@.len()
            ==> (#[trigger] self.versions@[k]).1 <= self.clock
    }

    pub open spec fn inv_trace_times(self) -> bool {
        forall|i: int| 0 <= i < self.trace@.len()
            ==> (#[trigger] self.trace@[i]).read_time < self.trace@[i].write_time
                && self.trace@[i].write_time <= self.clock
    }

    /// every committed write is a version at its commit time by its agent
    pub open spec fn inv_link(self) -> bool {
        forall|i: int, c: Cell|
            0 <= i < self.trace@.len() && #[trigger] in_set(self.trace@[i].write_cells@, c)
            ==> exists|k: int|
                    0 <= k < self.versions@.len()
                    && (#[trigger] self.versions@[k]).0 == c
                    && self.versions@[k].1 == self.trace@[i].write_time
                    && self.versions@[k].3 == self.trace@[i].agent
    }

    /// exclusive holders: no cell appears twice
    pub open spec fn inv_holds_distinct(self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.holds@.len() && 0 <= j < self.holds@.len() && i != j
            ==> (#[trigger] self.holds@[i]).0 != (#[trigger] self.holds@[j]).0
    }

    pub open spec fn inv_holds_since_le_clock(self) -> bool {
        forall|i: int| 0 <= i < self.holds@.len()
            ==> (#[trigger] self.holds@[i]).2 <= self.clock
    }

    /// no foreign write to a held cell since the hold began
    pub open spec fn inv_no_foreign_write_since_hold(self) -> bool {
        forall|i: int, k: int|
            0 <= i < self.holds@.len() && 0 <= k < self.versions@.len()
            && (#[trigger] self.holds@[i]).0 == (#[trigger] self.versions@[k]).0
            && self.versions@[k].3 != self.holds@[i].1
            ==> self.versions@[k].1 <= self.holds@[i].2
    }

    pub open spec fn inv(self) -> bool {
        &&& self.inv_versions_le_clock()
        &&& self.inv_trace_times()
        &&& self.inv_link()
        &&& !a1_cross(self.trace@)
        &&& self.inv_holds_distinct()
        &&& self.inv_holds_since_le_clock()
        &&& self.inv_no_foreign_write_since_hold()
    }

    pub fn new() -> (s: PessStore)
        ensures s.inv(), s.trace@.len() == 0, s.clock == 0,
    {
        let s = PessStore { versions: Vec::new(), clock: 0, holds: Vec::new(), trace: Vec::new() };
        proof {
            assert(s.versions@.len() == 0);
            assert(s.trace@.len() == 0);
            assert(s.holds@.len() == 0);
            assert(!a1_cross(s.trace@));
        }
        s
    }
}

// ---------------------------------------------------------------------
// holder lookup: which agent holds a cell, if any
// ---------------------------------------------------------------------

/// Some(agent) iff some hold on `c` exists (then it is that agent's, by
/// distinctness); None iff no hold on `c` exists.
pub fn holder_of(holds: &Vec<(Cell, Agent, Time)>, c: Cell) -> (r: Option<Agent>)
    ensures
        r.is_none() ==> (forall|i: int| 0 <= i < holds@.len() ==> (#[trigger] holds@[i]).0 != c),
        r.is_some() ==> (exists|i: int| 0 <= i < holds@.len() && (#[trigger] holds@[i]).0 == c && holds@[i].1 == r.unwrap()),
{
    let n = holds.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == holds@.len(),
            forall|t: int| 0 <= t < k ==> (#[trigger] holds@[t]).0 != c,
        decreases n - k
    {
        let (hc, ha, _) = holds[k];
        if hc == c {
            assert(holds@[k as int].0 == c && holds@[k as int].1 == ha);
            return Some(ha);
        }
        k = k + 1;
    }
    None
}

/// `c` is held by `agent` since no later than `rt`.  A named spec predicate,
/// so that every statement about holds is a flat application instead of a
/// quantifier nested inside another quantifier (rounds 9 and 11 failed on
/// exactly that nesting).
pub open spec fn held_by_since(holds: Seq<(Cell, Agent, Time)>, agent: Agent, c: Cell, rt: Time) -> bool {
    exists|i: int| 0 <= i < holds.len()
        && (#[trigger] holds[i]).0 == c && holds[i].1 == agent && holds[i].2 <= rt
}

/// the witness behind `held_by_since`, extracted once
pub proof fn held_witness(holds: Seq<(Cell, Agent, Time)>, agent: Agent, c: Cell, rt: Time) -> (i: int)
    requires held_by_since(holds, agent, c, rt),
    ensures 0 <= i < holds.len() && holds[i].0 == c && holds[i].1 == agent && holds[i].2 <= rt,
{
    let i = choose|i: int| 0 <= i < holds.len()
        && (#[trigger] holds[i]).0 == c && holds[i].1 == agent && holds[i].2 <= rt;
    i
}

/// exclusive holders: two holds on the same cell are the same hold.  Kept as
/// its own lemma so the step happens with nothing else in scope; round 16
/// failed on exactly this step done inline, where `inv_holds_distinct` had to
/// be unfolded and its multi-trigger matched inside a loop body.
pub proof fn unique_holder(holds: Seq<(Cell, Agent, Time)>, c: Cell, w: int, i: int)
    requires
        forall|a: int, b: int|
            0 <= a < holds.len() && 0 <= b < holds.len() && a != b
            ==> (#[trigger] holds[a]).0 != (#[trigger] holds[b]).0,
        0 <= w < holds.len(),
        0 <= i < holds.len(),
        holds[w].0 == c,
        holds[i].0 == c,
    ensures i == w,
{
    if i != w {
        assert(holds[i].0 != holds[w].0);
    }
}

/// if true, `c` is held by `agent` since no later than `rt`
pub fn held_since_one(holds: &Vec<(Cell, Agent, Time)>, agent: Agent, c: Cell, rt: Time) -> (b: bool)
    ensures b ==> held_by_since(holds@, agent, c, rt),
{
    let m = holds.len();
    let mut k: usize = 0;
    while k < m
        invariant k <= m, m == holds@.len(),
        decreases m - k
    {
        let (hc, ha, hs) = holds[k];
        if hc == c && ha == agent && hs <= rt {
            assert(holds@[k as int].0 == c && holds@[k as int].1 == agent && holds@[k as int].2 <= rt);
            assert(held_by_since(holds@, agent, c, rt));
            return true;
        }
        k = k + 1;
    }
    false
}

/// if true, every cell in `cells` is held by `agent` since no later than `rt`
/// (the negative direction is not needed and not stated)
pub fn all_held_since(holds: &Vec<(Cell, Agent, Time)>, agent: Agent, cells: &Vec<Cell>, rt: Time) -> (b: bool)
    ensures
        b ==> (forall|t: int| #![trigger cells@[t]] 0 <= t < cells@.len()
                ==> held_by_since(holds@, agent, cells@[t], rt)),
{
    let n = cells.len();
    let mut t: usize = 0;
    while t < n
        invariant
            t <= n,
            n == cells@.len(),
            forall|u: int| #![trigger cells@[u]] 0 <= u < t
                ==> held_by_since(holds@, agent, cells@[u], rt),
        decreases n - t
    {
        let c = cells[t];
        if !held_since_one(holds, agent, c, rt) {
            return false;
        }
        proof {
            assert(cells@[t as int] == c);
        }
        t = t + 1;
    }
    true
}

// ---------------------------------------------------------------------
// the four steps
// ---------------------------------------------------------------------

/// begin: refuse if any cell is held by another agent; else hold every
/// cell (existing holds by this agent are kept), snapshot the latest
/// version per cell, read_time := clock.  Returns (store, snapshot);
/// snapshot is None on refusal and the store is then unchanged.
pub fn begin_step(s: PessStore, agent: Agent, cells: Vec<Cell>) -> (r: (PessStore, Option<Snapshot>))
    requires s.inv(),
    ensures
        r.0.inv(),
        r.1.is_some() ==> r.1.unwrap().read_time == s.clock,
        r.1.is_some() ==> r.1.unwrap().agent == agent,
        r.1.is_some() ==> r.1.unwrap().read_cells@ == cells@,
        r.1.is_none() ==> r.0.holds@ == s.holds@,
        r.0.clock == s.clock,
        r.0.versions@ == s.versions@,
        r.0.trace@ == s.trace@,
{
    let ghost s0 = s;

    // phase 1: a pure scan.  No `return` inside the loop and no mutation of
    // the store, so `s` is never havoc'd and the refusal below is
    // straight-line code (rounds 11/13/15 failed here: a return from inside
    // a loop had to re-derive "the store is unchanged" from the invariant,
    // and struct equality over Vec-bearing structs does not carry views).
    let n = cells.len();
    let mut t: usize = 0;
    let mut conflict = false;
    while t < n
        invariant t <= n, n == cells@.len(),
        decreases n - t
    {
        match holder_of(&s.holds, cells[t]) {
            Some(h) => { if h != agent { conflict = true; } }
            None => {}
        }
        t = t + 1;
    }
    if conflict {
        return (s, None);
    }

    // take the store apart: the acquisition loop below touches only a local
    // vector, so no loop invariant mentions the struct or its invariant
    let clock0 = s.clock;
    let versions = s.versions;
    let trace = s.trace;
    let mut holds = s.holds;
    let ghost holds0 = holds@;
    proof {
        assert(holds0 == s0.holds@);
        assert(versions@ == s0.versions@);
        assert(trace@ == s0.trace@);
    }

    let mut t: usize = 0;
    while t < n
        invariant
            t <= n,
            n == cells@.len(),
            holds@.len() >= holds0.len(),
            forall|i: int| #![trigger holds@[i]] 0 <= i < holds0.len() ==> holds@[i] == holds0[i],
            forall|i: int| #![trigger holds@[i]] holds0.len() <= i < holds@.len()
                ==> holds@[i].1 == agent && holds@[i].2 == clock0,
            forall|i: int, j: int|
                0 <= i < holds@.len() && 0 <= j < holds@.len() && i != j
                ==> (#[trigger] holds@[i]).0 != (#[trigger] holds@[j]).0,
            forall|i: int| 0 <= i < holds@.len() ==> (#[trigger] holds@[i]).2 <= clock0,
            forall|i: int, k: int|
                0 <= i < holds@.len() && 0 <= k < versions@.len()
                && (#[trigger] holds@[i]).0 == (#[trigger] versions@[k]).0
                && versions@[k].3 != holds@[i].1
                ==> versions@[k].1 <= holds@[i].2,
            forall|k: int| 0 <= k < versions@.len() ==> (#[trigger] versions@[k]).1 <= clock0,
        decreases n - t
    {
        let c = cells[t];
        match holder_of(&holds, c) {
            Some(_) => {}
            None => {
                let ghost before = holds@;
                holds.push((c, agent, clock0));
                proof {
                    let last = before.len() as int;
                    assert(holds@ == before.push((c, agent, clock0)));
                    assert(holds@[last] == (c, agent, clock0));
                    assert forall|i: int, j: int|
                        0 <= i < holds@.len() && 0 <= j < holds@.len() && i != j
                        implies (#[trigger] holds@[i]).0 != (#[trigger] holds@[j]).0 by {
                        if i < last && j < last {
                            assert(holds@[i] == before[i]); assert(holds@[j] == before[j]);
                        } else if i == last {
                            assert(holds@[j] == before[j]); assert(before[j].0 != c);
                        } else {
                            assert(holds@[i] == before[i]); assert(before[i].0 != c);
                        }
                    }
                    assert forall|i: int| 0 <= i < holds@.len()
                        implies (#[trigger] holds@[i]).2 <= clock0 by {
                        if i < last { assert(holds@[i] == before[i]); }
                    }
                    assert forall|i: int, k: int|
                        0 <= i < holds@.len() && 0 <= k < versions@.len()
                        && (#[trigger] holds@[i]).0 == (#[trigger] versions@[k]).0
                        && versions@[k].3 != holds@[i].1
                        implies versions@[k].1 <= holds@[i].2 by {
                        if i < last {
                            assert(holds@[i] == before[i]);
                        } else {
                            assert(holds@[i] == (c, agent, clock0));
                            assert(versions@[k].1 <= clock0);
                        }
                    }
                }
            }
        }
        t = t + 1;
    }

    // reassemble once, outside every loop
    let s = PessStore { versions, clock: clock0, holds, trace };
    proof {
        assert(s.versions@ == s0.versions@);
        assert(s.trace@ == s0.trace@);
        assert(s.clock == s0.clock);
        assert(s.inv_versions_le_clock());
        assert(s.inv_trace_times());
        assert(s.inv_link());
        assert(!a1_cross(s.trace@));
        assert(s.inv_holds_distinct());
        assert(s.inv_holds_since_le_clock());
        assert(s.inv_no_foreign_write_since_hold());
        assert(s.inv());
    }

    // snapshot values: latest version per requested cell (no specification)
    let mut read_values: Vec<(Cell, Val)> = Vec::new();
    let m = s.versions.len();
    let mut t: usize = 0;
    while t < n
        invariant t <= n, n == cells@.len(), m == s.versions@.len(),
        decreases n - t
    {
        let c = cells[t];
        let mut best_t: u64 = 0;
        let mut best_v: Val = 0;
        let mut k: usize = 0;
        while k < m
            invariant k <= m, m == s.versions@.len(),
            decreases m - k
        {
            let (vc, vt, vv, _) = s.versions[k];
            if vc == c && vt >= best_t { best_t = vt; best_v = vv; }
            k = k + 1;
        }
        read_values.push((c, best_v));
        t = t + 1;
    }
    let snap = Snapshot { agent, read_time: clock0, read_cells: cells, read_values };
    (s, Some(snap))
}

/// commit: refuse unless every read cell is held by the snapshot's agent
/// since no later than its read_time and every write cell is free or held
/// by that agent; else acquire the write cells, advance the clock, append
/// the versions and the record.  The store is unchanged on refusal.
pub fn commit_step(s: PessStore, snap: Snapshot, writes: &Vec<(Cell, Val)>) -> (r: (PessStore, bool))
    requires s.inv(),
    ensures
        r.0.inv(),
        r.1 ==> r.0.clock == s.clock + 1,
        r.1 ==> r.0.trace@.len() == s.trace@.len() + 1,
        !r.1 ==> r.0.clock == s.clock,
        !r.1 ==> r.0.versions@ == s.versions@,
        !r.1 ==> r.0.trace@ == s.trace@,
{
    let ghost s0 = s;
    let agent = snap.agent;
    let read_time = snap.read_time;
    let read_cells = snap.read_cells;
    let ghost rs = read_cells@;

    if read_time > s.clock || s.clock == u64::MAX {
        return (s, false);
    }
    let held = all_held_since(&s.holds, agent, &read_cells, read_time);
    if !held {
        return (s, false);
    }

    // every write cell free or held by agent.  A flag, not a return, so the
    // refusal is straight-line code and `s` is never havoc'd.
    let n_w = writes.len();
    let mut t: usize = 0;
    let mut foreign = false;
    while t < n_w
        invariant
            t <= n_w,
            n_w == writes@.len(),
            s.inv(),
            s.inv_holds_distinct(),
            forall|u: int, i: int| 0 <= u < t && 0 <= i < s.holds@.len()
                && (#[trigger] s.holds@[i]).0 == (#[trigger] writes@[u]).0
                ==> s.holds@[i].1 == agent || foreign,
        decreases n_w - t
    {
        let c = writes[t].0;
        match holder_of(&s.holds, c) {
            Some(h) => {
                if h != agent {
                    foreign = true;
                } else {
                    proof {
                        assert(s.inv_holds_distinct());
                        let w = choose|w: int| 0 <= w < s.holds@.len()
                            && (#[trigger] s.holds@[w]).0 == c && s.holds@[w].1 == h;
                        assert(0 <= w < s.holds@.len() && s.holds@[w].0 == c && s.holds@[w].1 == h);
                        assert forall|i: int| 0 <= i < s.holds@.len()
                            && (#[trigger] s.holds@[i]).0 == c
                            implies s.holds@[i].1 == agent by {
                            unique_holder(s.holds@, c, w, i);
                            assert(i == w);
                        }
                    }
                }
            }
            None => {
                proof {
                    assert forall|i: int| 0 <= i < s.holds@.len()
                        && (#[trigger] s.holds@[i]).0 == c
                        implies s.holds@[i].1 == agent by { assert(s.holds@[i].0 != c); }
                }
            }
        }
        t = t + 1;
    }
    if foreign {
        return (s, false);
    }

    // take the store apart; every loop below touches only local vectors
    let clock0 = s.clock;
    let ghost holds0 = s.holds@;
    let ghost vs0 = s.versions@;
    let ghost tr0 = s.trace@;
    let mut versions = s.versions;
    let mut trace = s.trace;
    let mut holds = s.holds;
    proof {
        assert(holds0 == s0.holds@);
        assert(vs0 == s0.versions@);
        assert(tr0 == s0.trace@);
    }

    let mut t: usize = 0;
    while t < n_w
        invariant
            t <= n_w,
            n_w == writes@.len(),
            versions@ == vs0,
            trace@ == tr0,
            holds@.len() >= holds0.len(),
            forall|i: int| #![trigger holds@[i]] 0 <= i < holds0.len() ==> holds@[i] == holds0[i],
            forall|i: int| #![trigger holds@[i]] holds0.len() <= i < holds@.len()
                ==> holds@[i].1 == agent && holds@[i].2 == clock0,
            forall|u: int, i: int| 0 <= u < n_w && 0 <= i < holds@.len()
                && (#[trigger] holds@[i]).0 == (#[trigger] writes@[u]).0
                ==> holds@[i].1 == agent,
            forall|i: int, j: int|
                0 <= i < holds@.len() && 0 <= j < holds@.len() && i != j
                ==> (#[trigger] holds@[i]).0 != (#[trigger] holds@[j]).0,
            forall|i: int| 0 <= i < holds@.len() ==> (#[trigger] holds@[i]).2 <= clock0,
            forall|i: int, k: int|
                0 <= i < holds@.len() && 0 <= k < versions@.len()
                && (#[trigger] holds@[i]).0 == (#[trigger] versions@[k]).0
                && versions@[k].3 != holds@[i].1
                ==> versions@[k].1 <= holds@[i].2,
            forall|k: int| 0 <= k < versions@.len() ==> (#[trigger] versions@[k]).1 <= clock0,
        decreases n_w - t
    {
        let c = writes[t].0;
        match holder_of(&holds, c) {
            Some(_h) => {}
            None => {
                let ghost before = holds@;
                holds.push((c, agent, clock0));
                proof {
                    let last = before.len() as int;
                    assert(holds@ == before.push((c, agent, clock0)));
                    assert(holds@[last] == (c, agent, clock0));
                    assert forall|u: int, i: int| 0 <= u < n_w && 0 <= i < holds@.len()
                        && (#[trigger] holds@[i]).0 == (#[trigger] writes@[u]).0
                        implies holds@[i].1 == agent by {
                        if i < last { assert(holds@[i] == before[i]); }
                    }
                    assert forall|i: int, j: int|
                        0 <= i < holds@.len() && 0 <= j < holds@.len() && i != j
                        implies (#[trigger] holds@[i]).0 != (#[trigger] holds@[j]).0 by {
                        if i < last && j < last {
                            assert(holds@[i] == before[i]); assert(holds@[j] == before[j]);
                        } else if i == last {
                            assert(holds@[j] == before[j]); assert(before[j].0 != c);
                        } else {
                            assert(holds@[i] == before[i]); assert(before[i].0 != c);
                        }
                    }
                    assert forall|i: int| 0 <= i < holds@.len()
                        implies (#[trigger] holds@[i]).2 <= clock0 by {
                        if i < last { assert(holds@[i] == before[i]); }
                    }
                    assert forall|i: int, k: int|
                        0 <= i < holds@.len() && 0 <= k < versions@.len()
                        && (#[trigger] holds@[i]).0 == (#[trigger] versions@[k]).0
                        && versions@[k].3 != holds@[i].1
                        implies versions@[k].1 <= holds@[i].2 by {
                        if i < last {
                            assert(holds@[i] == before[i]);
                        } else {
                            assert(holds@[i] == (c, agent, clock0));
                            assert(versions@[k].1 <= clock0);
                        }
                    }
                }
            }
        }
        t = t + 1;
    }
    let ghost holds1 = holds@;

    // apply: versions at clock0 + 1, then the record
    let new_clock: u64 = clock0 + 1;
    let mut write_cells: Vec<Cell> = Vec::new();
    let mut i: usize = 0;
    while i < n_w
        invariant
            i <= n_w,
            n_w == writes@.len(),
            trace@ == tr0,
            holds@ == holds1,
            write_cells@.len() == i as int,
            forall|t: int| #![trigger write_cells@[t]] 0 <= t < i ==> write_cells@[t] == writes@[t].0,
            versions@.len() == vs0.len() + (i as int),
            forall|k: int| #![trigger versions@[k]] 0 <= k < vs0.len() ==> versions@[k] == vs0[k],
            forall|k: int| #![trigger versions@[k]] vs0.len() <= k < versions@.len()
                ==> versions@[k] == (writes@[k - vs0.len()].0, new_clock, writes@[k - vs0.len()].1, agent),
        decreases n_w - i
    {
        let (c, v) = writes[i];
        versions.push((c, new_clock, v, agent));
        write_cells.push(c);
        proof {
            assert(c == writes@[i as int].0);
            assert(v == writes@[i as int].1);
            assert(versions@.len() == vs0.len() + (i as int) + 1);
            assert(versions@[vs0.len() + (i as int)] == (c, new_clock, v, agent));
            assert(write_cells@[i as int] == c);
        }
        i = i + 1;
    }
    let ghost wcells = write_cells@;
    let rec = Rec { agent, read_cells, read_time, write_cells, write_time: new_clock };
    let ghost rec0 = rec;
    trace.push(rec);

    // reassemble once, outside every loop: the proof below is unchanged
    let s = PessStore { versions, clock: new_clock, holds, trace };
    proof {
        assert(s.holds@ == holds1);
        assert(s.clock == new_clock);
    }
    proof {
        let tr1 = s.trace@;
        let n = tr0.len();
        assert(tr1 == tr0.push(rec0));
        assert(s.trace@ == tr0.push(rec0));
        assert(s.trace@.len() == n + 1);
        assert(s.trace@[n as int] == rec0);
        assert(forall|q: int| #![trigger s.trace@[q]] 0 <= q < n ==> s.trace@[q] == tr0[q]);
        assert(rec0.read_cells@ == rs);
        assert(rec0.write_cells@ == wcells);
        assert(rec0.read_time == read_time);
        assert(rec0.write_time == new_clock);
        assert(rec0.agent == agent);
        assert(s0.versions@ == vs0);
        assert(s0.trace@ == tr0);
        assert(s0.clock == clock0);
        // read cells are held by agent since <= read_time (from all_held_since), and
        // holds only grew by agent's own holds since, so on holds1 too
        assert forall|t: int| #![trigger rs[t]] 0 <= t < rs.len()
            implies held_by_since(holds0, agent, rs[t], read_time) by { }

        // I1
        assert forall|k: int| 0 <= k < s.versions@.len()
            implies (#[trigger] s.versions@[k]).1 <= s.clock by {
            if k < vs0.len() {
                assert(s.versions@[k] == vs0[k]);
                assert(s0.versions@[k].1 <= clock0);
                assert(vs0[k] == s0.versions@[k]);
            } else {
                assert(s.versions@[k].1 == new_clock);
            }
        }
        // I2
        assert forall|q: int| 0 <= q < s.trace@.len()
            implies (#[trigger] s.trace@[q]).read_time < s.trace@[q].write_time
                    && s.trace@[q].write_time <= s.clock by {
            if q < n {
                assert(s.trace@[q] == tr0[q]);
                assert(s0.trace@[q].read_time < s0.trace@[q].write_time);
                assert(s0.trace@[q].write_time <= clock0);
                assert(tr0[q] == s0.trace@[q]);
            } else {
                assert(s.trace@[q] == rec0);
                assert(rec0.read_time <= clock0);
                assert(rec0.write_time == new_clock);
            }
        }
        // I3 (with writer agent)
        assert forall|q: int, c: Cell|
            0 <= q < s.trace@.len() && #[trigger] in_set(s.trace@[q].write_cells@, c)
            implies exists|k: int|
                0 <= k < s.versions@.len()
                && (#[trigger] s.versions@[k]).0 == c
                && s.versions@[k].1 == s.trace@[q].write_time
                && s.versions@[k].3 == s.trace@[q].agent by {
            if q < n {
                assert(s.trace@[q] == tr0[q]);
                assert(in_set(s0.trace@[q].write_cells@, c));
                let k = choose|k: int|
                    0 <= k < s0.versions@.len()
                    && (#[trigger] s0.versions@[k]).0 == c
                    && s0.versions@[k].1 == s0.trace@[q].write_time
                    && s0.versions@[k].3 == s0.trace@[q].agent;
                assert(s.versions@[k] == vs0[k]);
                assert(0 <= k < s.versions@.len()
                    && s.versions@[k].0 == c
                    && s.versions@[k].1 == s.trace@[q].write_time
                    && s.versions@[k].3 == s.trace@[q].agent);
            } else {
                assert(s.trace@[q] == rec0);
                assert(in_set(wcells, c));
                let t = choose|t: int| 0 <= t < wcells.len() && wcells[t] == c;
                assert(wcells[t] == writes@[t].0);
                let k = vs0.len() + t;
                assert(s.versions@[k] == (writes@[k - vs0.len()].0, new_clock, writes@[k - vs0.len()].1, agent));
                assert(s.versions@[k].0 == c);
                assert(s.versions@[k].1 == new_clock);
                assert(s.versions@[k].3 == agent);
                assert(0 <= k < s.versions@.len()
                    && s.versions@[k].0 == c
                    && s.versions@[k].1 == s.trace@[q].write_time
                    && s.versions@[k].3 == s.trace@[q].agent);
            }
        }
        // I4: no window
        assert(!a1_cross(s.trace@)) by {
            if a1_cross(s.trace@) {
                let (i, j, c) = choose|i: int, j: int, c: Cell|
                    0 <= i < s.trace@.len() && 0 <= j < s.trace@.len() && i != j
                    && #[trigger] in_set(s.trace@[i].read_cells@, c)
                    && #[trigger] in_set(s.trace@[j].write_cells@, c)
                    && s.trace@[i].read_time < s.trace@[j].write_time
                    && s.trace@[j].write_time < s.trace@[i].write_time;
                if i < n && j < n {
                    assert(s.trace@[i] == s0.trace@[i]);
                    assert(s.trace@[j] == s0.trace@[j]);
                    assert(in_set(s0.trace@[i].read_cells@, c));
                    assert(in_set(s0.trace@[j].write_cells@, c));
                    assert(s0.trace@[i].read_time < s0.trace@[j].write_time);
                    assert(s0.trace@[j].write_time < s0.trace@[i].write_time);
                    assert(a1_cross(s0.trace@));
                    assert(false);
                } else if i == n {
                    // the new record reads c at read_time, holding c (as `agent`)
                    // since <= read_time -- the hold all_held_since found in holds0;
                    // the old writer j is another agent, and its write is a version
                    // by that agent (I3 on s0); H3 on s0 bounds that version's time
                    // by the hold's start, hence by read_time -- but the window says
                    // read_time < write_time(j).
                    assert(j < n);
                    assert(s.trace@[i] == rec0);
                    assert(s.trace@[j] == s0.trace@[j]);
                    assert(s0.trace@[j].agent != agent);
                    assert(in_set(s0.trace@[j].write_cells@, c));
                    let k = choose|k: int|
                        0 <= k < s0.versions@.len()
                        && (#[trigger] s0.versions@[k]).0 == c
                        && s0.versions@[k].1 == s0.trace@[j].write_time
                        && s0.versions@[k].3 == s0.trace@[j].agent;
                    assert(in_set(rs, c));
                    let t = choose|t: int| 0 <= t < rs.len() && rs[t] == c;
                    assert(held_by_since(holds0, agent, rs[t], read_time));
                    let h = held_witness(holds0, agent, rs[t], read_time);
                    assert(s0.holds@ == holds0);
                    assert(s0.holds@[h].0 == s0.versions@[k].0);
                    assert(s0.versions@[k].3 != s0.holds@[h].1);
                    assert(s0.versions@[k].1 <= s0.holds@[h].2);
                    assert(s0.trace@[j].write_time <= read_time);
                    assert(false);
                } else {
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
        // H3: old versions with the unchanged holds carry over; a new version is
        // agent's own write to a cell whose only hold is agent's, so no foreign
        // hold on it exists
        assert forall|i: int, k: int|
            0 <= i < s.holds@.len() && 0 <= k < s.versions@.len()
            && (#[trigger] s.holds@[i]).0 == (#[trigger] s.versions@[k]).0
            && s.versions@[k].3 != s.holds@[i].1
            implies s.versions@[k].1 <= s.holds@[i].2 by {
            if k < vs0.len() {
                assert(s.versions@[k] == vs0[k]);
                assert(s.holds@ == holds1);
            } else {
                let u = k - vs0.len();
                assert(s.versions@[k] == (writes@[u].0, new_clock, writes@[u].1, agent));
                assert(s.holds@[i].0 == writes@[u].0);
                assert(s.holds@[i].1 == agent);
                assert(false);
            }
        }
        // H2: holds unchanged since acquisition, clock grew
        assert forall|i: int| 0 <= i < s.holds@.len()
            implies (#[trigger] s.holds@[i]).2 <= s.clock by {
            assert(s.holds@[i].2 <= clock0);
        }
        assert(s.inv_versions_le_clock());
        assert(s.inv_trace_times());
        assert(s.inv_link());
        assert(s.inv_holds_distinct());
        assert(s.inv_holds_since_le_clock());
        assert(s.inv_no_foreign_write_since_hold());
        assert(s.inv());
    }
    (s, true)
}

/// release: drop every hold of `agent`.  The kept holds are elements of the
/// old ones, so their properties carry over one by one; distinctness is kept
/// by the invariant "no kept hold shares a cell with any hold not yet
/// scanned", which the push re-establishes from the old table's distinctness.
pub fn release_step(s: PessStore, agent: Agent) -> (r: PessStore)
    requires s.inv(),
    ensures
        r.inv(),
        r.clock == s.clock,
        r.versions@ == s.versions@,
        r.trace@ == s.trace@,
        forall|j: int| 0 <= j < r.holds@.len() ==> (#[trigger] r.holds@[j]).1 != agent,
{
    let ghost s0 = s;
    proof { assert(s0.inv()); }
    let mut s = s;
    let ghost holds0 = s.holds@;
    let ghost vs = s.versions@;
    let clock0 = s.clock;
    let mut out: Vec<(Cell, Agent, Time)> = Vec::new();
    let n = s.holds.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == holds0.len(),
            s.holds@ == holds0,
            s.versions@ == vs,
            s.clock == clock0,
            s.trace@ == s0.trace@,
            s.inv(),
            // the old table's facts, usable at any index
            forall|i: int, j: int|
                0 <= i < holds0.len() && 0 <= j < holds0.len() && i != j
                ==> (#[trigger] holds0[i]).0 != (#[trigger] holds0[j]).0,
            forall|i: int| 0 <= i < holds0.len() ==> (#[trigger] holds0[i]).2 <= clock0,
            forall|i: int, m: int|
                0 <= i < holds0.len() && 0 <= m < vs.len()
                && (#[trigger] holds0[i]).0 == (#[trigger] vs[m]).0
                && vs[m].3 != holds0[i].1
                ==> vs[m].1 <= holds0[i].2,
            // what has been kept so far
            forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).1 != agent,
            forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).2 <= clock0,
            forall|j: int, m: int|
                0 <= j < out@.len() && 0 <= m < vs.len()
                && (#[trigger] out@[j]).0 == (#[trigger] vs[m]).0
                && vs[m].3 != out@[j].1
                ==> vs[m].1 <= out@[j].2,
            forall|j1: int, j2: int|
                0 <= j1 < out@.len() && 0 <= j2 < out@.len() && j1 != j2
                ==> (#[trigger] out@[j1]).0 != (#[trigger] out@[j2]).0,
            // no kept hold shares a cell with a hold not yet scanned
            forall|j: int, i: int|
                0 <= j < out@.len() && k <= i < holds0.len()
                ==> (#[trigger] out@[j]).0 != (#[trigger] holds0[i]).0,
        decreases n - k
    {
        let (hc, ha, hs) = s.holds[k];
        proof { assert(holds0[k as int] == (hc, ha, hs)); }
        if ha != agent {
            let ghost before = out@;
            out.push((hc, ha, hs));
            proof {
                let last = before.len() as int;
                assert(out@ == before.push((hc, ha, hs)));
                assert(out@[last] == holds0[k as int]);
                assert forall|j: int| 0 <= j < out@.len()
                    implies (#[trigger] out@[j]).1 != agent by { if j < last { assert(out@[j] == before[j]); } }
                assert forall|j: int| 0 <= j < out@.len()
                    implies (#[trigger] out@[j]).2 <= clock0 by {
                    if j < last { assert(out@[j] == before[j]); } else { assert(holds0[k as int].2 <= clock0); }
                }
                assert forall|j: int, m: int|
                    0 <= j < out@.len() && 0 <= m < vs.len()
                    && (#[trigger] out@[j]).0 == (#[trigger] vs[m]).0
                    && vs[m].3 != out@[j].1
                    implies vs[m].1 <= out@[j].2 by {
                    if j < last { assert(out@[j] == before[j]); }
                }
                assert forall|j1: int, j2: int|
                    0 <= j1 < out@.len() && 0 <= j2 < out@.len() && j1 != j2
                    implies (#[trigger] out@[j1]).0 != (#[trigger] out@[j2]).0 by {
                    if j1 < last && j2 < last {
                        assert(out@[j1] == before[j1]); assert(out@[j2] == before[j2]);
                    } else if j1 == last {
                        assert(out@[j2] == before[j2]);
                        assert(before[j2].0 != holds0[k as int].0);
                    } else {
                        assert(out@[j1] == before[j1]);
                        assert(before[j1].0 != holds0[k as int].0);
                    }
                }
                assert forall|j: int, i: int|
                    0 <= j < out@.len() && k + 1 <= i < holds0.len()
                    implies (#[trigger] out@[j]).0 != (#[trigger] holds0[i]).0 by {
                    if j < last {
                        assert(out@[j] == before[j]);
                    } else {
                        assert(out@[j] == holds0[k as int]);
                        assert(holds0[k as int].0 != holds0[i].0);
                    }
                }
            }
        } else {
            proof {
                assert forall|j: int, i: int|
                    0 <= j < out@.len() && k + 1 <= i < holds0.len()
                    implies (#[trigger] out@[j]).0 != (#[trigger] holds0[i]).0 by { }
            }
        }
        k = k + 1;
    }
    let ghost kept = out@;
    s.holds = out;
    proof {
        assert(s.holds@ == kept);
        assert(s.versions@ == vs);
        assert(s.clock == clock0);
        assert(s.inv_versions_le_clock());
        assert(s.inv_trace_times());
        assert(s.inv_link());
        assert(!a1_cross(s.trace@));
        assert(s.inv_holds_distinct());
        assert(s.inv_holds_since_le_clock());
        assert(s.inv_no_foreign_write_since_hold());
        assert(s.inv());
    }
    s
}

/// tick: clock + 1 (unchanged at the ceiling).
pub fn tick_step(s: PessStore) -> (r: PessStore)
    requires s.inv(),
    ensures
        r.inv(),
        s.clock < u64::MAX ==> r.clock == s.clock + 1,
        s.clock == u64::MAX ==> r.clock == s.clock,
        r.versions@ == s.versions@,
        r.holds@ == s.holds@,
        r.trace@ == s.trace@,
{
    if s.clock == u64::MAX {
        return s;
    }
    let ghost s0 = s;
    proof { assert(s0.inv()); }
    let mut s = s;
    s.clock = s.clock + 1;
    proof {
        assert(s.versions@ == s0.versions@);
        assert(s.trace@ == s0.trace@);
        assert(s.holds@ == s0.holds@);
        assert(s0.clock < s.clock);
    }
    proof {
        assert forall|k: int| 0 <= k < s.versions@.len()
            implies (#[trigger] s.versions@[k]).1 <= s.clock by {
            assert(s0.versions@[k].1 <= s0.clock);
        }
        assert forall|i: int| 0 <= i < s.trace@.len()
            implies (#[trigger] s.trace@[i]).read_time < s.trace@[i].write_time
                    && s.trace@[i].write_time <= s.clock by {
            assert(s0.trace@[i].write_time <= s0.clock);
        }
        assert forall|i: int| 0 <= i < s.holds@.len()
            implies (#[trigger] s.holds@[i]).2 <= s.clock by {
            assert(s0.holds@[i].2 <= s0.clock);
        }
        assert(s.inv_link());
        assert(!a1_cross(s.trace@));
        assert(s.inv_holds_distinct());
        assert(s.inv_no_foreign_write_since_hold());
        assert(s.inv());
    }
    s
}

// ---------------------------------------------------------------------
// the lock predicate and the concurrent store
// ---------------------------------------------------------------------

pub struct PessPred;

impl RwLockPredicate<PessStore> for PessPred {
    open spec fn inv(self, v: PessStore) -> bool {
        v.inv()
    }
}

pub struct PessConcurrent {
    pub lock: RwLock<PessStore, PessPred>,
}

impl PessConcurrent {
    pub fn new() -> (r: PessConcurrent) {
        let store = PessStore::new();
        let lock = RwLock::<PessStore, PessPred>::new(store, Ghost(PessPred));
        PessConcurrent { lock }
    }

    /// begin under the exclusive lock (it acquires holds).  None on conflict.
    pub fn begin(&self, agent: Agent, cells: Vec<Cell>) -> (r: Option<Snapshot>) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let (store2, snap) = begin_step(store, agent, cells);
        assert(store2.inv());
        write_handle.release_write(store2);
        snap
    }

    /// commit under the exclusive lock; (applied, clock afterwards).
    pub fn commit(&self, snap: Snapshot, writes: &Vec<(Cell, Val)>) -> (r: (bool, Time)) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let (store2, ok) = commit_step(store, snap, writes);
        assert(store2.inv());
        let t = store2.clock;
        write_handle.release_write(store2);
        (ok, t)
    }

    pub fn release(&self, agent: Agent) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let store2 = release_step(store, agent);
        assert(store2.inv());
        write_handle.release_write(store2);
    }

    pub fn tick(&self) -> (t: Time) {
        let (store, write_handle) = self.lock.acquire_write();
        assert(store.inv());
        let store2 = tick_step(store);
        assert(store2.inv());
        let t = store2.clock;
        write_handle.release_write(store2);
        t
    }

    pub fn clock(&self) -> (t: Time) {
        let handle = self.lock.acquire_read();
        let store = handle.borrow();
        let t = store.clock;
        handle.release_read();
        t
    }

    /// The concurrent safety statement at a read handle: whatever state
    /// this thread observes, after any interleaving by any other threads,
    /// its trace has no cross-agent stale-generation window and its holds
    /// are exclusive.
    pub fn trace_is_a1_free(&self) {
        let handle = self.lock.acquire_read();
        let store = handle.borrow();
        proof {
            assert(store.inv());
            assert(!a1_cross(store.trace@));
            assert(store.inv_holds_distinct());
        }
        handle.release_read();
    }
}

// ---------------------------------------------------------------------
// non-vacuity: the excluded window is satisfiable
// ---------------------------------------------------------------------

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
        assert(tr@[1].agent != tr@[0].agent);
        assert(tr@[1].read_time < tr@[0].write_time);
        assert(tr@[0].write_time < tr@[1].write_time);
        assert(a1_cross(tr@));
    }
}

} // verus!
