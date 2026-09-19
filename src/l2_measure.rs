//! l2_measure.rs -- measure A3 prevention through the VERIFIED runtime,
//! against a real baseline, on schedules that can tell them apart.
//!
//! The guarded arm is `crate::l2_exec::L2Runtime`: the same bytes Verus
//! checks, proofs erased by the `verus!` macro, exactly as
//! `si_concurrent.rs` is at L1.  The unguarded arm is
//! `crate::l2_unguarded::UnguardedStore`: a real second execution that
//! validates reads and does not cascade.  Neither arm is a relabelling
//! of the other; an earlier version of this file produced its "baseline"
//! by rewriting abort flags in the reporting loop, which made the
//! 1000/1000 figure a tautology.
//!
//! Scenarios vary with the seed in SHAPE, not only in the values
//! written: chain length, whether a conflicting writer is interleaved
//! inside a dependent's read-to-commit window, and which committed
//! transaction is retracted.  A harness whose seed reaches only the
//! payload runs one scenario N times and its rule-of-three interval
//! presumes an independence it does not have.
//!
//! THE DECIDER IS NOW VERIFIED.
//! `L2Runtime::can_commit` carries `ensures b == commit_valid(self.view(),
//! t as int)` -- two-sided, so branching on it establishes `commit`'s
//! precondition by proof. This driver calls it. An earlier version called
//! `commit_gate`, a hand transcription in this file, which is now deleted:
//! a verified decision procedure that the measurement does not call is the
//! same equivocation as measuring a twin instead of the verified runtime.
//! The two agreed on all 3,000 scenarios before the transcription was
//! removed.
//!
//! HISTORICAL NOTE ON THE OLD UNVERIFIED PATH.
//! `L2Runtime::commit` takes `commit_valid(view, t)` as a precondition
//! and the crate ships no verified decision procedure for it.  Plain
//! cargo erases preconditions, so the caller must establish it.
//! Before `can_commit` existed, this driver transcribed `commit_valid` by
//! hand, and that transcription was the last unverified link in the L2
//! chain. It is gone.
//!
//! `can_commit` reads `read_set` directly, which is why that field is a
//! `Vec`: vstd's `HashSetWithView` exposes no iterator, so `reads_fresh`
//! could not be decided in exec mode while it was a hash set.
//!
//! 2026-09-16 round 26: every `L2Runtime` entry point checks its own
//! precondition. `commit` decides `commit_valid` itself, `write`, `read`,
//! `commit`, `abort` and `externalize` return whether they acted, `begin`
//! returns `None` when its counters are exhausted, and a refused call leaves
//! the runtime unchanged. This driver asserts every call it expects to act.
//!
//! 2026-09-16 round 28: A3 is an EXTERNALIZED operation with an aborted
//! operation in its causal closure (Anomalies.tla CausalCascade since round
//! 23, lib_l2_safety.rs a3_witness since round 24). OVERRULED (rounds <= 26):
//! this file scored a surviving -- committed, unaborted -- dependent of an
//! aborted operation, which the cascade "prevents" by flagging dependents
//! aborted even when their effects are already out. Both arms now release
//! effects, and the trace carries the flag:
//!   - the unguarded baseline releases every transaction's effects at commit
//!     (`UnguardedStore::commit` sets `externalized`);
//!   - the verified runtime releases through `L2Runtime::externalize`, which
//!     output commit refuses until the transaction's causal closure is out.
//! The schedule adds a REVIEW: one committed transaction is under review and
//! is retracted or approved (seeded). Every other committed transaction asks
//! to release at once; under output commit its dependents are held until the
//! decision. A late review (seeded) comes after the reviewed transaction has
//! released, and the verified runtime then refuses the retraction: released
//! effects need compensation, not abort. Both costs are measured -- effects
//! held, and retractions refused -- next to the anomaly count.
//!
//! 2026-09-19 round 33: A THIRD ARM, AND A COUNT THAT READS NO FLAG.
//! With two arms the overruled predicate and the current one agreed in every
//! cell -- 519/519, 624/624, 563/563 on the baseline, 0/0 on the verified
//! runtime -- so nothing here showed that the change of definition in rounds
//! 23-28 mattered. It could not have: `UnguardedStore` releases every
//! transaction at commit and never flags a dependent, so on its traces
//! `externalized == committed` and `aborted` is set on the reviewed operation
//! alone, which makes the two predicates the same predicate. The arm that
//! separates them is the superseded design itself (`l2_cascade::CascadeStore`:
//! release at commit AND cascade): the overruled predicate reads zero on it
//! while the current one fires exactly as often as on the unguarded baseline.
//! Both A3 predicates still read flags that the runtime under test sets for
//! itself, so every arm also reports `exposed`: effects that are OUT although
//! the review asked to withdraw their basis. It reads no abort flag. On it the
//! two release-at-commit arms are identical, and the verified runtime is NOT
//! zero: it is exposed in exactly the scenarios where it refused a retraction.
//! OVERRULED (rounds 28-32): a two-valued arm switch on `run_experiment`, two
//! arms, and a refusal count reported without what it left in the world.

use std::collections::BTreeSet;

use crate::l2_cascade::CascadeStore;
use crate::l2_exec::L2Runtime;
use crate::l2_unguarded::UnguardedStore;

/// One emitted provenance record.
#[derive(Debug, Clone)]
pub struct Prov {
    pub txn: u64,
    pub committed: bool,
    pub aborted: bool,
    pub externalized: bool,
    pub predecessors: Vec<u64>,
}

/// Every operation reachable from `start` through recorded predecessors.
/// The verified runtime records the closure directly; the baseline records
/// only direct writers, so the closure is taken here, over the trace, for
/// both arms alike.
fn closure(trace: &[Prov], start: &Prov) -> BTreeSet<u64> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<u64> = start.predecessors.clone();
    while let Some(p) = stack.pop() {
        if seen.insert(p) {
            if let Some(q) = trace.iter().find(|x| x.txn == p) {
                stack.extend(q.predecessors.iter().copied());
            }
        }
    }
    seen
}

/// A3 over an emitted provenance trace: an operation whose effects left the
/// runtime while an operation in its causal closure is aborted.
pub fn detect_a3(trace: &[Prov]) -> Option<(u64, u64)> {
    for r in trace.iter().filter(|r| r.externalized) {
        for p in closure(trace, r) {
            if trace.iter().any(|x| x.txn == p && x.aborted) {
                return Some((r.txn, p));
            }
        }
    }
    None
}

/// The OVERRULED A3 (rounds <= 26), kept so both arms report it next to the
/// current one: a surviving (committed, unaborted) operation with an aborted
/// operation in its causal closure. The cascade prevents it by relabeling.
pub fn detect_a3_unpropagated(trace: &[Prov]) -> Option<(u64, u64)> {
    for r in trace.iter().filter(|r| r.committed && !r.aborted) {
        for p in closure(trace, r) {
            if trace.iter().any(|x| x.txn == p && x.aborted) {
                return Some((r.txn, p));
            }
        }
    }
    None
}

/// Effects that are OUT although the review asked to withdraw their basis:
/// the reviewed operation itself and every operation with it in its causal
/// closure, counted when externalized. This reads no abort flag. It asks the
/// same question of every arm -- what reached the world -- whereas both A3
/// predicates read flags the runtime under test sets for itself.
pub fn exposed_effects(trace: &[Prov], reviewed: u64, retraction_asked: bool) -> u64 {
    if !retraction_asked {
        return 0;
    }
    trace
        .iter()
        .filter(|r| r.externalized && (r.txn == reviewed || closure(trace, r).contains(&reviewed)))
        .count() as u64
}

/// Dependents flagged aborted AFTER their effects were out: R5's class
/// (lib_a3_residue.rs), the operations the flat-trace projection drops.
pub fn relabeled_after_release(trace: &[Prov], reviewed: u64) -> u64 {
    trace.iter().filter(|r| r.txn != reviewed && r.aborted && r.externalized).count() as u64
}

/// The SUPERSEDED gate, transcribed from l2_causal.rs:126-128 so the
/// defect stays visible and cannot be reintroduced silently:
///
/// ```text
/// for c in &t.read_set { if writes.contains_key(c) { continue; } ... }
/// ```
///
/// It skips the freshness check for every cell the transaction itself
/// writes, and carries none of the started / !committed / !aborted
/// self-guards.  Kept ONLY so `carve_out_gate_is_weaker` can demonstrate
/// that the two gates disagree.  Never call it from a measurement.
pub fn carve_out_gate(rt: &L2Runtime, t: u64, cells: &[u64], writes: &[u64]) -> bool {
    let txn = match rt.txns.get(&t) {
        Some(x) => x,
        None => return false,
    };
    for c in cells {
        if writes.contains(c) {
            continue; // <- the defect
        }
        let observed = match txn.read_values.get(c) {
            Some(v) => *v,
            None => return false,
        };
        match rt.cell_value.get(c) {
            Some(current) if *current == observed => {}
            _ => return false,
        }
    }
    for p in &txn.predecessors {
        match rt.txns.get(p) {
            Some(q) if q.committed && !q.aborted => {}
            _ => return false,
        }
    }
    true
}

/// The shape of one scenario, derived from the seed.
#[derive(Debug, Clone, Copy)]
pub struct Shape {
    pub chain: usize,
    pub interleave: bool,
    /// which committed transaction is under review
    pub abort_at: usize,
    /// the review retracts it (otherwise approves it)
    pub retract: bool,
    /// the review comes after the reviewed transaction has released its effects
    pub late_review: bool,
}

/// Vary the SHAPE with the seed, not just the payload.
pub fn shape_of(seed: u64, depth: usize) -> Shape {
    let chain = depth + (seed % 3) as usize;
    Shape {
        chain,
        interleave: seed % 2 == 1,
        abort_at: (seed as usize / 2) % chain,
        retract: (seed / 7) % 4 != 0,
        late_review: (seed / 11) % 4 == 0,
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Outcome {
    /// A3: an externalized operation with an aborted operation in its closure
    pub a3: bool,
    /// the overruled A3: a surviving operation with an aborted one in its closure
    pub a3_unpropagated: bool,
    /// operations aborted by the cascade (the reviewed one excluded)
    pub cascaded: u64,
    /// commits refused
    pub refused: u64,
    /// operations whose release was refused at least once (output commit held them)
    pub held: u64,
    /// operations whose effects are out at the end
    pub released: u64,
    /// operations committed and not aborted at the end
    pub live: u64,
    /// the review asked for a retraction and the runtime refused it
    pub retraction_refused: bool,
    /// effects out although the review asked to withdraw their basis (no flag read)
    pub exposed: u64,
    /// dependents flagged aborted after their effects were out
    pub relabeled: u64,
}

fn trace_of_runtime(rt: &L2Runtime) -> Vec<Prov> {
    let mut trace = Vec::new();
    for id in 0..rt.next_txn {
        if let Some(x) = rt.txns.get(&id) {
            trace.push(Prov {
                txn: id,
                committed: x.committed,
                aborted: x.aborted,
                externalized: x.externalized,
                predecessors: x.predecessors.clone(),
            });
        }
    }
    trace
}

/// One release pass in id order, which is causal order: a transaction only
/// reads cells that earlier transactions committed. Every committed, unaborted,
/// unreleased transaction other than `exempt` asks `externalize`.
fn release_pass(rt: &mut L2Runtime, exempt: Option<u64>, held: &mut BTreeSet<u64>) {
    for id in 0..rt.next_txn {
        if Some(id) == exempt {
            continue;
        }
        let ask = match rt.txns.get(&id) {
            Some(x) => x.committed && !x.aborted && !x.externalized,
            None => false,
        };
        if ask && !rt.externalize(id) {
            held.insert(id);
        }
    }
}

/// Guarded arm: the verified runtime.
///
/// Every call this driver makes is one the runtime accepts, and it asserts
/// so: `read` needs the cell to exist, `write` an uncommitted transaction,
/// `commit` a valid one. The runtime checks each of these itself (round 26)
/// and refuses instead of assuming it; the `written` frontier below is what
/// keeps every `read` accepted when a commit is refused and its cell is never
/// created. `externalize` and the review's `abort` are the two calls whose
/// refusal is the measurement, so their results are recorded, not asserted.
pub fn run_guarded(seed: u64, depth: usize) -> Outcome {
    let s = shape_of(seed, depth);
    let base = 1_000 + (seed % 11) * 100;
    let mut rt = L2Runtime::new();
    let mut refused = 0u64;

    let root = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.write(root, base, 40 + seed % 5), "L2Runtime::write refused");
    if !rt.can_commit(root) {
        return Outcome { refused: 1, ..Outcome::default() };
    }
    assert!(rt.commit(root), "L2Runtime::commit refused");
    // Cells known to exist. `read` may only target one of these.
    let mut written: Vec<u64> = vec![base];
    let mut committed: Vec<u64> = vec![root];
    let mut next_cell = base + 1;

    for k in 0..s.chain {
        let rc = written[written.len() - 1];
        let wc = next_cell;
        let t = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.read(t, rc), "L2Runtime::read refused");
        assert!(rt.write(t, wc, 70 + k as u64), "L2Runtime::write refused");
        // Adversarial interleave: a concurrent writer lands on the cell
        // t has already read, inside t's read-to-commit window, so t's
        // read set goes stale and commit must refuse.
        if s.interleave && k % 2 == 0 {
            let c = rt.begin().expect("L2Runtime counters exhausted");
            assert!(rt.write(c, rc, 900 + k as u64), "L2Runtime::write refused");
            if rt.can_commit(c) {
                assert!(rt.commit(c), "L2Runtime::commit refused");
                committed.push(c);
            }
        }

        if rt.can_commit(t) {
            assert!(rt.commit(t), "L2Runtime::commit refused");
            committed.push(t);
            written.push(wc);
            next_cell += 1;
        } else {
            refused += 1;
            assert!(rt.abort(t), "L2Runtime::abort refused");
        }
    }

    let reviewed = committed[s.abort_at % committed.len()];
    let mut held = BTreeSet::new();
    // Before the review: everything asks to release, except the transaction
    // under review -- unless the review is late and it has released too.
    release_pass(&mut rt, if s.late_review { None } else { Some(reviewed) }, &mut held);

    let mut retraction_refused = false;
    if s.retract {
        retraction_refused = !rt.abort(reviewed);
    }
    // After the review: nothing is exempt.
    release_pass(&mut rt, None, &mut held);

    let trace = trace_of_runtime(&rt);
    let cascaded = trace.iter().filter(|x| x.aborted && x.txn != reviewed && x.committed).count() as u64;
    Outcome {
        a3: detect_a3(&trace).is_some(),
        a3_unpropagated: detect_a3_unpropagated(&trace).is_some(),
        cascaded,
        refused,
        held: held.len() as u64,
        released: trace.iter().filter(|x| x.externalized).count() as u64,
        live: trace.iter().filter(|x| x.committed && !x.aborted).count() as u64,
        retraction_refused,
        exposed: exposed_effects(&trace, reviewed, s.retract),
        relabeled: relabeled_after_release(&trace, reviewed),
    }
}

/// Which runtime a scenario runs on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arm {
    /// `l2_exec::L2Runtime`: cascades, and releases under output commit
    Verified,
    /// `l2_unguarded::UnguardedStore`: releases at commit, does not cascade
    Unguarded,
    /// `l2_cascade::CascadeStore`: releases at commit AND cascades -- the
    /// superseded design of rounds <= 22
    Cascade,
}

impl Arm {
    pub fn label(self) -> &'static str {
        match self {
            Arm::Verified => "verified",
            Arm::Unguarded => "unguarded",
            Arm::Cascade => "cascade",
        }
    }
}

/// The provenance trace of a release-at-commit store.
pub fn provenance_of(st: &UnguardedStore) -> Vec<Prov> {
    st.txns
        .iter()
        .enumerate()
        .map(|(i, x)| Prov {
            txn: i as u64,
            committed: x.committed,
            aborted: x.aborted,
            externalized: x.externalized,
            predecessors: x.predecessors.clone(),
        })
        .collect()
}

/// A baseline store that releases effects at commit. Both baselines run the
/// SAME schedule through the SAME driver below, so a difference between their
/// figures is a difference between the stores and nothing else.
pub trait ReleasesAtCommit {
    fn begin(&mut self) -> u64;
    fn read(&mut self, t: u64, c: u64);
    fn commit(&mut self, t: u64, writes: &[(u64, u64)]) -> bool;
    /// the review retracts `t`
    fn retract(&mut self, t: u64);
    fn provenance(&self) -> Vec<Prov>;
}

impl ReleasesAtCommit for UnguardedStore {
    fn begin(&mut self) -> u64 {
        UnguardedStore::begin(self)
    }
    fn read(&mut self, t: u64, c: u64) {
        UnguardedStore::read(self, t, c)
    }
    fn commit(&mut self, t: u64, writes: &[(u64, u64)]) -> bool {
        UnguardedStore::commit(self, t, writes)
    }
    fn retract(&mut self, t: u64) {
        UnguardedStore::abort(self, t)
    }
    fn provenance(&self) -> Vec<Prov> {
        provenance_of(self)
    }
}

impl ReleasesAtCommit for CascadeStore {
    fn begin(&mut self) -> u64 {
        CascadeStore::begin(self)
    }
    fn read(&mut self, t: u64, c: u64) {
        CascadeStore::read(self, t, c)
    }
    fn commit(&mut self, t: u64, writes: &[(u64, u64)]) -> bool {
        CascadeStore::commit(self, t, writes)
    }
    fn retract(&mut self, t: u64) {
        CascadeStore::abort(self, t);
    }
    fn provenance(&self) -> Vec<Prov> {
        provenance_of(&self.inner)
    }
}

/// The release-at-commit schedule: the same scenario the guarded arm runs,
/// with nothing to hold and no retraction to refuse, since effects leave at
/// commit. `late_review` has no meaning here -- every review is late.
fn run_release_at_commit<S: ReleasesAtCommit>(mut st: S, seed: u64, depth: usize) -> Outcome {
    let s = shape_of(seed, depth);
    let base = 1_000 + (seed % 11) * 100;
    let mut refused = 0u64;

    let root = st.begin();
    if !st.commit(root, &[(base, 40 + seed % 5)]) {
        return Outcome { refused: 1, ..Outcome::default() };
    }
    let mut written: Vec<u64> = vec![base];
    let mut committed: Vec<u64> = vec![root];
    let mut next_cell = base + 1;

    for k in 0..s.chain {
        let rc = written[written.len() - 1];
        let wc = next_cell;
        let t = st.begin();
        st.read(t, rc);

        if s.interleave && k % 2 == 0 {
            let c = st.begin();
            if st.commit(c, &[(rc, 900 + k as u64)]) {
                committed.push(c);
            }
        }

        if st.commit(t, &[(wc, 70 + k as u64)]) {
            committed.push(t);
            written.push(wc);
            next_cell += 1;
        } else {
            refused += 1;
        }
    }

    let reviewed = committed[s.abort_at % committed.len()];
    if s.retract {
        st.retract(reviewed);
    }

    let trace = st.provenance();
    Outcome {
        a3: detect_a3(&trace).is_some(),
        a3_unpropagated: detect_a3_unpropagated(&trace).is_some(),
        cascaded: trace.iter().filter(|x| x.aborted && x.txn != reviewed && x.committed).count() as u64,
        refused,
        held: 0,
        released: trace.iter().filter(|x| x.externalized).count() as u64,
        live: trace.iter().filter(|x| x.committed && !x.aborted).count() as u64,
        retraction_refused: false,
        exposed: exposed_effects(&trace, reviewed, s.retract),
        relabeled: relabeled_after_release(&trace, reviewed),
    }
}

/// Unguarded arm: releases at commit, does not cascade.
pub fn run_unguarded(seed: u64, depth: usize) -> Outcome {
    run_release_at_commit(UnguardedStore::new(), seed, depth)
}

/// Cascade arm: releases at commit AND cascades -- the superseded design.
pub fn run_cascade(seed: u64, depth: usize) -> Outcome {
    run_release_at_commit(CascadeStore::new(), seed, depth)
}

pub struct Summary {
    pub runs: u32,
    pub depth: usize,
    pub arm: Arm,
    pub a3_hits: u32,
    pub a3_unpropagated_hits: u32,
    pub cascaded: u64,
    pub refused: u64,
    pub held: u64,
    pub released: u64,
    pub live: u64,
    pub retractions: u32,
    pub retractions_refused: u32,
    /// effects out although the review asked to withdraw their basis
    pub exposed: u64,
    /// scenarios with at least one such effect
    pub exposed_scenarios: u32,
    /// dependents flagged aborted after their effects were out
    pub relabeled: u64,
}

pub fn run_experiment(runs: u32, depth: usize, arm: Arm) -> Summary {
    let mut s = Summary {
        runs, depth, arm, a3_hits: 0, a3_unpropagated_hits: 0, cascaded: 0, refused: 0,
        held: 0, released: 0, live: 0, retractions: 0, retractions_refused: 0,
        exposed: 0, exposed_scenarios: 0, relabeled: 0,
    };
    for i in 0..runs as u64 {
        let seed = i.wrapping_mul(2_654_435_761) ^ (i << 7);
        let o = match arm {
            Arm::Verified => run_guarded(seed, depth),
            Arm::Unguarded => run_unguarded(seed, depth),
            Arm::Cascade => run_cascade(seed, depth),
        };
        if o.a3 {
            s.a3_hits += 1;
        }
        if o.a3_unpropagated {
            s.a3_unpropagated_hits += 1;
        }
        if shape_of(seed, depth).retract {
            s.retractions += 1;
        }
        if o.retraction_refused {
            s.retractions_refused += 1;
        }
        s.cascaded += o.cascaded;
        s.refused += o.refused;
        s.held += o.held;
        s.released += o.released;
        s.live += o.live;
        s.exposed += o.exposed;
        if o.exposed > 0 {
            s.exposed_scenarios += 1;
        }
        s.relabeled += o.relabeled;
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verified_runtime_prevents_a3_at_every_depth() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, Arm::Verified);
            assert_eq!(s.a3_hits, 0, "verified L2 runtime admitted A3 at depth {depth}");
            assert_eq!(s.a3_unpropagated_hits, 0, "verified L2 runtime left a surviving dependent of an aborted operation at depth {depth}");
        }
    }

    #[test]
    fn unguarded_baseline_exhibits_a3_but_not_vacuously() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, Arm::Unguarded);
            assert!(
                s.a3_hits > 0,
                "unguarded baseline never exhibits A3 at depth {depth}; \
                 a prevention result against a baseline that does not fail is vacuous"
            );
            assert!(
                s.a3_hits < s.runs,
                "unguarded baseline exhibits A3 in EVERY scenario at depth {depth}; \
                 the scenarios cannot discriminate and the figure is a tautology"
            );
        }
    }

    #[test]
    fn the_gate_actually_refuses_somewhere() {
        let s = run_experiment(1000, 3, Arm::Verified);
        assert!(
            s.refused > 0,
            "commit refused nothing in 1000 scenarios; its refusal path is untested \
             and the measurement cannot distinguish it from a gate with no check at all"
        );
    }

    #[test]
    fn output_commit_holds_dependents_of_a_reviewed_transaction() {
        let s = run_experiment(1000, 3, Arm::Verified);
        assert!(
            s.held > 0,
            "no release was ever refused; output commit is untested and the A3 figure \
             cannot distinguish the verified runtime from one that releases at commit"
        );
    }

    #[test]
    fn a_late_review_cannot_retract_released_effects() {
        let s = run_experiment(1000, 3, Arm::Verified);
        assert!(
            s.retractions_refused > 0,
            "no retraction was refused; the late-review path is untested"
        );
        assert!(s.retractions_refused < s.retractions, "every retraction was refused; the cascade path is untested");
    }

    #[test]
    fn every_live_effect_is_released_after_the_review() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, Arm::Verified);
            assert_eq!(
                s.released, s.live,
                "at depth {depth} output commit stranded a live transaction's effects"
            );
        }
    }

    #[test]
    fn the_two_a3_detectors_disagree_exactly_where_effects_are_held_or_out() {
        // A transaction under review is retracted after a dependent committed,
        // with no release: the overruled predicate fires on the baseline trace,
        // the current one does not until the dependent's effects are out.
        let mut trace = vec![
            Prov { txn: 0, committed: true, aborted: true, externalized: false, predecessors: vec![] },
            Prov { txn: 1, committed: true, aborted: false, externalized: false, predecessors: vec![0] },
        ];
        assert!(detect_a3(&trace).is_none(), "an unreleased dependent is not A3");
        assert!(detect_a3_unpropagated(&trace).is_some());
        trace[1].externalized = true;
        assert_eq!(detect_a3(&trace), Some((1, 0)));
        // transitive: a released operation two hops from the aborted one
        trace[1].externalized = false;
        trace.push(Prov { txn: 2, committed: true, aborted: false, externalized: true, predecessors: vec![1] });
        assert_eq!(detect_a3(&trace), Some((2, 0)), "the detector must follow the closure");
    }

    /// Round 33. The superseded design satisfies the overruled predicate in
    /// every scenario and fails the current one exactly as often as the
    /// unguarded baseline does: its cascade moves flags, not effects.
    #[test]
    fn the_superseded_design_passes_the_overruled_predicate_and_fails_the_current_one() {
        for depth in [2usize, 3, 5] {
            let c = run_experiment(1000, depth, Arm::Cascade);
            let u = run_experiment(1000, depth, Arm::Unguarded);
            assert_eq!(
                c.a3_unpropagated_hits, 0,
                "the cascade left a surviving dependent at depth {depth}; this arm no longer models the superseded design"
            );
            assert!(c.a3_hits > 0, "the cascade arm never releases on a retracted basis at depth {depth}; it cannot separate the predicates");
            assert_eq!(
                c.a3_hits, u.a3_hits,
                "at depth {depth} the cascade changed how often an effect is out on a retracted basis; it may only change flags"
            );
            assert!(c.relabeled > 0, "no dependent was flagged after release at depth {depth}; R5's class is unexercised");
            assert_eq!(u.relabeled, 0, "the unguarded baseline does not cascade, so it can relabel nothing");
        }
    }

    /// Round 33. `exposed` reads no abort flag, so the two release-at-commit
    /// arms must agree on it, and the verified runtime is NOT zero on it: it
    /// is exposed in exactly the scenarios where it refused a retraction.
    #[test]
    fn exposure_reads_no_flag_and_the_verified_residue_is_the_refused_retractions() {
        for depth in [2usize, 3, 5] {
            let v = run_experiment(1000, depth, Arm::Verified);
            let u = run_experiment(1000, depth, Arm::Unguarded);
            let c = run_experiment(1000, depth, Arm::Cascade);
            assert_eq!(c.exposed, u.exposed, "a cascade changed what reached the world at depth {depth}");
            assert_eq!(c.exposed_scenarios, u.exposed_scenarios);
            assert_eq!(
                u.exposed_scenarios, u.retractions,
                "release at commit exposes the reviewed operation in every retraction"
            );
            assert!(v.exposed > 0, "late reviews must leave residue at depth {depth}, or the refusal count is unexplained");
            assert!(v.exposed < u.exposed, "output commit exposed no less than release at commit at depth {depth}");
            assert_eq!(
                v.exposed_scenarios, v.retractions_refused,
                "at depth {depth} the verified runtime is exposed somewhere other than where it refused a retraction"
            );
            assert_eq!(v.relabeled, 0, "the verified runtime flagged an operation whose effects were out");
        }
    }

    /// Round 33. A literal trace on which every dependent is flagged: the
    /// overruled predicate is satisfied, and effects are out all the same.
    #[test]
    fn exposure_counts_effects_not_flags() {
        let trace = vec![
            Prov { txn: 0, committed: true, aborted: true, externalized: true, predecessors: vec![] },
            Prov { txn: 1, committed: true, aborted: true, externalized: true, predecessors: vec![0] },
            Prov { txn: 2, committed: true, aborted: true, externalized: false, predecessors: vec![1] },
            Prov { txn: 3, committed: true, aborted: false, externalized: true, predecessors: vec![] },
        ];
        assert_eq!(exposed_effects(&trace, 0, true), 2, "the reviewed operation and its released dependent");
        assert_eq!(exposed_effects(&trace, 0, false), 0, "an approved operation exposes nothing");
        assert_eq!(relabeled_after_release(&trace, 0), 1);
        assert!(detect_a3_unpropagated(&trace).is_none(), "every dependent is flagged: the overruled predicate is satisfied");
        assert_eq!(detect_a3(&trace), Some((1, 0)), "and an effect is out on a retracted basis all the same");
    }

    /// The B4 regression test. A transaction reads a cell, another
    /// transaction overwrites it, and the reader also WRITES that cell.
    /// commit_valid forbids the commit; the superseded carve-out gate
    /// allows it. If this ever stops failing to disagree, the defect is
    /// back.
    #[test]
    fn carve_out_gate_is_weaker_than_commit_valid() {
        let mut rt = L2Runtime::new();
        let a = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.write(a, 1, 10), "L2Runtime::write refused");
        assert!(rt.can_commit(a));
        assert!(rt.commit(a), "L2Runtime::commit refused");
        let b = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.read(b, 1), "L2Runtime::read refused");
        assert!(rt.write(b, 1, 11), "L2Runtime::write refused");
        let c = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.write(c, 1, 99), "L2Runtime::write refused");
        assert!(rt.can_commit(c));
        assert!(rt.commit(c), "L2Runtime::commit refused");
        assert!(
            !rt.can_commit(b),
            "the VERIFIED decision procedure accepted a stale read of a cell the \
             transaction writes; commit_valid forbids it"
        );
        assert!(
            carve_out_gate(&rt, b, &[1], &[1]),
            "the superseded gate no longer accepts the case it was shipped accepting; \
             if this changed, re-audit l2_causal.rs before deleting this test"
        );
    }
}
