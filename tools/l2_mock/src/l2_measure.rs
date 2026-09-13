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

use crate::l2_exec::L2Runtime;
use crate::l2_unguarded::UnguardedStore;

/// One emitted provenance record.
#[derive(Debug, Clone)]
pub struct Prov {
    pub txn: u64,
    pub committed: bool,
    pub aborted: bool,
    pub predecessors: Vec<u64>,
}

/// Definition 3 over an emitted provenance trace: a surviving
/// (committed, non-aborted) operation retaining an aborted predecessor.
pub fn detect_a3(trace: &[Prov]) -> Option<(u64, u64)> {
    for r in trace {
        if r.committed && !r.aborted {
            for p in &r.predecessors {
                if let Some(q) = trace.iter().find(|x| x.txn == *p) {
                    if q.aborted {
                        return Some((r.txn, *p));
                    }
                }
            }
        }
    }
    None
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
    pub abort_at: usize,
}

/// Vary the SHAPE with the seed, not just the payload.
pub fn shape_of(seed: u64, depth: usize) -> Shape {
    let chain = depth + (seed % 3) as usize;
    Shape {
        chain,
        interleave: seed % 2 == 1,
        abort_at: (seed as usize / 2) % chain,
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Outcome {
    pub a3: bool,
    pub cascaded: u64,
    pub refused: u64,
}

/// Guarded arm: the verified runtime.
///
/// Every erased precondition of `L2Runtime` is respected by construction:
/// `read` requires the cell to already exist (`cell_value.contains_key(c)`),
/// `write`/`commit`/`abort` require the transaction to exist and, for
/// `write`, to be uncommitted. Under plain cargo those clauses are erased,
/// so a driver that violates one panics inside the verified file rather
/// than failing a check. The `written` frontier below is what keeps the
/// `read` precondition true when a commit is refused and its cell is
/// therefore never created.
pub fn run_guarded(seed: u64, depth: usize) -> Outcome {
    let s = shape_of(seed, depth);
    let base = 1_000 + (seed % 11) * 100;
    let mut rt = L2Runtime::new();
    let mut refused = 0u64;

    let root = rt.begin();
    rt.write(root, base, 40 + seed % 5);
    if !rt.can_commit(root) {
        return Outcome { a3: false, cascaded: 0, refused: 1 };
    }
    rt.commit(root);

    // Cells known to exist. `read` may only target one of these.
    let mut written: Vec<u64> = vec![base];
    let mut committed: Vec<u64> = vec![root];
    let mut next_cell = base + 1;

    for k in 0..s.chain {
        let rc = written[written.len() - 1];
        let wc = next_cell;
        let t = rt.begin();
        rt.read(t, rc);
        rt.write(t, wc, 70 + k as u64);

        // Adversarial interleave: a concurrent writer lands on the cell
        // t has already read, inside t's read-to-commit window, so t's
        // read set goes stale and commit_gate must refuse.
        if s.interleave && k % 2 == 0 {
            let c = rt.begin();
            rt.write(c, rc, 900 + k as u64);
            if rt.can_commit(c) {
                rt.commit(c);
                committed.push(c);
            }
        }

        if rt.can_commit(t) {
            rt.commit(t);
            committed.push(t);
            written.push(wc);
            next_cell += 1;
        } else {
            refused += 1;
            rt.abort(t);
        }
    }

    let victim = committed[s.abort_at % committed.len()];
    rt.abort(victim);

    let mut trace = Vec::new();
    let mut cascaded = 0u64;
    for id in 0..rt.next_txn {
        if let Some(x) = rt.txns.get(&id) {
            if x.aborted && id != victim {
                cascaded += 1;
            }
            trace.push(Prov {
                txn: id,
                committed: x.committed,
                aborted: x.aborted,
                predecessors: x.predecessors.clone(),
            });
        }
    }

    Outcome { a3: detect_a3(&trace).is_some(), cascaded, refused }
}

/// Unguarded arm: a real second execution on the SAME schedule.
pub fn run_unguarded(seed: u64, depth: usize) -> Outcome {
    let s = shape_of(seed, depth);
    let base = 1_000 + (seed % 11) * 100;
    let mut st = UnguardedStore::new();
    let mut refused = 0u64;

    let root = st.begin();
    if !st.commit(root, &[(base, 40 + seed % 5)]) {
        return Outcome { a3: false, cascaded: 0, refused: 1 };
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

    let victim = committed[s.abort_at % committed.len()];
    st.abort(victim);

    let trace: Vec<Prov> = st
        .txns
        .iter()
        .enumerate()
        .map(|(i, x)| Prov {
            txn: i as u64,
            committed: x.committed,
            aborted: x.aborted,
            predecessors: x.predecessors.clone(),
        })
        .collect();

    Outcome { a3: detect_a3(&trace).is_some(), cascaded: 0, refused }
}

pub struct Summary {
    pub runs: u32,
    pub depth: usize,
    pub guarded: bool,
    pub a3_hits: u32,
    pub cascaded: u64,
    pub refused: u64,
}

pub fn run_experiment(runs: u32, depth: usize, guarded: bool) -> Summary {
    let mut s = Summary { runs, depth, guarded, a3_hits: 0, cascaded: 0, refused: 0 };
    for i in 0..runs as u64 {
        let seed = i.wrapping_mul(2_654_435_761) ^ (i << 7);
        let o = if guarded { run_guarded(seed, depth) } else { run_unguarded(seed, depth) };
        if o.a3 {
            s.a3_hits += 1;
        }
        s.cascaded += o.cascaded;
        s.refused += o.refused;
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verified_runtime_prevents_a3_at_every_depth() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, true);
            assert_eq!(s.a3_hits, 0, "verified L2 runtime admitted A3 at depth {depth}");
        }
    }

    #[test]
    fn unguarded_baseline_exhibits_a3_but_not_vacuously() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, false);
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
        let s = run_experiment(1000, 3, true);
        assert!(
            s.refused > 0,
            "commit_gate refused nothing in 1000 scenarios; its refusal path is untested \
             and the measurement cannot distinguish it from a gate with no check at all"
        );
    }

    /// The B4 regression test. A transaction reads a cell, another
    /// transaction overwrites it, and the reader also WRITES that cell.
    /// commit_valid forbids the commit; the superseded carve-out gate
    /// allows it. If this ever stops failing to disagree, the defect is
    /// back.
    #[test]
    fn carve_out_gate_is_weaker_than_commit_valid() {
        let mut rt = L2Runtime::new();
        let a = rt.begin();
        rt.write(a, 1, 10);
        assert!(rt.can_commit(a));
        rt.commit(a);

        let b = rt.begin();
        rt.read(b, 1);
        rt.write(b, 1, 11);

        let c = rt.begin();
        rt.write(c, 1, 99);
        assert!(rt.can_commit(c));
        rt.commit(c);

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
