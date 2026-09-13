//! l2_measure.rs -- measure A3 prevention through the VERIFIED runtime.
//!
//! Section 5.11's numbers were previously produced by `l2_causal.rs`,
//! whose commit check skipped freshness for every cell a transaction
//! writes and carried none of the model's self-guards.  The model's
//! `commit_valid` has no such carve-out, so the measured artifact was
//! strictly weaker than the verified one and Table 1's "L2 verified, run
//! live" fused two different artifacts into one cell.
//!
//! Here the guarded arm is `crate::l2_exec::L2Runtime` -- the same bytes
//! Verus checks, with the proofs erased by the `verus!` macro, exactly as
//! `si_concurrent.rs` is at L1.  The unguarded arm is an ordinary Rust
//! baseline that aborts the root without cascading; it carries no safety
//! claim and exists only to exhibit what the discipline removes.
//!
//! THE ONE UNVERIFIED PIECE, NAMED.
//! `L2Runtime::commit` takes `commit_valid(view, t)` as a precondition
//! and the crate ships no verified decision procedure for it.  Plain
//! cargo erases preconditions, so a caller that ignores it would run
//! outside the theorem.  `commit_gate` below transcribes `commit_valid`
//! conjunct for conjunct, with no carve-out, and the driver refuses the
//! commit when it is false -- so every `commit` this measurement issues
//! satisfies the precondition.  `commit_gate` is NOT verified.  Proving
//! it sound and complete against `commit_valid`, the way
//! `lib_si_concurrent.rs::validate` is proved against `fresh`, is the
//! remaining step; until then the guarantee covers this measurement
//! because the gate holds at every call site, not because the gate is
//! checked.
//!
//! `commit_gate` reads the transaction's cells from the caller's own
//! list rather than from `read_set`, because vstd's `HashSetWithView`
//! exposes no iterator.  The two coincide by construction: `read` is the
//! only path by which a cell enters `read_set`, and the driver records
//! exactly the cells it passed to `read`.  Stated, not hidden.

use crate::l2_exec::L2Runtime;

/// One emitted provenance record, the shape `detect_a3_cascade` scores.
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

/// A conjunct-for-conjunct transcription of
/// `lib_l2_exec.rs::commit_valid`.  UNVERIFIED -- see the module header.
///
///   commit_valid(s,t) == s.txns.contains_key(t)
///                     && s.txns[t].started
///                     && !s.txns[t].committed
///                     && !s.txns[t].aborted
///                     && reads_fresh(s,t)
///                     && predecessors_clean(s,t)
///
/// `cells` is the caller's record of every cell passed to `read` for `t`.
/// No cell is skipped for any reason; in particular a cell the
/// transaction also writes is checked like any other.
pub fn commit_gate(rt: &L2Runtime, t: u64, cells: &[u64]) -> bool {
    let txn = match rt.txns.get(&t) {
        Some(x) => x,
        None => return false, // s.txns.contains_key(t)
    };
    if !txn.started || txn.committed || txn.aborted {
        return false; // started && !committed && !aborted
    }
    // reads_fresh: every read cell still holds the value that was read.
    for c in cells {
        let observed = match txn.read_values.get(c) {
            Some(v) => *v,
            None => return false,
        };
        match rt.cell_value.get(c) {
            Some(current) if *current == observed => {}
            _ => return false,
        }
    }
    // predecessors_clean: every predecessor committed and not aborted.
    for p in &txn.predecessors {
        match rt.txns.get(p) {
            Some(q) if q.committed && !q.aborted => {}
            _ => return false,
        }
    }
    true
}

/// Outcome of one scenario.
#[derive(Debug, Clone, Copy)]
pub struct Outcome {
    pub a3: bool,
    pub cascaded: u64,
    pub refused: u64,
}

/// Build a causal chain of `depth` dependents on one root, commit them,
/// then abort the root.
///
/// `guarded = true` drives the verified `L2Runtime`, whose `abort`
/// cascades.  `guarded = false` is the L1-class baseline: the same
/// schedule with the root's abort applied to the root alone.
pub fn run_one(seed: u64, depth: usize, guarded: bool) -> Outcome {
    let cell_base = 1_000 + (seed % 7) * 100;
    let mut rt = L2Runtime::new();

    // Root writes cell_base.
    let root = rt.begin();
    rt.write(root, cell_base, 40 + (seed % 5));
    let root_cells: Vec<u64> = Vec::new();
    if !commit_gate(&rt, root, &root_cells) {
        return Outcome { a3: false, cascaded: 0, refused: 1 };
    }
    rt.commit(root);

    // A chain of dependents: each reads the previous cell, writes the next.
    let mut chain: Vec<u64> = Vec::new();
    let mut refused = 0u64;
    for k in 0..depth {
        let t = rt.begin();
        let rc = cell_base + k as u64;
        rt.read(t, rc);
        rt.write(t, cell_base + k as u64 + 1, 70 + k as u64);
        let cells = vec![rc];
        if commit_gate(&rt, t, &cells) {
            rt.commit(t);
            chain.push(t);
        } else {
            refused += 1;
            rt.abort(t);
        }
    }

    // Saga compensation: the root is retracted.
    rt.abort(root);

    // Emit the provenance trace by id -- keys are 0..next_txn
    // (L2Runtime::keys_contiguous), and vstd's HashMapWithView has no
    // iterator, so we scan the range rather than the map.
    let mut trace: Vec<Prov> = Vec::new();
    let mut cascaded = 0u64;
    for id in 0..rt.next_txn {
        if let Some(x) = rt.txns.get(&id) {
            let aborted = if guarded {
                x.aborted
            } else {
                // Unguarded baseline: only the root is retracted; the
                // cascade is not applied to its dependents.
                id == root
            };
            if guarded && x.aborted && id != root {
                cascaded += 1;
            }
            trace.push(Prov {
                txn: id,
                committed: x.committed,
                aborted,
                predecessors: x.predecessors.clone(),
            });
        }
    }

    Outcome {
        a3: detect_a3(&trace).is_some(),
        cascaded,
        refused,
    }
}

/// Aggregate over `runs` independent scenarios at one depth.
pub struct Summary {
    pub runs: u32,
    pub depth: usize,
    pub guarded: bool,
    pub a3_hits: u32,
    pub cascaded: u64,
    pub refused: u64,
}

pub fn run_experiment(runs: u32, depth: usize, guarded: bool) -> Summary {
    let mut s = Summary {
        runs,
        depth,
        guarded,
        a3_hits: 0,
        cascaded: 0,
        refused: 0,
    };
    for seed in 0..runs as u64 {
        let o = run_one(seed, depth, guarded);
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
    fn guarded_prevents_a3_at_every_depth() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, true);
            assert_eq!(
                s.a3_hits, 0,
                "verified L2 runtime admitted A3 at depth {depth}"
            );
        }
    }

    #[test]
    fn unguarded_baseline_exhibits_a3_at_every_depth() {
        for depth in [2usize, 3, 5] {
            let s = run_experiment(1000, depth, false);
            assert_eq!(
                s.a3_hits, 1000,
                "unguarded baseline failed to exhibit A3 at depth {depth}; \
                 a prevention result against a baseline that does not fail is vacuous"
            );
        }
    }

    #[test]
    fn commit_gate_has_no_write_set_carve_out() {
        // A transaction that reads a cell and then writes the same cell
        // must still be checked for freshness on that cell.  The twin
        // skipped exactly this case.
        let mut rt = L2Runtime::new();
        let a = rt.begin();
        rt.write(a, 1, 10);
        assert!(commit_gate(&rt, a, &[]));
        rt.commit(a);

        let b = rt.begin();
        rt.read(b, 1);
        rt.write(b, 1, 11);

        let c = rt.begin();
        rt.write(c, 1, 99);
        assert!(commit_gate(&rt, c, &[]));
        rt.commit(c);

        // b read cell 1 as 10; it is now 99.  b also WRITES cell 1, which
        // is the case the twin skipped.  The gate must refuse.
        assert!(
            !commit_gate(&rt, b, &[1]),
            "commit_gate accepted a stale read of a cell the transaction writes"
        );
    }
}
