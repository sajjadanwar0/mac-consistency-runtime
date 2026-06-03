// lib_si_validate_exec.rs
//
// Verified EXEC-mode SI commit-validation. This is the enforcement check from
// mac-consistency-runtime/src/snapshot_isolation.rs::validate, written as a
// Verus `exec fn` and proven SOUND and COMPLETE against the snapshot-freshness
// predicate. `validate` is the gate that makes an SI commit safe: a commit is
// admitted only if no version of any read-set cell was committed after the
// transaction's snapshot read_time. A validated commit therefore did not read
// a value that a concurrent transaction has since overwritten -- the A_1
// (stale-generation) guard at the enforcement layer.
//
// CORRESPONDENCE TO THE DEPLOYED CODE (residual, stated not hidden)
//   1. Deployed versions are BTreeMap<Cell, Vec<(Time,Val)>>; here they are a
//      FLAT Vec<(Cell, Time, Val)> with one entry per version. The deployed
//      nested map flattens to exactly this multiset of versions, and the
//      validation condition ("some read-set cell has a version with time >
//      read_time") is identical under the flatten; only iteration order
//      differs, which does not affect the boolean result.
//   2. Cells/values are integers; deployed uses interned Strings
//      (axiom_string_to_int_injective).
//   3. The surrounding critical section uses parking_lot::Mutex, a trusted
//      acquire/release lock of the same class as std::sync::Mutex; its
//      weak-memory soundness is the bounded GenMC/RC11 result, and its
//      correspondence is RustBelt's verified Mutex.
//   The validation LOGIC -- the scan and the time-window test -- is the
//   deployed `validate`, now mechanically tied to the freshness predicate.
//
// NO axiom, NO assume, NO admit, NO external_body in this file.

use vstd::prelude::*;

verus! {

pub type Cell = usize;
pub type Val = usize;

// =====================================================================
// Spec layer: snapshot freshness
// =====================================================================

pub open spec fn in_set(rs: Seq<Cell>, c: Cell) -> bool {
    exists|i: int| 0 <= i < rs.len() && rs[i] == c
}

/// The snapshot is fresh for `rs` at `rt` iff no version of any read-set cell
/// was committed strictly after `rt`. `vs` is the flattened version log:
/// each element is (cell, commit_time, value).
pub open spec fn fresh(vs: Seq<(Cell, u64, Val)>, rs: Seq<Cell>, rt: u64) -> bool {
    forall|k: int|
        0 <= k < vs.len() ==> (in_set(rs, vs[k].0) ==> vs[k].1 <= rt)
}

// =====================================================================
// Verified exec helper: read-set membership
// =====================================================================

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

// =====================================================================
// validate: SOUND + COMPLETE against freshness
// =====================================================================

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
        // Either c is not a read-set cell, or its commit time is <= rt;
        // in both cases the freshness clause holds at index k.
        assert(in_set(rs@, vs@[k as int].0) ==> vs@[k as int].1 <= rt);
        k = k + 1;
    }
    // All versions scanned satisfy the clause => fresh.
    true
}

// =====================================================================
// Interpretation: validated commit did not read a stale value.
// freshness is exactly the SI safety invariant for the read set; this
// lemma restates it in the form used by the L-level argument.
// =====================================================================

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
    // Direct from fresh at index idx, since c is in the read set.
}

} // verus!