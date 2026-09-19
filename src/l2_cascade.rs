//! l2_cascade.rs -- the SUPERSEDED L2 design, kept as a measured arm.
//!
//! Rounds <= 22 of this development called a runtime "L2" when it tracked
//! causal predecessors, refused to commit on an aborted one, and CASCADED an
//! abort to every dependent -- while releasing each transaction's effects at
//! commit. That design satisfies the overruled A3 (no surviving dependent of
//! an aborted operation) and prevents nothing: the dependents it flags have
//! already released their effects. The flag moves; the effect does not.
//!
//! 2026-09-19 round 33: this store exists so the MEASUREMENT can show that,
//! not only the model (R5 in lib_a3_residue.rs, and the three literal
//! histories TLC discriminates). Before this round the L2 measurement had two
//! arms, and on both of them the overruled predicate and the current one gave
//! the same count in every cell (519/519, 624/624, 563/563; 0/0), so the
//! measurement could not tell the two definitions apart and carried no
//! evidence that the change of definition in rounds 23-28 mattered.
//!
//! It is ordinary Rust: no vstd, no proofs, no invariant, NO safety claim.
//! It cannot be built on `l2_exec::L2Runtime`, because the verified runtime
//! refuses the one thing this design does -- retract an operation whose
//! effects are out (`abort_valid`). It is therefore a second baseline, not a
//! second implementation of L2.
//!
//! It WRAPS `l2_unguarded::UnguardedStore` rather than copying it, so the two
//! release-at-commit arms share begin, read, read validation, the write path
//! and the release point byte for byte, and differ in exactly two places:
//!   1. `commit` refuses when an operation in the causal closure is aborted;
//!   2. `abort` cascades to every operation whose closure holds the aborted one.
//! OVERRULED (rounds <= 22): (1) and (2) together were the L2 discipline.

use std::collections::BTreeSet;

use crate::l2_unguarded::UnguardedStore;

#[derive(Default)]
pub struct CascadeStore {
    pub inner: UnguardedStore,
}

impl CascadeStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn begin(&mut self) -> u64 {
        self.inner.begin()
    }

    /// Read a cell, acquiring its writer as a causal predecessor.
    pub fn read(&mut self, t: u64, c: u64) {
        self.inner.read(t, c)
    }

    /// Every operation reachable from `t` through recorded predecessors. The
    /// inner store records direct writers only, so the closure is taken here.
    pub fn closure(&self, t: u64) -> BTreeSet<u64> {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<u64> = match self.inner.txns.get(t as usize) {
            Some(x) => x.predecessors.clone(),
            None => Vec::new(),
        };
        while let Some(p) = stack.pop() {
            if seen.insert(p) {
                if let Some(q) = self.inner.txns.get(p as usize) {
                    stack.extend(q.predecessors.iter().copied());
                }
            }
        }
        seen
    }

    /// No operation in `t`'s causal closure is aborted.
    pub fn closure_clean(&self, t: u64) -> bool {
        self.closure(t)
            .iter()
            .all(|p| self.inner.txns.get(*p as usize).map_or(false, |q| !q.aborted))
    }

    /// Difference 1: refuse to commit on an aborted basis; otherwise the inner
    /// store's commit, which validates reads and RELEASES AT COMMIT.
    pub fn commit(&mut self, t: u64, writes: &[(u64, u64)]) -> bool {
        if !self.closure_clean(t) {
            return false;
        }
        self.inner.commit(t, writes)
    }

    /// Difference 2: abort and cascade. Flags `t` and every operation whose
    /// causal closure holds `t` -- released or not, which is the whole defect.
    /// Returns how many OTHER operations the cascade flagged.
    pub fn abort(&mut self, t: u64) -> u64 {
        let dependents: Vec<u64> = (0..self.inner.txns.len() as u64)
            .filter(|i| *i != t && self.closure(*i).contains(&t))
            .collect();
        self.inner.abort(t);
        let mut flagged = 0u64;
        for i in dependents {
            if !self.inner.txns[i as usize].aborted {
                self.inner.txns[i as usize].aborted = true;
                flagged += 1;
            }
        }
        flagged
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// root -> a -> b, all committed; retracting the root flags both
    /// dependents, and both had already released at commit.
    #[test]
    fn the_cascade_flags_transitive_dependents_after_their_effects_are_out() {
        let mut st = CascadeStore::new();
        let root = st.begin();
        assert!(st.commit(root, &[(1, 10)]));
        let a = st.begin();
        st.read(a, 1);
        assert!(st.commit(a, &[(2, 20)]));
        let b = st.begin();
        st.read(b, 2);
        assert!(st.commit(b, &[(3, 30)]));
        assert!(st.inner.txns[a as usize].externalized && st.inner.txns[b as usize].externalized,
                "this design releases at commit");
        assert_eq!(st.abort(root), 2, "the cascade must reach the transitive dependent");
        for t in [root, a, b] {
            let x = &st.inner.txns[t as usize];
            assert!(x.aborted, "operation {t} was not flagged");
            assert!(x.externalized, "the flag must not un-release anything: that is the defect this arm exhibits");
        }
    }

    /// A reader of a retracted writer's value cannot commit. The inner store
    /// does not roll the value back, so the gate is what stops it.
    #[test]
    fn a_reader_of_a_retracted_writer_cannot_commit() {
        let mut st = CascadeStore::new();
        let w = st.begin();
        assert!(st.commit(w, &[(1, 10)]));
        assert_eq!(st.abort(w), 0);
        let r = st.begin();
        st.read(r, 1);
        assert!(!st.commit(r, &[(2, 20)]), "committed on an aborted basis");
        // the unguarded baseline accepts exactly this commit
        let mut un = UnguardedStore::new();
        let w = un.begin();
        assert!(un.commit(w, &[(1, 10)]));
        un.abort(w);
        let r = un.begin();
        un.read(r, 1);
        assert!(un.commit(r, &[(2, 20)]), "the two baselines must differ here");
    }

    /// With no abort anywhere the two release-at-commit stores are the same
    /// store: same decisions, same state.
    #[test]
    fn without_an_abort_the_two_baselines_are_indistinguishable() {
        let mut ca = CascadeStore::new();
        let mut un = UnguardedStore::new();
        let (r1, r2) = (ca.begin(), un.begin());
        assert_eq!(ca.commit(r1, &[(1, 10)]), un.commit(r2, &[(1, 10)]));
        let (a1, a2) = (ca.begin(), un.begin());
        ca.read(a1, 1);
        un.read(a2, 1);
        // a concurrent writer makes the read stale in both
        let (c1, c2) = (ca.begin(), un.begin());
        assert_eq!(ca.commit(c1, &[(1, 99)]), un.commit(c2, &[(1, 99)]));
        assert_eq!(ca.commit(a1, &[(2, 20)]), un.commit(a2, &[(2, 20)]));
        assert!(!ca.inner.txns[a1 as usize].committed, "stale read must be refused");
        assert_eq!(ca.inner.cell_value, un.cell_value);
        assert_eq!(ca.inner.cell_writer, un.cell_writer);
    }
}
