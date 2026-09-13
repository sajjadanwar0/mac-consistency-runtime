//! l2_unguarded.rs -- an L1-class store that does NOT cascade.
//!
//! This is the baseline the L2 discipline is measured against.  It is
//! ordinary Rust: no vstd, no proofs, no invariant, and it carries NO
//! safety claim whatsoever, exactly like `vanilla.rs` at L0.  It exists
//! for one reason: a prevention result measured against a baseline that
//! does not actually fail is vacuous, so the baseline has to be a real
//! execution rather than a relabelling of the guarded one.
//!
//! What it does: validates a committing transaction's read set against
//! the current store (so it is L1-class, not L0 -- it prevents A1), and
//! on abort marks only the aborted transaction.  Dependents that read a
//! value the aborted transaction wrote survive with a retracted basis.
//! That surviving-dependent-of-an-aborted-operation condition is
//! Definition 3.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct Txn {
    pub started: bool,
    pub committed: bool,
    pub aborted: bool,
    pub read_cells: Vec<u64>,
    pub read_values: BTreeMap<u64, u64>,
    pub predecessors: Vec<u64>,
}

#[derive(Default)]
pub struct UnguardedStore {
    pub txns: Vec<Txn>,
    pub cell_value: BTreeMap<u64, u64>,
    pub cell_writer: BTreeMap<u64, u64>,
}

impl UnguardedStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn begin(&mut self) -> u64 {
        self.txns.push(Txn {
            started: true,
            committed: false,
            aborted: false,
            read_cells: Vec::new(),
            read_values: BTreeMap::new(),
            predecessors: Vec::new(),
        });
        (self.txns.len() - 1) as u64
    }

    /// Read a cell, acquiring its writer as a causal predecessor.
    pub fn read(&mut self, t: u64, c: u64) {
        let v = self.cell_value.get(&c).copied();
        let w = self.cell_writer.get(&c).copied();
        let txn = &mut self.txns[t as usize];
        if !txn.read_cells.contains(&c) {
            txn.read_cells.push(c);
        }
        if let Some(v) = v {
            txn.read_values.insert(c, v);
        }
        if let Some(w) = w {
            if w != t && !txn.predecessors.contains(&w) {
                txn.predecessors.push(w);
            }
        }
    }

    /// L1-class validation: every read cell must still hold what was read.
    /// No carve-out for cells the transaction also writes -- the baseline
    /// is weaker than L2 by not cascading, not by validating badly.
    pub fn reads_fresh(&self, t: u64) -> bool {
        let txn = &self.txns[t as usize];
        txn.read_cells.iter().all(|c| {
            matches!(
                (self.cell_value.get(c), txn.read_values.get(c)),
                (Some(cur), Some(obs)) if cur == obs
            )
        })
    }

    /// Commit if the read set is fresh. Returns false when refused.
    pub fn commit(&mut self, t: u64, writes: &[(u64, u64)]) -> bool {
        {
            let txn = &self.txns[t as usize];
            if !txn.started || txn.committed || txn.aborted {
                return false;
            }
        }
        if !self.reads_fresh(t) {
            return false;
        }
        for (c, v) in writes {
            self.cell_value.insert(*c, *v);
            self.cell_writer.insert(*c, t);
        }
        self.txns[t as usize].committed = true;
        true
    }

    /// Abort WITHOUT cascading. This is the whole difference from L2.
    pub fn abort(&mut self, t: u64) {
        self.txns[t as usize].aborted = true;
    }
}
