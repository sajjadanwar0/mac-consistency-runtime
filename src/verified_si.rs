//! verified_si.rs -- SI commit validation routed through the actual
//! Verus-verified gate.
//!
//! This calls `crate::lib_si_validate_exec::validate` directly -- the literal
//! exec function proven SOUND and COMPLETE against snapshot freshness
//! (lib_si_validate_exec.rs: 5 verified, 0 errors, no assume/admit/external_body).
//! There is no hand-copied projection: the function that decides commit-vs-abort
//! at runtime IS the proven one.
//!
//! `validate_fresh` is the faithful marshalling wrapper: it flattens the
//! deployed BTreeMap<Cell, Vec<(Time,Value)>> version map into the flat
//! Vec<(cell, time, value)> the verified gate consumes, and interns cell/value
//! Strings to usize. The result is a single boolean -- true iff no read-set
//! cell has a version committed after `read_time` -- bit-identical to the
//! original `SnapshotIsolationStore::validate`.
//!
//! Residual (stated, not hidden): the version-map flatten, string interning
//! (axiom_string_to_int_injective), and the parking_lot::Mutex critical section
//! (a RustBelt-class lock, weak-memory-bounded by the GenMC/RC11 check). The
//! validation LOGIC itself is no longer trusted -- it is the verified gate.

use std::collections::{BTreeMap, HashMap};

use crate::lib_si_validate_exec::validate as verified_validate;
use crate::oprecord::{CellId, Time, Value};

/// Consistent per-call string->usize interning. Equal ids iff equal strings.
struct Interner {
    to_id: HashMap<String, usize>,
}

impl Interner {
    fn new() -> Self {
        Self { to_id: HashMap::new() }
    }

    fn id(&mut self, s: &str) -> usize {
        if let Some(&i) = self.to_id.get(s) {
            return i;
        }
        let i = self.to_id.len();
        self.to_id.insert(s.to_string(), i);
        i
    }
}

/// Validate a snapshot's read set against the version map, through the verified
/// gate. Returns true iff the snapshot is fresh: no read-set cell has a version
/// committed after `read_time`. Bit-identical to the original hand-written
/// `validate`, but the decision is now the exec-verified function.
pub fn validate_fresh(
    versions: &BTreeMap<CellId, Vec<(Time, Value)>>,
    read_set: &[CellId],
    read_time: Time,
) -> bool {
    let mut intern = Interner::new();

    // Flatten the version map: one (cell_id, commit_time, value_id) per version.
    let mut flat: Vec<(usize, u64, usize)> = Vec::new();
    for (cell, chain) in versions.iter() {
        let cid = intern.id(cell);
        for (ct, v) in chain {
            flat.push((cid, *ct, intern.id(v)));
        }
    }
    // Intern the read set with the SAME interner so cell ids line up.
    let rs: Vec<usize> = read_set.iter().map(|c| intern.id(c)).collect();

    // The actual exec-verified gate. Sound + complete vs freshness by the
    // Verus proof; only the marshalling above is unverified.
    verified_validate(&flat, &rs, read_time)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chain(items: &[(u64, &str)]) -> Vec<(Time, Value)> {
        items.iter().map(|(t, v)| (*t, v.to_string())).collect()
    }

    #[test]
    fn fresh_when_all_versions_at_or_before_read_time() {
        let mut vs: BTreeMap<CellId, Vec<(Time, Value)>> = BTreeMap::new();
        vs.insert("ticket".to_string(), chain(&[(1, "v0")]));
        assert!(validate_fresh(&vs, &["ticket".to_string()], 1));
    }

    #[test]
    fn stale_when_read_set_cell_has_newer_version() {
        let mut vs: BTreeMap<CellId, Vec<(Time, Value)>> = BTreeMap::new();
        vs.insert("ticket".to_string(), chain(&[(1, "v0"), (2, "v1")]));
        assert!(!validate_fresh(&vs, &["ticket".to_string()], 1));
    }

    #[test]
    fn newer_version_on_unread_cell_is_irrelevant() {
        let mut vs: BTreeMap<CellId, Vec<(Time, Value)>> = BTreeMap::new();
        vs.insert("other".to_string(), chain(&[(2, "x")]));
        assert!(validate_fresh(&vs, &["ticket".to_string()], 1));
    }
}