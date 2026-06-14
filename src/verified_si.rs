use std::collections::{BTreeMap, HashMap};

use crate::lib_si_validate_exec::validate as verified_validate;
use crate::oprecord::{CellId, Time, Value};

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

pub fn validate_fresh(
    versions: &BTreeMap<CellId, Vec<(Time, Value)>>,
    read_set: &[CellId],
    read_time: Time,
) -> bool {
    let mut intern = Interner::new();

    let mut flat: Vec<(usize, u64, usize)> = Vec::new();

    for (cell, chain) in versions.iter() {
        let cid = intern.id(cell);
        for (ct, v) in chain {
            flat.push((cid, *ct, intern.id(v)));
        }
    }

    let rs: Vec<usize> = read_set.iter().map(|c| intern.id(c)).collect();

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