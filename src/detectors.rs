//! Anomaly detectors over OpRecord traces.
//!
//! These four functions are the executable counterparts of the Verus-verified
//! detectors in `verus_lib_v3.rs`. They are deliberately written to mirror the
//! Verus `detect_a*` functions so that the equivalence between this code and
//! the verified version can be checked by inspection. The Verus chain proves
//! sound + complete equivalence between these patterns and the corresponding
//! TLA+ predicates.

use crate::oprecord::{CellId, OpRecord, Value};

/// A_1 (stale-generation) witness: (i, j, cell).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct A1Witness {
    pub i: usize,
    pub j: usize,
    pub cell: CellId,
}

/// A_3 (causal-cascade) witness: (j, cell, value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct A3Witness {
    pub j: usize,
    pub cell: CellId,
    pub value: Value,
}

pub const NULL_VALUE: &str = "NULL";

/// Detect A_1: returns the first witness or None.
///
/// Equivalent to the Verus `detect_a1` proven sound + complete in
/// `verus_lib_v3.rs`. A trace satisfies `a1` iff this function returns Some.
pub fn detect_a1(h: &[OpRecord]) -> Option<A1Witness> {
    for i in 0..h.len() {
        for j in 0..h.len() {
            if i == j {
                continue;
            }
            for c in &h[i].read_set {
                if !h[j].writes_cell(c) {
                    continue;
                }
                if !(h[i].read_time < h[j].write_time && h[j].write_time < h[i].write_time) {
                    continue;
                }
                let rv = h[i].first_read_value(c);
                let wv = h[j].first_write_value(c);
                match (rv, wv) {
                    (Some(r), Some(w)) if r != w => {
                        return Some(A1Witness {
                            i,
                            j,
                            cell: c.clone(),
                        });
                    }
                    _ => continue,
                }
            }
        }
    }
    None
}

/// Detect A_2: returns the index of the first witness record or None.
pub fn detect_a2(h: &[OpRecord]) -> Option<usize> {
    for (i, r) in h.iter().enumerate() {
        if let Some(t) = &r.planned_tool {
            let visible = r.tools_visible_at_read.iter().any(|x| x == t);
            let used = r.tools_used.iter().any(|x| x == t);
            if visible && !used {
                return Some(i);
            }
        }
    }
    None
}

/// Detect A_3: returns (j, c, v) of the first witness or None.
pub fn detect_a3(h: &[OpRecord]) -> Option<A3Witness> {
    for (j, rj) in h.iter().enumerate() {
        for c in &rj.read_set {
            let v = match rj.first_read_value(c) {
                Some(v) if v != NULL_VALUE => v,
                _ => continue,
            };
            // Search for an antecedent committed write of c with value v at
            // commit time <= rj.read_time.
            let mut has_antecedent = false;
            for (k, rk) in h.iter().enumerate() {
                if k == j {
                    continue;
                }
                if !rk.writes_cell(c) {
                    continue;
                }
                if rk.write_time > rj.read_time {
                    continue;
                }
                if rk.first_write_value(c) == Some(v) {
                    has_antecedent = true;
                    break;
                }
            }
            if !has_antecedent {
                return Some(A3Witness {
                    j,
                    cell: c.clone(),
                    value: v.clone(),
                });
            }
        }
    }
    None
}

/// Detect A_6: returns the index of the first witness record or None.
pub fn detect_a6(h: &[OpRecord]) -> Option<usize> {
    for (i, r) in h.iter().enumerate() {
        if !r.io.is_empty() && r.io != r.co {
            return Some(i);
        }
    }
    None
}

/// Classify the trace by the highest L_n it satisfies on the chosen chain
/// (L_0 admits A_1; L_1 admits A_3; L_2 admits A_6; L_3 admits A_2;
/// L_4 admits none).
pub fn classify_level(h: &[OpRecord]) -> u8 {
    if detect_a1(h).is_some() {
        return 0;
    }
    if detect_a3(h).is_some() {
        return 1;
    }
    if detect_a6(h).is_some() {
        return 2;
    }
    if detect_a2(h).is_some() {
        return 3;
    }
    4
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn rec(
        agent: &str,
        rs: &[&str],
        rv: &[(&str, &str)],
        rt: u64,
        ws: &[&str],
        wv: &[(&str, &str)],
        wt: u64,
    ) -> OpRecord {
        OpRecord {
            agent: agent.to_string(),
            read_set: rs.iter().map(|s| s.to_string()).collect(),
            read_values: rv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect::<BTreeMap<_, _>>(),
            read_time: rt,
            write_set: ws.iter().map(|s| s.to_string()).collect(),
            write_values: wv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect::<BTreeMap<_, _>>(),
            write_time: wt,
            planned_tool: None,
            tools_used: vec![],
            tools_visible_at_read: vec![],
            io: wv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
            co: wv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        }
    }

    #[test]
    fn smoke_a1_full_witness() {
        let h = vec![
            rec("a", &["c"], &[("c", "NULL")], 0, &["c"], &[("c", "v1")], 2),
            rec("b", &["c"], &[("c", "NULL")], 0, &["c"], &[("c", "v2")], 1),
        ];
        assert!(detect_a1(&h).is_some());
        assert_eq!(classify_level(&h), 0);
    }

    #[test]
    fn smoke_clean_trace_is_l4() {
        let h = vec![rec(
            "a",
            &["c"],
            &[("c", "NULL")],
            0,
            &["c"],
            &[("c", "v")],
            1,
        )];
        assert!(detect_a1(&h).is_none());
        assert!(detect_a2(&h).is_none());
        assert!(detect_a3(&h).is_none());
        assert!(detect_a6(&h).is_none());
        assert_eq!(classify_level(&h), 4);
    }

    /// Reproduce the SI/triage trace shape: reporter writes twice, triager
    /// has stale read with empty write_set, A_1 fires structurally.
    #[test]
    fn si_triage_replication() {
        let h = vec![
            rec("rep", &[], &[], 0, &["t"], &[("t", "v0")], 1),
            rec("rep", &[], &[], 1, &["t"], &[("t", "v1")], 2),
            rec("tri", &["t"], &[("t", "v0")], 1, &[], &[], 3),
        ];
        let w = detect_a1(&h);
        assert!(w.is_some(), "A_1 should fire on the SI/triage shape");
        let w = w.unwrap();
        assert_eq!(w.i, 2);
        assert_eq!(w.j, 1);
    }
}
