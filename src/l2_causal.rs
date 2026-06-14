use std::collections::{BTreeMap, BTreeSet};

pub type TxnId = u64;
pub type CellId = String;
pub type Value = String;
pub type Time = u64;

pub const NULL: &str = "NULL";

#[derive(Clone, Debug)]
struct TxnRec {
    txn: TxnId,
    agent: String,
    read_set: Vec<CellId>,
    read_values: BTreeMap<CellId, Value>,
    read_time: Time,
    write_set: Vec<CellId>,
    write_values: BTreeMap<CellId, Value>,
    write_time: Time,
    predecessors: BTreeSet<TxnId>,
    committed: bool,
    aborted: bool,
}

#[derive(Clone, Debug)]
pub struct ProvRecord {
    pub txn: TxnId,
    pub agent: String,
    pub read_set: Vec<CellId>,
    pub read_values: BTreeMap<CellId, Value>,
    pub read_time: Time,
    pub write_set: Vec<CellId>,
    pub write_values: BTreeMap<CellId, Value>,
    pub write_time: Time,
    pub preds: Vec<TxnId>,
    pub aborted: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbortPolicy {
    Cascade,
    NoCascade,
}

#[derive(Clone, Copy, Debug)]
pub struct BeginToken {
    pub txn: TxnId,
}

pub struct L2CausalStore {
    clock: Time,
    next_txn: TxnId,
    cell_value: BTreeMap<CellId, Value>,
    cell_producer: BTreeMap<CellId, TxnId>,
    txns: BTreeMap<TxnId, TxnRec>,
    policy: AbortPolicy,
    cascade_aborts: u64,
    rejected_commits: u64,
}

impl L2CausalStore {
    pub fn new(policy: AbortPolicy) -> Self {
        L2CausalStore {
            clock: 0,
            next_txn: 0,
            cell_value: BTreeMap::new(),
            cell_producer: BTreeMap::new(),
            txns: BTreeMap::new(),
            policy,
            cascade_aborts: 0,
            rejected_commits: 0,
        }
    }
    
    pub fn begin(&mut self, agent: &str, cells: &[CellId]) -> BeginToken {
        let txn = self.next_txn;
        self.next_txn += 1;
        let read_time = self.clock;

        let mut read_values = BTreeMap::new();
        let mut preds: BTreeSet<TxnId> = BTreeSet::new();
        
        for c in cells {
            let v = self
                .cell_value
                .get(c)
                .cloned()
                .unwrap_or_else(|| NULL.to_string());
            read_values.insert(c.clone(), v);
        
            if let Some(p) = self.cell_producer.get(c).copied() {
                preds.insert(p);
                if let Some(prec) = self.txns.get(&p) {
                    for q in &prec.predecessors {
                        preds.insert(*q);
                    }
                }
            }
        }

        self.txns.insert(
            txn,
            TxnRec {
                txn,
                agent: agent.to_string(),
                read_set: cells.to_vec(),
                read_values,
                read_time,
                write_set: Vec::new(),
                write_values: BTreeMap::new(),
                write_time: 0,
                predecessors: preds,
                committed: false,
                aborted: false,
            },
        );
        BeginToken { txn }
    }
    
    fn commit_valid(&self, txn: TxnId, writes: &BTreeMap<CellId, Value>) -> bool {
        let t = match self.txns.get(&txn) {
            Some(t) => t,
            None => return false,
        };
        
        for c in &t.read_set {
            if writes.contains_key(c) {
                continue; 
            }
        
            let cur = self.cell_value.get(c).map(|v| v.as_str()).unwrap_or(NULL);
            let obs = t.read_values.get(c).map(|v| v.as_str()).unwrap_or(NULL);
        
            if cur != obs {
                return false; 
            }
        }
        
        for p in &t.predecessors {
            match self.txns.get(p) {
                Some(pr) if pr.committed && !pr.aborted => {}
                _ => return false, 
            }
        }
        true
    }

    pub fn commit(&mut self, tok: BeginToken, writes: &BTreeMap<CellId, Value>) -> bool {
        let txn = tok.txn;
        
        if !self.commit_valid(txn, writes) {
            self.rejected_commits += 1;
            if let Some(t) = self.txns.get_mut(&txn) {
                t.aborted = true;
            }
            return false;
        }
        
        self.clock += 1;
        
        let wt = self.clock;
        
        for (c, v) in writes {
            self.cell_value.insert(c.clone(), v.clone());
            self.cell_producer.insert(c.clone(), txn);
        }
        
        let t = self.txns.get_mut(&txn).unwrap();
        
        t.write_set = writes.keys().cloned().collect();
        t.write_values = writes.clone();
        t.write_time = wt;
        t.committed = true;
        true
    }

    pub fn abort(&mut self, txn: TxnId) {
        if let Some(t) = self.txns.get_mut(&txn) {
            t.aborted = true;
        }
        if self.policy == AbortPolicy::Cascade {
            let victims: Vec<TxnId> = self
                .txns
                .values()
                .filter(|u| !u.aborted && u.predecessors.contains(&txn))
                .map(|u| u.txn)
                .collect();
            for v in victims {
                if let Some(u) = self.txns.get_mut(&v) {
                    u.aborted = true;
                }
                self.cascade_aborts += 1;
            }
        }
    }

    pub fn trace(&self) -> Vec<ProvRecord> {
        self.txns
            .values()
            .map(|t| ProvRecord {
                txn: t.txn,
                agent: t.agent.clone(),
                read_set: t.read_set.clone(),
                read_values: t.read_values.clone(),
                read_time: t.read_time,
                write_set: t.write_set.clone(),
                write_values: t.write_values.clone(),
                write_time: t.write_time,
                preds: t.predecessors.iter().copied().collect(),
                aborted: t.aborted,
            })
            .collect()
    }

    pub fn cascade_aborts(&self) -> u64 {
        self.cascade_aborts
    }
    pub fn rejected_commits(&self) -> u64 {
        self.rejected_commits
    }
}

pub fn detect_a3_cascade(h: &[ProvRecord]) -> Option<(TxnId, TxnId)> {
    let aborted: BTreeSet<TxnId> = h.iter().filter(|r| r.aborted).map(|r| r.txn).collect();
    for r in h {
        if r.aborted {
            continue;
        }
        for p in &r.preds {
            if aborted.contains(p) {
                return Some((r.txn, *p));
            }
        }
    }
    None
}

#[derive(Clone, Debug)]
pub struct ExperimentResult {
    pub policy: AbortPolicy,
    pub runs: u32,
    pub depth: usize,
    pub a3_positive: u32,
    pub cascade_aborts_total: u64,
}

impl ExperimentResult {
    pub fn a3_rate(&self) -> f64 {
        self.a3_positive as f64 / self.runs as f64
    }
}

pub fn run_one(seed: u64, depth: usize, policy: AbortPolicy) -> (bool, u64) {
    assert!(depth >= 2, "need a root plus at least one dependent");
    let mut st = L2CausalStore::new(policy);

    let root = st.begin("a0", &[]);
    let root_txn = root.txn;
    let mut w0 = BTreeMap::new();
    w0.insert("c0".to_string(), format!("v{}", seed % 7));
    st.commit(root, &w0);

    let mut prev = "c0".to_string();
    
    for i in 1..depth {
        let cell = format!("c{}", i);
        let tok = st.begin(&format!("a{}", i), std::slice::from_ref(&prev));
        let mut w = BTreeMap::new();
        w.insert(cell.clone(), format!("v{}_{}", i, seed % 5));
        st.commit(tok, &w);
        prev = cell;
    }

    st.abort(root_txn);

    let tr = st.trace();
    (detect_a3_cascade(&tr).is_some(), st.cascade_aborts())
}

pub fn run_experiment(runs: u32, depth: usize, policy: AbortPolicy) -> ExperimentResult {
    let mut a3_positive = 0u32;
    let mut cascade_aborts_total = 0u64;
    
    for s in 0..runs as u64 {
        let seed = s.wrapping_mul(2_654_435_761);
        let (pos, casc) = run_one(seed, depth, policy);
        if pos {
            a3_positive += 1;
        }
        cascade_aborts_total += casc;
    }
    
    ExperimentResult {
        policy,
        runs,
        depth,
        a3_positive,
        cascade_aborts_total,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn baseline_admits_a3_l2_prevents_it() {
        let (base_pos, _) = run_one(1, 2, AbortPolicy::NoCascade);
        let (l2_pos, casc) = run_one(1, 2, AbortPolicy::Cascade);
        assert!(base_pos, "unguarded baseline must leave an A3 witness");
        assert!(!l2_pos, "L2 cascade must prevent A3");
        assert!(casc >= 1, "L2 must have cascaded at least one abort");
    }

    #[test]
    fn l2_prevents_transitive_cascade() {
        let (l2_pos, casc) = run_one(42, 4, AbortPolicy::Cascade);
        assert!(!l2_pos, "L2 must prevent A3 along the whole chain");
        assert!(casc >= 3, "depth-4 chain should cascade 3 dependents");
    }

    #[test]
    fn measure_a3_prevention() {
        let runs = 1000;
        
        for depth in [2usize, 3, 5] {
            let base = run_experiment(runs, depth, AbortPolicy::NoCascade);
            let l2 = run_experiment(runs, depth, AbortPolicy::Cascade);
        
            println!(
                "depth={}  baseline A3 = {}/{} ({:.0}%)   L2 A3 = {}/{} ({:.0}%)   L2 cascade-aborts = {}",
                depth,
                base.a3_positive,
                base.runs,
                base.a3_rate() * 100.0,
                l2.a3_positive,
                l2.runs,
                l2.a3_rate() * 100.0,
                l2.cascade_aborts_total,
            );
            assert_eq!(base.a3_positive, runs, "baseline should always admit A3");
            assert_eq!(l2.a3_positive, 0, "L2 should always prevent A3");
        }
    }
}