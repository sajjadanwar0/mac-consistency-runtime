//! Faithful mock of l2_exec::L2Runtime: same public API, and every
//! erased `requires` clause from lib_l2_exec.rs enforced as a runtime
//! assertion, so a driver that violates one fails here loudly instead of
//! panicking inside the verified file under plain cargo.
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct ExecTxn {
    pub started: bool, pub committed: bool, pub aborted: bool,
    pub read_set: Vec<u64>,
    pub read_values: BTreeMap<u64, u64>,
    pub writes: Vec<(u64, u64)>,
    pub predecessors: Vec<u64>,
    pub commit_time: u64,
}
#[derive(Default)]
pub struct Map(pub BTreeMap<u64, ExecTxn>);
impl Map { pub fn get(&self, k: &u64) -> Option<&ExecTxn> { self.0.get(k) } }
#[derive(Default)]
pub struct VMap(pub BTreeMap<u64, u64>);
impl VMap { pub fn get(&self, k: &u64) -> Option<&u64> { self.0.get(k) } }

#[derive(Default)]
pub struct L2Runtime {
    pub now: u64,
    pub txns: Map,
    pub cell_value: VMap,
    pub cell_writer: VMap,
    pub next_txn: u64,
}

impl L2Runtime {
    pub fn new() -> Self { Self::default() }

    pub fn begin(&mut self) -> u64 {
        let t = self.next_txn;
        self.txns.0.insert(t, ExecTxn { started: true, ..Default::default() });
        self.next_txn += 1; self.now += 1; t
    }

    pub fn read(&mut self, t: u64, c: u64) {
        assert!(self.txns.0.contains_key(&t), "read: requires txns.contains_key(t)");
        assert!(self.cell_value.0.contains_key(&c),
            "read: requires cell_value.contains_key(c)  <-- THE PRECONDITION THAT PANICS AT l2_exec.rs:1922");
        assert!(!self.txns.0[&t].committed, "read: requires !txns[t].committed");
        let v = self.cell_value.0[&c];
        let w = self.cell_writer.0[&c];
        let txn = self.txns.0.get_mut(&t).unwrap();
        if !txn.read_set.contains(&c) { txn.read_set.push(c); }
        txn.read_values.insert(c, v);
        if w != t && !txn.predecessors.contains(&w) { txn.predecessors.push(w); }
        self.now += 1;
    }

    pub fn write(&mut self, t: u64, c: u64, v: u64) {
        assert!(self.txns.0.contains_key(&t), "write: requires txns.contains_key(t)");
        assert!(!self.txns.0[&t].committed, "write: requires !txns[t].committed");
        self.txns.0.get_mut(&t).unwrap().writes.push((c, v));
        self.now += 1;
    }

    pub fn commit(&mut self, t: u64) {
        assert!(self.txns.0.contains_key(&t), "commit: requires txns.contains_key(t)");
        let ws = self.txns.0[&t].writes.clone();
        for (c, v) in ws { self.cell_value.0.insert(c, v); self.cell_writer.0.insert(c, t); }
        let txn = self.txns.0.get_mut(&t).unwrap();
        txn.committed = true; txn.commit_time = self.now;
        self.now += 1;
    }

    pub fn abort(&mut self, t: u64) {
        assert!(self.txns.0.contains_key(&t), "abort: requires txns.contains_key(t)");
        self.txns.0.get_mut(&t).unwrap().aborted = true;
        // cascade_abort: transitively abort every txn retaining an aborted predecessor
        loop {
            let mut changed = false;
            let ids: Vec<u64> = self.txns.0.keys().copied().collect();
            for id in ids {
                if self.txns.0[&id].aborted { continue; }
                let preds = self.txns.0[&id].predecessors.clone();
                if preds.iter().any(|p| self.txns.0.get(p).map_or(false, |q| q.aborted)) {
                    self.txns.0.get_mut(&id).unwrap().aborted = true; changed = true;
                }
            }
            if !changed { break; }
        }
        self.now += 1;
    }
}
