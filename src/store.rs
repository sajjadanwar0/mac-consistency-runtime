use crate::oprecord::{CellId, Time, Value};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub enum CommitOutcome {
    Committed { write_time: Time },
    AbortedConflict,
}

#[derive(Clone, Debug)]
pub struct Snapshot {
    pub values: BTreeMap<CellId, Value>,
    pub read_time: Time,
}

pub trait Store: Send + Sync {
    fn begin(&self, agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str>;

    fn commit(
        &self,
        agent: &str,
        snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome;

    fn tick(&self) -> Time;

    fn release(&self, agent: &str);

    fn aborts(&self) -> u64 {
        0
    }

    fn begin_conflicts(&self) -> u64 {
        0
    }
}