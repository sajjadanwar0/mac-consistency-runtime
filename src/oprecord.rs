//! OpRecord: the canonical record emitted by every runtime in this crate.
//!
//! Format matches the JSONL traces produced by the Python pilot's
//! `instrument.py`, allowing the same detectors to run against records
//! from either runtime.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub type CellId = String;
pub type Value = String;
pub type ToolId = String;
pub type Time = u64;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OpRecord {
    pub agent: String,

    pub read_set: Vec<CellId>,
    /// Stored as an ordered map to preserve insertion order across serialise.
    pub read_values: BTreeMap<CellId, Value>,
    pub read_time: Time,

    pub write_set: Vec<CellId>,
    pub write_values: BTreeMap<CellId, Value>,
    pub write_time: Time,

    /// Tool actually planned for this op (None if the op is pure data).
    pub planned_tool: Option<ToolId>,
    pub tools_used: Vec<ToolId>,
    pub tools_visible_at_read: Vec<ToolId>,

    /// Order of effect *issuance* by the agent within this record.
    pub io: Vec<(CellId, Value)>,
    /// Order of effect *commit* by the runtime within this record.
    pub co: Vec<(CellId, Value)>,
}

impl OpRecord {
    pub fn writes_cell(&self, c: &str) -> bool {
        self.write_set.iter().any(|x| x == c)
    }

    pub fn reads_cell(&self, c: &str) -> bool {
        self.read_set.iter().any(|x| x == c)
    }

    /// First-match value lookup over the read_values map. Matches the Verus
    /// `first_value` spec: returns the first value associated with `c`, or
    /// `None` if `c` is not in the map.
    pub fn first_read_value(&self, c: &str) -> Option<&Value> {
        self.read_values.get(c)
    }

    pub fn first_write_value(&self, c: &str) -> Option<&Value> {
        self.write_values.get(c)
    }
}
