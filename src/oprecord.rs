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
    pub read_values: BTreeMap<CellId, Value>,
    pub read_time: Time,
    pub write_set: Vec<CellId>,
    pub write_values: BTreeMap<CellId, Value>,
    pub write_time: Time,
    pub planned_tool: Option<ToolId>,
    pub tools_used: Vec<ToolId>,
    pub tools_visible_at_read: Vec<ToolId>,
    pub io: Vec<(CellId, Value)>,
    pub co: Vec<(CellId, Value)>,
}

impl OpRecord {
    pub fn writes_cell(&self, c: &str) -> bool {
        self.write_set.iter().any(|x| x == c)
    }

    pub fn reads_cell(&self, c: &str) -> bool {
        self.read_set.iter().any(|x| x == c)
    }
    
    pub fn first_read_value(&self, c: &str) -> Option<&Value> {
        self.read_values.get(c)
    }

    pub fn first_write_value(&self, c: &str) -> Option<&Value> {
        self.write_values.get(c)
    }
}