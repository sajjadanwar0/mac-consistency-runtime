//! `Agent`: an agent-facing API over a `Store`.
//!
//! The agent owns a session ID, a reference to a `Store`, and an emitter
//! for `OpRecord`s. The pattern is:
//!
//!   let mut a = Agent::new("editor", store, emitter);
//!   a.begin(&["doc"], None);
//!   ... agent does stuff ...
//!   a.commit(&[("doc", "new value")], None);
//!
//! On a conflict (begin or commit), the operation is silently dropped: no
//! OpRecord is emitted but the runtime's abort counter increments. The
//! agent owner can choose to retry or proceed.

use crate::oprecord::{CellId, OpRecord, ToolId, Value};
use crate::store::{CommitOutcome, Snapshot, Store};
use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::sync::Arc;

/// A simple JSONL emitter; thread-safe via Mutex.
pub trait Emitter: Send + Sync {
    fn emit(&self, record: &OpRecord);
}

/// Append-only Vec emitter (good for tests).
#[derive(Default)]
pub struct VecEmitter {
    pub records: Mutex<Vec<OpRecord>>,
}

impl VecEmitter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn drain(&self) -> Vec<OpRecord> {
        std::mem::take(&mut self.records.lock())
    }
}

impl Emitter for VecEmitter {
    fn emit(&self, record: &OpRecord) {
        self.records.lock().push(record.clone());
    }
}

#[derive(Clone)]
struct Pending {
    snapshot: Snapshot,
    read_set: Vec<CellId>,
    planned_tool: Option<ToolId>,
    tools_visible: Vec<ToolId>,
    aborted_at_begin: bool,
}

pub struct Agent {
    pub agent_id: String,
    store: Arc<dyn Store>,
    emitter: Arc<dyn Emitter>,
    pending: Mutex<Option<Pending>>,
    visible_tools: Vec<ToolId>,
}

impl Agent {
    pub fn new(
        agent_id: impl Into<String>,
        store: Arc<dyn Store>,
        emitter: Arc<dyn Emitter>,
        visible_tools: Vec<ToolId>,
    ) -> Self {
        Self {
            agent_id: agent_id.into(),
            store,
            emitter,
            pending: Mutex::new(None),
            visible_tools,
        }
    }

    /// Begin an operation. If the runtime aborts, the op is marked as such
    /// and `commit()` will not emit; this is the pessimistic-locking
    /// non-blocking acquisition pattern.
    pub fn begin(
        &self,
        read_set: &[CellId],
        planned_tool: Option<ToolId>,
    ) -> Result<(), &'static str> {
        let mut pending = self.pending.lock();
        if pending.is_some() {
            return Err("begin during pending op");
        }
        let result = self.store.begin(&self.agent_id, read_set);
        match result {
            Ok(snapshot) => {
                *pending = Some(Pending {
                    snapshot,
                    read_set: read_set.to_vec(),
                    planned_tool,
                    tools_visible: self.visible_tools.clone(),
                    aborted_at_begin: false,
                });
                Ok(())
            }
            Err(_) => {
                // Aborted at begin: mark pending so commit() is consistent.
                *pending = Some(Pending {
                    snapshot: Snapshot {
                        values: BTreeMap::new(),
                        read_time: 0,
                    },
                    read_set: read_set.to_vec(),
                    planned_tool,
                    tools_visible: self.visible_tools.clone(),
                    aborted_at_begin: true,
                });
                Ok(())
            }
        }
    }

    pub fn commit(
        &self,
        writes: &[(CellId, Value)],
        tool_used: Option<ToolId>,
    ) -> Result<bool, &'static str> {
        let p = self.pending.lock().take().ok_or("commit without begin")?;
        if p.aborted_at_begin {
            // Drop. Aborted at begin already counted by the store.
            return Ok(false);
        }

        let writes_map: BTreeMap<CellId, Value> = writes.iter().cloned().collect();

        let outcome = self.store.commit(&self.agent_id, &p.snapshot, &writes_map);

        let (write_time, emit) = match outcome {
            CommitOutcome::Committed { write_time } => (write_time, true),
            CommitOutcome::AbortedConflict => {
                self.store.release(&self.agent_id);
                return Ok(false);
            }
        };

        let _ = emit;

        let tools_used = match (&tool_used, &p.planned_tool) {
            (Some(t), _) if p.tools_visible.contains(t) => vec![t.clone()],
            (None, Some(t)) if p.tools_visible.contains(t) => vec![t.clone()],
            _ => vec![],
        };

        let io: Vec<(CellId, Value)> = writes.to_vec();
        let co = io.clone();

        let record = OpRecord {
            agent: self.agent_id.clone(),
            read_set: p.read_set,
            read_values: p.snapshot.values,
            read_time: p.snapshot.read_time,
            write_set: writes_map.keys().cloned().collect(),
            write_values: writes_map,
            write_time,
            planned_tool: p.planned_tool,
            tools_used,
            tools_visible_at_read: p.tools_visible,
            io,
            co,
        };
        self.emitter.emit(&record);

        self.store.release(&self.agent_id);
        Ok(true)
    }

    /// Tick the clock for a no-write operation and emit a no-write record.
    pub fn no_write_commit(&self, tool_used: Option<ToolId>) -> Result<bool, &'static str> {
        let p = self.pending.lock().take().ok_or("commit without begin")?;
        if p.aborted_at_begin {
            return Ok(false);
        }

        // Under SI with validate_no_write=true (SSI), a no-write commit
        // still validates. We use the empty-writes path so the store
        // decides.
        let outcome = self.store.commit(&self.agent_id, &p.snapshot, &BTreeMap::new());

        let write_time = match outcome {
            CommitOutcome::Committed { write_time } => write_time,
            CommitOutcome::AbortedConflict => {
                self.store.release(&self.agent_id);
                return Ok(false);
            }
        };

        let tools_used = match (&tool_used, &p.planned_tool) {
            (Some(t), _) if p.tools_visible.contains(t) => vec![t.clone()],
            (None, Some(t)) if p.tools_visible.contains(t) => vec![t.clone()],
            _ => vec![],
        };

        let record = OpRecord {
            agent: self.agent_id.clone(),
            read_set: p.read_set,
            read_values: p.snapshot.values,
            read_time: p.snapshot.read_time,
            write_set: vec![],
            write_values: BTreeMap::new(),
            write_time,
            planned_tool: p.planned_tool,
            tools_used,
            tools_visible_at_read: p.tools_visible,
            io: vec![],
            co: vec![],
        };
        self.emitter.emit(&record);

        self.store.release(&self.agent_id);
        Ok(true)
    }
}
