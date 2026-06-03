//! `Store` trait — the interface every concurrency-control backend implements.

use crate::oprecord::{CellId, Time, Value};
use std::collections::BTreeMap;

/// Result of an attempted commit. The runtime surfaces aborts so the agent
/// can decide whether to retry; a `Committed` result emits an OpRecord.
#[derive(Clone, Debug)]
pub enum CommitOutcome {
    Committed { write_time: Time },
    AbortedConflict,
}

/// A snapshot returned by `Store::read`.
#[derive(Clone, Debug)]
pub struct Snapshot {
    pub values: BTreeMap<CellId, Value>,
    pub read_time: Time,
}

/// A `Store` is the agent-consistency runtime backend.
///
/// All three implementations in this crate (vanilla, pessimistic, snapshot
/// isolation) implement this trait. The agent API (see `agent.rs`) is generic
/// over Store so the same agent code switches runtime by parameter.
pub trait Store: Send + Sync {
    /// Begin an operation: try to acquire the locks (or take a snapshot)
    /// needed to read `cells`. Implementations decide what "begin" means:
    /// pessimistic: acquire per-cell locks (fail on conflict);
    /// SI: take a versioned snapshot (always succeeds);
    /// vanilla: just read current state.
    fn begin(&self, agent: &str, cells: &[CellId]) -> Result<Snapshot, &'static str>;

    /// Commit writes accumulated during the op. May abort under SI if
    /// validation fails, or under pessimistic locking if escalating writes
    /// cannot acquire the additional locks.
    fn commit(
        &self,
        agent: &str,
        snapshot: &Snapshot,
        writes: &BTreeMap<CellId, Value>,
    ) -> CommitOutcome;

    /// Tick the clock without writing or releasing anything (used by no-write
    /// commits in SI; pessimistic uses this to advance time after a release).
    fn tick(&self) -> Time;

    /// Release any locks an agent holds (no-op for SI / vanilla).
    fn release(&self, agent: &str);

    /// Telemetry: number of aborted commits across all agents.
    fn aborts(&self) -> u64 {
        0
    }

    /// Telemetry: number of begin-time conflicts (pessimistic only).
    fn begin_conflicts(&self) -> u64 {
        0
    }
}
