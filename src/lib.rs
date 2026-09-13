pub mod agent;

pub mod detectors;

pub mod oprecord;
pub mod pess_concurrent;
pub mod pessimistic;

pub mod si_concurrent;

pub mod snapshot_isolation;

pub mod store;

pub mod vanilla;

pub mod lib_si_validate_exec;

pub mod verified_si;

// The VERIFIED L2 runtime, byte-identical to
// ../mac-consistency-pilot/verus-detector/src/lib_l2_exec.rs, compiled
// here by plain cargo with the verus! macro erasing the proofs -- the
// same discipline as si_concurrent.rs and pess_concurrent.rs.
pub mod l2_exec;

// The L1-class baseline: validates reads, does not cascade. Ordinary
// Rust, no safety claim.
pub mod l2_unguarded;

// The measurement driver: guarded arm is l2_exec, unguarded arm is
// l2_unguarded, and the two are run over the same seeded schedules.
pub mod l2_measure;

// Superseded L2-class store. Its guarded path carries a write-set
// carve-out that commit_valid does not have; nothing should cite it.
pub mod l2_causal;

#[allow(dead_code)]
pub mod l3_sequencer;
pub mod l4_registry;

pub use agent::{Agent, Emitter, VecEmitter};

pub use detectors::{
    classify_level, detect_a1, detect_a2, detect_a3, detect_a6, A1Witness, A3Witness, NULL_VALUE,
};

pub use oprecord::{CellId, OpRecord, Time, ToolId, Value};

pub use pessimistic::PessimisticStore;

pub use snapshot_isolation::SnapshotIsolationStore;

pub use store::{CommitOutcome, Snapshot, Store};

pub use vanilla::VanillaStore;
