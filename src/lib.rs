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
// same discipline as si_concurrent.rs and pess_concurrent.rs.  This is
// the runtime the L2 measurements are taken through.
pub mod l2_exec;

// The measurement driver.  Its guarded arm is l2_exec::L2Runtime above;
// its unguarded arm is the L1-class baseline, which carries no safety
// claim and exists only to exhibit what the discipline removes.
pub mod l2_measure;

// Unguarded L2-class baseline and the provenance-trace A3 detector.
// Its guarded path still carries the write-set carve-out that
// commit_valid does not have; nothing in Section 5.11 should cite it.
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
