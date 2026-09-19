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
// ../mac-consistency-pilot/verus-detector/src/lib_l2_exec.rs, compiled here
// by plain cargo with the verus! macro erasing the proofs. Since round 26 every
// entry point checks its own precondition and refuses instead (G8); output
// commit (externalize) holds a dependent's effects until its closure is out.
pub mod l2_exec;

// The L1-class baseline: validates reads, does not cascade. Ordinary Rust,
// no proofs, no safety claim -- the behaviour L2 removes.
pub mod l2_unguarded;

// The synthetic measurement driver: the verified arm is l2_exec under output
// commit, the unguarded arm is l2_unguarded (releases at commit), over
// seed-varied schedules with a reviewed, retracted or approved transaction.
pub mod l2_measure;

// Replay of recorded live sessions through the same verified runtime, so
// the live L2 figure rests on the same artifact as the synthetic one.
pub mod l2_replay_lib;
#[allow(dead_code)]
pub mod l3_sequencer;

// The VERIFIED L4 dispatcher, byte-identical to
// ../mac-consistency-pilot/verus-detector/src/lib_l4_exec.rs (round 29):
// dispatch is refused unless the live registry still binds the planned tool to
// its pinned signature.
pub mod l4_exec;

// A2 measured on that dispatcher against live and snapshot resolution
// (round 30; OVERRULED: an unverified snapshot twin scored against itself).
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
