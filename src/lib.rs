//! Agent-consistency runtime crate.
//!
//! This crate provides:
//!   * Three concurrency-control backends (`vanilla`, `pessimistic`,
//!     `snapshot_isolation`), all implementing the `Store` trait.
//!   * A common `Agent` API over `Store` that emits `OpRecord` events to
//!     a pluggable `Emitter`.
//!   * The four anomaly detectors verified sound + complete in Verus
//!     (`detectors`).
//!
//! The detectors are verified in `verus_lib_v3.rs` (Verus); the runnable
//! port in this crate (`detectors.rs`) mirrors the verified spec by
//! inspection. The Verus chain proves equivalence between detector code
//! and TLA+ predicate; the operational claim that the runtimes prevent
//! the corresponding anomalies follows from the trace shape they emit
//! and is exercised in the integration tests.

pub mod agent;
pub mod detectors;
pub mod oprecord;
pub mod pessimistic;
pub mod snapshot_isolation;
pub mod store;
pub mod vanilla;
pub mod lib_si_validate_exec;
pub mod verified_si;
pub mod l2_causal;


pub use agent::{Agent, Emitter, VecEmitter};
pub use detectors::{
    classify_level, detect_a1, detect_a2, detect_a3, detect_a6, A1Witness, A3Witness, NULL_VALUE,
};
pub use oprecord::{CellId, OpRecord, Time, ToolId, Value};
pub use pessimistic::PessimisticStore;
pub use snapshot_isolation::SnapshotIsolationStore;
pub use store::{CommitOutcome, Snapshot, Store};
pub use vanilla::VanillaStore;
