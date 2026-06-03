# agent-consistency-runtime

Reference Rust runtime that integrates the Verus-verified detectors
from `verus_lib_v3.rs` with three concurrency-control backends. This is
the artefact referenced in §6 of the paper as the principal Rust
deliverable.

## Honest scope (read this first)

This crate **is**:
- A working Rust library implementing three runtime backends (vanilla,
  pessimistic locking, snapshot isolation with optional SSI mode) over a
  common `Store` trait
- An agent-facing API (`Agent`) that emits `OpRecord` events compatible
  with the JSONL traces produced by the Python pilot
- A Rust port of the four anomaly detectors that are verified sound and
  complete in `verus_lib_v3.rs`
- A self-contained crate that compiles standalone

This crate **is not**:
- Verified Rust. The detectors mirror the verified Verus version by
  inspection; the runtimes themselves are unverified.
- Production-grade. There's no error-recovery, no observability, no
  performance tuning. This is a reference implementation, not a
  deployable agent runtime.
- Connected to LLMs. The agents are programmatic; integrating real LLM
  reasoning agents is left to the consumer.

## Build and test

```bash
cargo build
cargo test
```

`cargo test` runs the integration tests in `tests/integration.rs`,
which reproduce the empirical findings of the paper:

- Vanilla admits A_1 in the edit-review shape (test:
  `vanilla_admits_a1`).
- Pessimistic locking blocks at begin and produces clean traces
  (test: `pessimistic_blocks_at_begin`).
- SI aborts at validation when committing writes (test:
  `si_aborts_on_validation`).
- **SI default misses the no-write stale-read shape** that surfaces the
  3% triage gap (test: `si_default_misses_no_write_stale`).
- **SSI mode closes the gap** by validating every commit (test:
  `ssi_mode_closes_no_write_gap`).

The last two tests are the runnable counterpart to §5.5's empirical
finding.

## Layout

```
src/
  lib.rs              re-exports
  oprecord.rs         OpRecord struct (canonical record format)
  store.rs            Store trait
  vanilla.rs          unsynchronized baseline
  pessimistic.rs      per-cell locks, non-blocking acquire
  snapshot_isolation.rs   MVCC + commit-time validation, optional SSI mode
  agent.rs            Agent API + Emitter trait
  detectors.rs        Rust port of the four Verus-verified detectors
tests/
  integration.rs      end-to-end tests across all three backends
```

## Spec-to-implementation correspondence

The four detectors in `src/detectors.rs` (`detect_a1`, `detect_a2`,
`detect_a3`, `detect_a6`) are the executable counterparts of the
Verus-verified versions in `verus_lib_v3.rs`. The Verus chain proves
soundness AND completeness equivalence with the TLA+ predicate. This
crate's detectors are written to mirror the Verus code line-for-line so
the inspection cost of trusting the equivalence is small.

The runtimes (`vanilla`, `pessimistic`, `snapshot_isolation`) are
**not** Verus-verified. Their correctness is established by:

1. Code inspection against §3 (operational model) of the paper
2. Integration tests that exercise the runtime against expected
   detector outcomes
3. Equivalence (in spirit) with the Python baselines in
   `mac-consistency-pilot/python/baselines/runtimes/`

A natural follow-up is to verify the runtimes themselves. The locking
runtime is the closest to existing verified-concurrency artifacts
(IronFleet, Verdi); the SI/MVCC runtime would require a more substantial
proof effort.

## Use as a library

```rust
use std::sync::Arc;
use agent_consistency_runtime::{Agent, PessimisticStore, Store, VecEmitter};

fn main() {
    let store: Arc<dyn Store> = Arc::new(PessimisticStore::new());
    let emitter = Arc::new(VecEmitter::new());
    let alice = Agent::new("alice", store.clone(), emitter.clone(), vec![]);

    alice.begin(&["doc".to_string()], None).unwrap();
    alice.commit(&[("doc".to_string(), "hello".to_string())], None).unwrap();

    let records = emitter.drain();
    println!("{} records emitted", records.len());
    println!("conflicts: {}, aborts: {}", store.begin_conflicts(), store.aborts());
}
```

## What's missing for a paper-grade artefact

To turn this from a reference implementation into something a reviewer
calls "production-grade":

1. Async/Tokio integration so it's usable from real async agent runtimes
2. JSONL emitter (write traces to disk in the same format as the Python
   pilot, so the Python detector pipeline runs against Rust-emitted
   traces)
3. Performance benchmarks: latency overhead of pessimistic vs SI vs
   vanilla under realistic concurrent agent workloads
4. Adapters for real agent frameworks (AutoGen Python via FFI, or
   Rust-native agent crates like `rig`)

These are the items that would lift the Rust artefact from "reference"
to "deployable." None are in scope for this paper version.
