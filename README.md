# mac-consistency-runtime

Reference Rust runtime for the paper **Verified Detection and Prevention of
Concurrency Anomalies in Multi-Agent Large Language Model Systems**
(arXiv:2606.17182). It implements the consistency-control backends of the
L₀–L₄ lattice over a common `Store` trait, ports the four Verus-verified
anomaly detectors to executable Rust, and runs the verified L₂ runtime
(`src/l2_exec.rs`) against an unguarded baseline, synthetically and on 600
recorded live-agent sessions.

This is the artifact referenced in §6 as the principal Rust deliverable, plus
the L₂ measurement and session replay for §5 (executable L₂ runtime).

**Companion repositories.** The TLA+/TLC/TLAPS specifications and proofs are in
`mac-consistency`; the full Verus development (all proof files, 358 curated /
379 full obligations, including the `lib_l2_safety.rs` / `lib_l*_exec.rs` /
refinement proofs) is in `mac-consistency-pilot/verus-detector/`. This crate
carries Verus source that plain cargo compiles with the proofs erased: the two
helpers that back SI validation (`verified_si.rs`, `lib_si_validate_exec.rs`)
and two verified runtimes copied byte-for-byte from the pilot, `src/l2_exec.rs`
and `src/l4_exec.rs`; everything else here is ordinary executable Rust.

## Honest scope (read this first)

This crate **is**:
- Working Rust backends over a common `Store` trait: an unsynchronized baseline,
  pessimistic locking, snapshot isolation (with optional SSI), and the L₂/L₃/L₄
  discipline models (causal tracking with output commit and cascading abort, an
  effect sequencer, registry validation at dispatch).
- A Rust port of the four detectors (`detect_a1/a2/a3/a6`) proved sound *and*
  complete in Verus (in `mac-consistency-pilot/verus-detector/`), written to
  mirror the Verus source line-for-line.
- The verified L₂ runtime (`src/l2_exec.rs`, byte-identical to
  `mac-consistency-pilot/verus-detector/src/lib_l2_exec.rs`) measured against an
  unguarded baseline (`examples/l2_measure.rs`), and 600 recorded live-agent
  sessions (`tools/live_l2/sessions`) replayed through both
  (`examples/l2_replay.rs`), and a live driver (`l2-live/`) that runs model
  agents on the verified runtime with output commit releasing the executor's
  effect.

This crate **is not**:
- Fully verified Rust. The detectors mirror the verified Verus versions by
  inspection, and the locking and SI runtimes are unverified. `src/l2_exec.rs`
  and `src/l4_exec.rs` are Verus source, byte-identical copies of the pilot's
  `lib_l2_exec.rs` (73 verified) and `lib_l4_exec.rs` (11 verified); plain cargo
  erases their proofs, and every entry point checks its own precondition at run
  time rather than relying on an erased `requires`.
  `verified_si.rs` and `lib_si_validate_exec.rs` are Verus source — standard
  `cargo build`/`cargo test` compiles and runs them as ordinary Rust; the Verus
  toolchain is needed only to *re-check* their proofs.
- Production-grade. No error recovery, observability, or tuning — a reference
  implementation, not a deployable agent runtime.

## Layout

```
src/
  lib.rs                  re-exports
  oprecord.rs             OpRecord (canonical record: read/write sets, io/co, times)
  store.rs                Store trait (begin / commit / tick / release)
  vanilla.rs              unsynchronized baseline (admits A1)
  pessimistic.rs          per-cell locks, non-blocking acquire
  snapshot_isolation.rs   MVCC + commit-time validation, optional SSI mode
  verified_si.rs          Verus-exec SI validation
  lib_si_validate_exec.rs Verus-exec SI validation lemma support
  l2_exec.rs              L2: the verified runtime (output commit, cascading abort), Verus source
  l2_unguarded.rs         L2 baseline: releases effects at commit, does not cascade
  l2_measure.rs           L2 measurement: verified runtime vs baseline; A3 detectors
  l2_replay_lib.rs        L2 replay of recorded live sessions through both arms
  l3_sequencer.rs         L3: commit-order sequencer (A6); exposed (pub), prevention twin
  l4_exec.rs              L4: the verified dispatcher (validates against the live registry), Verus source
  l4_registry.rs          L4 measurement: verified dispatcher vs live and snapshot resolution (A2)
  detectors.rs            Rust ports of the four Verus-verified detectors
  agent.rs                Agent API + Emitter trait (VecEmitter)
examples/
  l2_measure.rs           verified L2 runtime vs unguarded baseline, depths {2,3,5}
  l2_replay.rs            replay tools/live_l2/sessions through both arms
  l4_measure.rs           verified L4 dispatcher vs live and snapshot resolution, widths {2,4,16}
  l3_deploy.rs            runnable L3 sequencer: baseline 1000/1000 vs L3 0/1000 (A6)
tests/
  integration.rs          end-to-end tests across the backends
  l2_exec_predecessors.rs L2: readers of retracted writers cannot commit
  l2_exec_output_commit.rs  L2: release order, irrevocability, refusals
tools/live_l2/            gen_sessions.py (records live sessions) and the 600 recorded sessions
l2-live/                  live L2 driver: model agents on the verified runtime vs the baseline (separate crate; see below)
  Cargo.toml
  src/main.rs
  l2_live_out/            a run's output: sessions/ (replayable), per-model outboxes and summaries; commit it
```

## Build and test

```bash
cargo build
cargo test
```

`cargo test` runs `tests/integration.rs` and the in-module tests, reproducing
the paper's runnable findings:

- Vanilla admits A₁ in the edit-review shape (`vanilla_admits_a1`).
- Pessimistic locking blocks at begin and produces clean traces.
- SI aborts at validation when committing writes; **default-SI misses the
  no-write stale-read shape** (the 3% triage gap), and **SSI mode closes it**.
- `l2_measure` tests: A₃ is an operation whose effects are out while an
  operation in its causal closure is aborted. Over 1000 seeded scenarios at
  depths {2,3,5}, each with one committed transaction under review (retracted or
  approved, sometimes reviewed only after it released), the verified L₂ runtime
  admits A₃ in **0/1000** at every depth and the unguarded baseline, which
  releases at commit, in some scenarios but not all. Output commit holds effects
  somewhere, refuses some late retractions, and releases every live effect after
  the review.

```bash
cargo run --release --example l2_measure
```

| depth | verified A₃ | baseline A₃ | cascaded | commits refused | effects held | released / live | retractions refused |
|---|---|---|---|---|---|---|---|
| 2 | 0/1000 | 519/1000 | 564 | 830 | 748 | 2870 / 2870 | 199 / 771 |
| 3 | 0/1000 | 624/1000 | 940 | 1177 | 1255 | 3494 / 3494 | 199 / 771 |
| 5 | 0/1000 | 563/1000 | 889 | 1677 | 1272 | 5545 / 5545 | 199 / 771 |

- `l4_registry` tests: A₂ is a call that reaches a tool revoked, or re-signed,
  since its operation planned. Over 1000 seeded runs at widths {2,4,16}, each
  pinning one tool and then revoking or re-signing random tools, three
  dispatchers act on the same registry: live resolution and snapshot resolution
  call unvalidated, and the verified dispatcher (`src/l4_exec.rs`) refuses unless
  the live binding still matches. Snapshot resolution calls a phantom exactly as
  often as live resolution, because a snapshot changes what the operation
  resolves, not the tool its call reaches; the verified dispatcher calls none and
  refuses exactly the runs whose planned tool was hit.

```bash
cargo run --release --example l4_measure
```

| width | planned tool hit | live resolution A₂ | snapshot resolution A₂ | verified A₂ | verified refused | verified dispatched |
|---|---|---|---|---|---|---|
| 2 | 630/1000 | 630/1000 | 630/1000 | 0/1000 | 630 | 370 |
| 4 | 505/1000 | 505/1000 | 505/1000 | 0/1000 | 505 | 495 |
| 16 | 387/1000 | 387/1000 | 387/1000 | 0/1000 | 387 | 613 |

The L₃ sequencer is exposed as a runnable runtime:

```bash
cargo run --example l3_deploy   # baseline A₆ 1000/1000 vs L₃ sequencer 0/1000, widths {2,4,8}
cargo test l3_sequencer         # the L₃ prevention-twin tests
```

## Detector ↔ spec correspondence

`detect_a1/a2/a3/a6` are the executable counterparts of the Verus-verified
detectors (proved sound **and** complete against the TLA+ predicates in
`mac-consistency`; the proofs are in `mac-consistency-pilot/verus-detector/`,
e.g. `lib_detector_equivalence.rs`, 24 verified). For black-box traces that
expose neither causal closures nor abort flags, `detect_a3` uses the flat-trace
*residue* formulation it is proved equivalent to. The runtimes are established
by code inspection against the operational model (§3), the integration tests,
and equivalence in spirit with the Python baselines in
`mac-consistency-pilot/python/baselines/`.

## Live L₂ sessions, replayed through the verified runtime

`tools/live_l2/gen_sessions.py` drives the §5 workload against real models and
records each session: a planner commits a one-line plan for an ambiguous triage
ticket, an executor reads it (acquiring the planner as a causal predecessor) and
commits a result, and a supervisor model decides whether to retract the plan.
600 sessions are committed, 200 per model. `examples/l2_replay.rs` replays every
session through the verified runtime and through the unguarded baseline, with no
API key:

```bash
cargo run --release --example l2_replay -- tools/live_l2/sessions
```

| model | sessions | retracted | verified A₃ | baseline A₃ | executor released (verified) |
|---|---|---|---|---|---|
| claude-haiku-4-5 | 200 | 1 | 0/1 | 1/1 | 99.5% |
| gpt-4o-mini | 200 | 3 | 0/3 | 3/3 | 98.5% |
| llama3.2 | 200 | 62 | 0/62 | 62/62 | 69.0% |
| POOLED | 600 | 66 | 0/66 | 66/66 | 89.0% |

What this shows, and what it does not. A recorded session holds the supervisor's
verdict, not when effects left, so the replay applies one release policy to
every session. The baseline releases at commit: each retraction leaves the
executor's effects out on a withdrawn plan. The verified runtime keeps the plan
under review until the verdict, so the executor's release is refused until KEEP
releases the plan, and RETRACT aborts both before either is out. The zero is
structural (output commit, proved in `lib_l2_safety.rs` and run here from
`src/l2_exec.rs`); the live component measures only how often real supervisors
retract.

### Live deployment: `l2-live/`

`l2-live/` runs the same workload with the models in the loop and the verified
runtime deciding what leaves. In each session the planner and the executor are
model calls; both arms commit on those outputs; the executor asks to release its
effect, which the baseline does at once and output commit refuses while the plan
is under review; then the supervisor model decides. KEEP releases the plan and
then the executor's effect; RETRACT aborts the plan, and the cascade aborts the
executor. Each arm appends every effect it releases, with the time it left, to
its own outbox file, and each session records the verdict, the latency of every
model call, and how long a kept executor's effect was held.

```bash
cd l2-live
cargo run --release -- --provider openai    --model gpt-4o-mini      --n 200
cargo run --release -- --provider anthropic --model claude-haiku-4-5 --n 200
cargo run --release -- --provider ollama    --model llama3.2         --n 200
cargo run --release -- --provider openai --model dry --n 40 --validator forced --dry-run --out /tmp/l2dry
```

Sessions land in `l2-live/l2_live_out/sessions` in the recorded format, so
`cargo run --release --example l2_replay -- l2-live/l2_live_out/sessions`
replays a live run and must agree with it. A live run adds two things to the
replay: the verdicts are that run's, and the cost of output commit is measured as
wall-clock hold time. It cannot add evidence that the verified arm's zero depends
on the models: that zero is structural. No live-run figures are reported here
until such runs are committed.

The driver previously built `src/l2_causal.rs`, an unverified twin of the L₂
discipline since removed, through `#[path]`, and reported 0/120 from it; those
outputs are removed and were never evidence for the verified runtime.

## Status of the higher levels

L₂ is verified down to the executable runtime this crate runs
(`src/l2_exec.rs`), measured against an unguarded baseline, and replayed on 600
recorded live sessions; `l2-live/` deploys it with model agents and output commit
releasing the executor's effect, with no live-run figures reported yet. L₃ is verified, twin-measured, and run under live agents
(below). L₄ is verified down to the dispatcher this crate runs
(`src/l4_exec.rs`) and measured on it under seeded registry churn; it has not
been run under live agents.

The L₃ commit-order sequencer is exposed as a runnable runtime (`pub mod
l3_sequencer`, `examples/l3_deploy.rs`) and measured live by the companion
harness `mac-consistency-pilot/python/l3_live_a6.py`: a superstep executor
issues four concurrent tool effects per session through real model calls and
takes the asynchronous completion order as the reorder source — the in-the-wild
cause of A₆, not a synthetic shuffle. Across gpt-4o-mini, claude-haiku-4-5, and
locally-served Llama-3.2 (40 sessions each), the unsequenced baseline exhibited
A₆ in **110/120** sessions (91.7%; per family 38/40, 39/40, 33/40) while the L₃
sequencer prevented it in **0/120** (exact 95% upper bound 3.0%). This is a
controlled multi-model harness; the in-the-wild instance remains LangGraph's
`ToolNode` (`mac-consistency-pilot/python/langgraph_a6.py`).

No live registry-mutation harness exists for L₄ yet. The earlier claim that
snapshot isolation prevents A₂ is withdrawn: a snapshot changes what an operation
resolves, not the tool its call reaches (`lemma_snapshot_resolution_does_not_prevent_a2`
in the pilot's `lib_l4_safety.rs`, and `snapshot_resolution_does_not_prevent_a2`
here).
