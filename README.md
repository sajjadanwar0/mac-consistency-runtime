# mac-consistency-runtime

Reference Rust runtime for the paper **Verified Detection and Prevention of
Concurrency Anomalies in Multi-Agent Large Language Model Systems**
(arXiv:2606.17182). It implements the consistency-control backends of the
L₀–L₄ lattice over a common `Store` trait, ports the four Verus-verified
anomaly detectors to executable Rust, and — via the `l2-live/` driver — runs
the verified L₂ discipline under live LLM agents.

This is the artifact referenced in §6 as the principal Rust deliverable, plus
the live-deployment harness for §5 (executable L₂ runtime).

**Companion repositories.** The TLA+/TLC/TLAPS specifications and proofs are in
`mac-consistency`; the full Verus development (all proof files, 274 curated /
295 full obligations, including the `lib_l2_safety.rs` / `lib_l*_exec.rs` /
refinement proofs) is in `mac-consistency-pilot/verus-detector/`. This crate
contains only the two Verus-exec helpers that back SI validation
(`verified_si.rs`, `lib_si_validate_exec.rs`); everything else here is ordinary
executable Rust.

## Honest scope (read this first)

This crate **is**:
- Working Rust backends over a common `Store` trait: an unsynchronized baseline,
  pessimistic locking, snapshot isolation (with optional SSI), and the L₂/L₃/L₄
  discipline models (causal tracking with cascading abort, an effect sequencer,
  a registry-snapshot model).
- A Rust port of the four detectors (`detect_a1/a2/a3/a6`) proved sound *and*
  complete in Verus (in `mac-consistency-pilot/verus-detector/`), written to
  mirror the Verus source line-for-line.
- A live-agent driver (`l2-live/`) that drives the **real** `L2CausalStore`
  under OpenAI / Anthropic / OpenAI-compatible (vLLM, Ollama) models and measures
  A₃ prevention.

This crate **is not**:
- Fully verified Rust. The detectors mirror the verified Verus versions by
  inspection; the locking and SI runtimes are unverified (their L₂ counterpart
  carries a separate exec-mode refinement in the Verus development —
  `mac-consistency-pilot/verus-detector/lib_l2_exec.rs`, 49 verified).
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
  l2_causal.rs            L2: causal tracking + cascading abort; detect_a3_cascade; twin experiment
  l3_sequencer.rs         L3: tool-effect ordering model (A6)
  l4_registry.rs          L4: registry-snapshot model (A2)
  detectors.rs            Rust ports of the four Verus-verified detectors
  agent.rs                Agent API + Emitter trait (VecEmitter)
tests/
  integration.rs          end-to-end tests across the backends
l2-live/                  live-agent driver (separate crate; see below)
  Cargo.toml
  src/main.rs
  l2_live_out/            recorded run outputs (git-ignored; zipped snapshot also present)
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
- `l2_causal` tests: the unguarded baseline admits A₃ in 1000/1000 scenarios at
  depths {2,3,5}; the L₂ cascade discipline admits it in **0/1000**, including
  transitive cascades (the dependency-free twin).

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

## `l2-live`: live A₃ prevention under real agents

`l2-live/` is a standalone binary that exercises the **real** L₂ runtime — it
pulls in `src/l2_causal.rs` via `#[path]` (no fork, no `vstd` dependency) and
drives `L2CausalStore` from a live plan→execute→revise loop: a planner commits a
plan for an ambiguous triage ticket, an executor reads it (acquiring the planner
as a causal predecessor) and commits a result, and a supervisor LLM decides
whether to retract the plan (the live analogue of saga compensation). It scores
every trace with the verified `detect_a3_cascade` and reports per-model and
pooled prevention with rule-of-three CIs and executor-liveness.

```bash
cd l2-live
# validate the wiring with no API calls (reproduces the synthetic twin)
cargo run --release -- --dry-run --n 200

# live runs (set keys; --validator llm lets each model decide retraction)
OPENAI_API_KEY=…    cargo run --release -- --provider openai    --model gpt-4o-mini       --validator llm --n 200
ANTHROPIC_API_KEY=… cargo run --release -- --provider anthropic --model claude-haiku-4-5  --validator llm --n 200
cargo run --release -- --provider vllm --base-url http://localhost:11434 --model llama3.2:latest --validator llm --n 200
```

**Measured result.** Across three model families the supervisor-driven
retraction rate — the trigger for A₃ — spanned **0%** (claude-haiku-4-5, a
permissive supervisor), **15.5%** (gpt-4o-mini), and **44.5%** (Llama-3.2). In
all **120** retracted sessions pooled across the three models, the unguarded
baseline left an A₃ witness; the verified L₂ discipline prevented every one
(**0/120, 95% CI [0, 2.5%]**), at 80% pooled executor-liveness. The prevention
is structural — the executor depends on the planner because it read the plan
cell, and the verified cascade removes the dependent whenever its predecessor is
retracted — so 0% holds by construction of the verified discipline regardless of
model; the live runs demonstrate it operating under real, divergent agent
behavior, not a model-contingent property.

## Status of the higher levels

L₂ is verified, twin-measured, **and** deployed live (above). L₃ and L₄ are
verified and twin-measured but **not** yet run under live agents: A₆ is a runtime
write-sequencing property and the current `Agent::commit` always applies effects
in intended order (`co = io`), so exercising it live would require a multi-effect
commit path that reorders under concurrency — not yet built.