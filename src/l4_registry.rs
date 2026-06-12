//! L4 registry-snapshot runtime: an **executable** realisation of the L4
//! model verified in `verus-detector/src/lib_l4_safety.rs` (state-machine
//! level) and `verus-detector/src/lib_l4_exec.rs` (exec-mode snapshot
//! discipline).
//!
//! The A_2 anomaly (phantom tool) fires when an operation plans a tool call
//! against the registry it observed at read time, but by call time the
//! registry has been mutated -- the tool removed or its signature changed --
//! so the call dispatches against a tool that no longer matches the plan.
//! The L4 snapshot discipline prevents it BY CONSTRUCTION: the operation
//! resolves its tool binding from a registry snapshot pinned at read time,
//! so concurrent registry churn cannot reach it.
//!
//! Correspondence to the verified artifacts:
//!   * `SnapshotOp::pin` / `dispatch` -- the exec-mode operations of
//!     `lib_l4_exec.rs` (verified: dispatch returns exactly the pinned
//!     signature; the live registry is not an input to dispatch); here
//!     reimplemented dependency-free for std.
//!   * `a2_witness` -- the catalogued A_2 predicate: dispatched signature
//!     differs from the planned (pinned) signature.
//!   * `Mode::LiveResolve` -- the contrast baseline: dispatch reads the
//!     live, post-mutation registry, which exhibits A_2 under any churn
//!     that touches the planned tool. Running identical adversarial churn
//!     schedules under both modes makes A_2 prevention **measurable**: the
//!     baseline produces witnesses; the snapshot runtime none.
//!
//! As with the L2 and L3 pairs, the verified exec artifact and this
//! measured twin are two artifacts of one protocol; the guarantee is the
//! Verus theorem, this file corroborates it and exhibits the unguarded
//! baseline's anomaly.

/// Deterministic xorshift64* PRNG: no external crates, reproducible runs.
struct XorShift(u64);
impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(seed.max(1))
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

/// Catalogued A_2 over one operation: the signature actually dispatched
/// against differs from the signature the operation planned (pinned).
pub fn a2_witness(pinned_sig: u64, dispatched_sig: u64) -> bool {
    dispatched_sig != pinned_sig
}

#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    /// Resolve the tool binding from the live registry at call time
    /// (unguarded baseline): registry churn between pin and call reaches
    /// the dispatch.
    LiveResolve,
    /// Resolve from the snapshot pinned at read time (L4 discipline).
    SnapshotResolve,
}

/// One run: a registry of `w` tools gets initial signatures; an operation
/// pins tool `t`; the adversary then mutates the registry -- including,
/// crucially, tool `t` itself, to a guaranteed-different signature --
/// before the operation dispatches. Returns (pinned_sig, dispatched_sig).
fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> (u64, u64) {
    // Live registry with random initial signatures.
    let mut registry: Vec<u64> = (0..w).map(|_| rng.next()).collect();
    // Operation pins: planned tool + full snapshot (the L4 pin).
    let t = rng.below(w as u64) as usize;
    let snapshot: Vec<u64> = registry.clone();
    let pinned_sig = snapshot[t];
    // Adversarial churn between pin and dispatch: mutate several tools,
    // always including the planned tool, to a guaranteed-different
    // signature (xor with a nonzero value can never be a fixed point).
    let churn = 1 + rng.below(w as u64) as usize;
    for _ in 0..churn {
        let victim = rng.below(w as u64) as usize;
        registry[victim] ^= 1 + rng.below(u64::MAX - 1);
    }
    registry[t] = pinned_sig ^ (1 + rng.below(0xFFFF_FFFF));
    debug_assert_ne!(registry[t], pinned_sig, "churn must change the planned tool");
    // Dispatch.
    let dispatched_sig = match mode {
        Mode::LiveResolve => registry[t],
        Mode::SnapshotResolve => snapshot[t],
    };
    (pinned_sig, dispatched_sig)
}

pub struct ExperimentResult {
    pub runs: usize,
    pub a2_positive: usize,
}
impl ExperimentResult {
    pub fn a2_rate(&self) -> f64 {
        self.a2_positive as f64 / self.runs as f64
    }
}

pub fn run_experiment(runs: usize, width: usize, mode: Mode, seed: u64) -> ExperimentResult {
    let mut rng = XorShift::new(seed);
    let mut pos = 0usize;
    for _ in 0..runs {
        let (pinned, dispatched) = run_once(width, mode, &mut rng);
        if a2_witness(pinned, dispatched) {
            pos += 1;
        }
    }
    ExperimentResult { runs, a2_positive: pos }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Mirrors measure_a3_prevention / measure_a6_prevention: identical
    /// adversarial churn schedules drive both modes; the live-resolving
    /// baseline must witness A_2 on every run (the planned tool's
    /// signature is always changed between pin and dispatch), the
    /// snapshot runtime on none. Self-asserting: a regression in either
    /// direction fails CI.
    #[test]
    fn measure_a2_prevention() {
        let runs = 1000;
        for width in [2usize, 4, 16] {
            let base = run_experiment(runs, width, Mode::LiveResolve, 0xBADC0DE + width as u64);
            let snap = run_experiment(runs, width, Mode::SnapshotResolve, 0xBADC0DE + width as u64);
            println!(
                "width={}  baseline A2 = {}/{} ({:.0}%)   L4 snapshot A2 = {}/{} ({:.0}%)",
                width,
                base.a2_positive, base.runs, base.a2_rate() * 100.0,
                snap.a2_positive, snap.runs, snap.a2_rate() * 100.0,
            );
            assert_eq!(base.a2_positive, runs, "baseline must always admit A2 (planned tool always churned)");
            assert_eq!(snap.a2_positive, 0, "snapshot runtime must always prevent A2");
        }
    }

    /// Completeness guard: the snapshot runtime still dispatches, and
    /// dispatches exactly the pinned signature (prevention is not achieved
    /// by refusing or altering the call).
    #[test]
    fn snapshot_dispatches_pinned() {
        let mut rng = XorShift::new(7);
        for width in [1usize, 3, 8] {
            for _ in 0..200 {
                let (pinned, dispatched) = run_once(width, Mode::SnapshotResolve, &mut rng);
                assert_eq!(dispatched, pinned);
            }
        }
    }
}