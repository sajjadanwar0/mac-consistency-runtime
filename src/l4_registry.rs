//! l4_registry.rs -- A2 (phantom tool) measured on the VERIFIED L4 dispatcher.
//!
//! 2026-09-16 round 30 (audit finding G2, runtime side). OVERRULED: this file
//! measured an unverified twin whose "L4 snapshot" arm returned `snapshot[t]`,
//! and `a2_witness(pinned, dispatched)` compared that with `pinned_sig`, which
//! was `snapshot[t]`: zero by construction -- the round-3 note that stood here
//! said so -- and still asserted as prevention. A call resolved from a snapshot
//! reaches the LIVE tool. A2 is now judged against the live registry at
//! dispatch: the planned tool revoked, or re-signed since the plan, as in
//! lib_l4_safety.rs and lib_l4_exec.rs (pilot round 29). The churn now revokes
//! tools as well as re-signing them.
//!
//! One seeded schedule per run: a registry of `width` live tools, an operation
//! pins one, then `churn` events re-sign or revoke random tools. Three
//! dispatchers then act on that same registry, and one predicate,
//! `a2_at_dispatch`, scores all three:
//!   - live resolution (baseline): calls the planned tool as the registry now
//!     has it, unvalidated;
//!   - snapshot resolution (the withdrawn L4 claim): resolves the pinned
//!     binding from its snapshot and calls, unvalidated; the call reaches the
//!     live tool all the same;
//!   - validated (L4): `crate::l4_exec::PinnedOp::dispatch`, the verified
//!     dispatcher (src/l4_exec.rs, byte-identical to the pilot's
//!     lib_l4_exec.rs), which refuses unless the live binding still matches.

use crate::l4_exec::{L4Registry, PinnedOp};

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

/// A2 at dispatch: a call to `tool` reaches a tool that is missing, revoked,
/// or re-signed since the operation pinned `pinned` (lib_l4_exec.rs
/// `a2_witness_exec`, on the erased registry).
pub fn a2_at_dispatch(live: &[Option<u64>], tool: usize, pinned: u64) -> bool {
    live.get(tool) != Some(&Some(pinned))
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    LiveResolve,
    SnapshotResolve,
    Validated,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Run {
    /// churn revoked or re-signed the planned tool between pin and dispatch
    pub hazard: bool,
    /// the dispatcher placed the call
    pub dispatched: bool,
    /// the call reached a phantom
    pub a2: bool,
    /// the binding the dispatcher resolved was the pinned one
    pub resolved_pinned: bool,
    /// churn events of each kind in this run
    pub revocations: u64,
    pub resignings: u64,
}

fn run_once(width: usize, mode: Mode, rng: &mut XorShift) -> Run {
    let mut reg = L4Registry { sigs: (0..width).map(|_| Some(rng.next())).collect() };
    let tool = rng.below(width as u64) as usize;
    let op = PinnedOp::pin(&reg, tool).expect("every tool is live before the churn");
    let snapshot: Vec<Option<u64>> = reg.sigs.clone();
    let churn = 1 + rng.below(width as u64) as usize;
    let mut run = Run::default();
    for _ in 0..churn {
        let victim = rng.below(width as u64) as usize;
        if rng.below(4) == 0 {
            assert!(reg.revoke(victim), "revoke refused an in-range tool");
            run.revocations += 1;
        } else {
            let sig = rng.next();
            assert!(reg.resign(victim, sig), "resign refused an in-range tool");
            run.resignings += 1;
        }
    }
    run.hazard = a2_at_dispatch(&reg.sigs, tool, op.pinned_sig);

    let resolved = match mode {
        Mode::LiveResolve => reg.sigs[tool],
        Mode::SnapshotResolve => snapshot[tool],
        Mode::Validated => op.dispatch(&reg),
    };
    // The unvalidated dispatchers always place the call -- against a revoked
    // tool too; the validated one only when dispatch returned Some.
    run.dispatched = match mode {
        Mode::LiveResolve | Mode::SnapshotResolve => true,
        Mode::Validated => resolved.is_some(),
    };
    run.resolved_pinned = resolved == Some(op.pinned_sig);
    run.a2 = run.dispatched && a2_at_dispatch(&reg.sigs, tool, op.pinned_sig);
    run
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ExperimentResult {
    pub runs: usize,
    /// runs in which churn revoked or re-signed the planned tool: the hazard
    pub hazard: usize,
    pub dispatched: usize,
    pub a2_positive: usize,
    pub resolved_pinned: usize,
    pub revocations: u64,
    pub resignings: u64,
}

impl ExperimentResult {
    pub fn refused(&self) -> usize {
        self.runs - self.dispatched
    }
}

pub fn run_experiment(runs: usize, width: usize, mode: Mode, seed: u64) -> ExperimentResult {
    let mut rng = XorShift::new(seed);
    let mut r = ExperimentResult { runs, ..ExperimentResult::default() };
    for _ in 0..runs {
        let o = run_once(width, mode, &mut rng);
        r.hazard += o.hazard as usize;
        r.dispatched += o.dispatched as usize;
        r.a2_positive += o.a2 as usize;
        r.resolved_pinned += o.resolved_pinned as usize;
        r.revocations += o.revocations;
        r.resignings += o.resignings;
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arms(width: usize) -> (ExperimentResult, ExperimentResult, ExperimentResult) {
        let seed = 0xBADC0DE + width as u64;
        (
            run_experiment(1000, width, Mode::LiveResolve, seed),
            run_experiment(1000, width, Mode::SnapshotResolve, seed),
            run_experiment(1000, width, Mode::Validated, seed),
        )
    }

    #[test]
    fn measure_a2_prevention() {
        for width in [2usize, 4, 16] {
            let (live, snap, val) = arms(width);
            // one schedule per seed: the three arms see the same hazards
            assert_eq!(live.hazard, snap.hazard);
            assert_eq!(live.hazard, val.hazard);
            assert!(
                live.hazard > 0 && live.hazard < live.runs,
                "the churn must sometimes hit and sometimes miss the planned tool; got {}/{}",
                live.hazard, live.runs
            );
            assert_eq!(live.a2_positive, live.hazard, "live resolution must call a phantom exactly on the hazard runs");
            assert_eq!(val.a2_positive, 0, "the verified dispatcher called a phantom");
            assert_eq!(val.refused(), val.hazard, "the verified dispatcher must refuse exactly the hazard runs");
        }
    }

    #[test]
    fn snapshot_resolution_does_not_prevent_a2() {
        for width in [2usize, 4, 16] {
            let (live, snap, _) = arms(width);
            assert_eq!(
                snap.a2_positive, live.a2_positive,
                "a snapshot changes what the operation resolves, not the tool its call reaches"
            );
        }
    }

    #[test]
    fn snapshot_dispatches_pinned() {
        // The OVERRULED claim's premise still holds -- the snapshot always
        // resolves the pinned binding -- and the test above shows it prevents
        // nothing.
        for width in [1usize, 3, 8] {
            let s = run_experiment(200, width, Mode::SnapshotResolve, 7 + width as u64);
            assert_eq!(s.resolved_pinned, s.runs);
        }
    }

    #[test]
    fn churn_revokes_and_resigns() {
        let (live, _, _) = arms(4);
        assert!(live.revocations > 0 && live.resignings > 0, "both kinds of churn must occur");
    }

    #[test]
    fn the_verified_executions_hold_under_cargo() {
        assert_eq!(crate::l4_exec::revoked_tool_is_refused(), None);
        assert_eq!(crate::l4_exec::resigned_tool_is_refused(), None);
        assert_eq!(crate::l4_exec::unchanged_tool_is_dispatched(), Some(5));
    }
}
