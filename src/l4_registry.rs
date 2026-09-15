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

pub fn a2_witness(pinned_sig: u64, dispatched_sig: u64) -> bool {
    dispatched_sig != pinned_sig
}

#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    LiveResolve,
    SnapshotResolve,
}

// 2026-09-14 round 3. Two constructions used to decide this experiment before
// it ran, and both are removed here.
//
//   1. `registry[t] = pinned_sig ^ (1 + rng.below(0xFFFF_FFFF));` rewrote the
//      planned tool's signature unconditionally AFTER the churn loop, with a
//      guaranteed-nonzero mask. The live baseline therefore admitted A2 in
//      1000/1000 runs for every seed and width, and `measure_a2_prevention`
//      asserted that. Removed: A2 now fires iff the churn happened to touch the
//      planned slot, which is a measurement. The accompanying
//      `debug_assert_ne!` enforced the same thing and is removed with it.
//
//   2. The guarded branch returns `snapshot[t]`, and `pinned_sig` IS
//      `snapshot[t]`, so `a2_witness(pinned, dispatched)` compared a value with
//      itself. That zero is definitional in this model, not the outcome of a
//      resolution step, and the third return value now makes the claim
//      checkable: the precondition (did the churn touch the planned tool?) is
//      reported alongside, so a prevented run is one where the hazard was
//      present and did not fire.
fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> (u64, u64, bool) {
    let mut registry: Vec<u64> = (0..w).map(|_| rng.next()).collect();
    let t = rng.below(w as u64) as usize;
    let snapshot: Vec<u64> = registry.clone();
    let pinned_sig = snapshot[t];
    let churn = 1 + rng.below(w as u64) as usize;

    for _ in 0..churn {
        let victim = rng.below(w as u64) as usize;
        registry[victim] ^= 1 + rng.below(u64::MAX - 1);
    }

    let churned_planned_tool = registry[t] != pinned_sig;

    let dispatched_sig = match mode {
        Mode::LiveResolve => registry[t],
        Mode::SnapshotResolve => snapshot[t],
    };
    (pinned_sig, dispatched_sig, churned_planned_tool)
}

pub struct ExperimentResult {
    pub runs: usize,
    pub a2_positive: usize,
    /// Runs in which the churn actually touched the planned tool, i.e. runs in
    /// which a phantom-tool dispatch was there to be prevented.
    pub precondition_positive: usize,
}
impl ExperimentResult {
    pub fn a2_rate(&self) -> f64 {
        self.a2_positive as f64 / self.runs as f64
    }
    pub fn precondition_rate(&self) -> f64 {
        self.precondition_positive as f64 / self.runs as f64
    }
}

pub fn run_experiment(runs: usize, width: usize, mode: Mode, seed: u64) -> ExperimentResult {
    let mut rng = XorShift::new(seed);
    let mut pos = 0usize;
    let mut pre = 0usize;
    for _ in 0..runs {
        let (pinned, dispatched, churned) = run_once(width, mode, &mut rng);
        if churned {
            pre += 1;
        }
        if a2_witness(pinned, dispatched) {
            pos += 1;
        }
    }
    ExperimentResult { runs, a2_positive: pos, precondition_positive: pre }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn measure_a2_prevention() {
        let runs = 1000;
        for width in [2usize, 4, 16] {
            let base = run_experiment(runs, width, Mode::LiveResolve, 0xBADC0DE + width as u64);
            let snap = run_experiment(runs, width, Mode::SnapshotResolve, 0xBADC0DE + width as u64);
            println!(
                "width={}  planned tool churned = {}/{} ({:.1}%)   baseline A2 = {}/{} ({:.1}%)   L4 snapshot A2 = {}/{} ({:.1}%)",
                width,
                base.precondition_positive, base.runs, base.precondition_rate() * 100.0,
                base.a2_positive, base.runs, base.a2_rate() * 100.0,
                snap.a2_positive, snap.runs, snap.a2_rate() * 100.0,
            );
            assert_eq!(
                base.a2_positive, base.precondition_positive,
                "live baseline must admit A2 exactly on the runs where the churn touched the planned tool"
            );
            assert_eq!(snap.a2_positive, 0, "snapshot runtime must always prevent A2");
            assert!(
                base.precondition_positive > 0 && base.precondition_positive < runs,
                "the churn must sometimes hit and sometimes miss the planned tool; got {}/{}",
                base.precondition_positive, runs
            );
        }
    }

    #[test]
    fn snapshot_dispatches_pinned() {
        let mut rng = XorShift::new(7);
        for width in [1usize, 3, 8] {
            for _ in 0..200 {
                let (pinned, dispatched, _) = run_once(width, Mode::SnapshotResolve, &mut rng);
                assert_eq!(dispatched, pinned);
            }
        }
    }
}
