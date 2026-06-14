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

fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> (u64, u64) {
    let mut registry: Vec<u64> = (0..w).map(|_| rng.next()).collect();
    let t = rng.below(w as u64) as usize;
    let snapshot: Vec<u64> = registry.clone();
    let pinned_sig = snapshot[t];
    let churn = 1 + rng.below(w as u64) as usize;

    for _ in 0..churn {
        let victim = rng.below(w as u64) as usize;
        registry[victim] ^= 1 + rng.below(u64::MAX - 1);
    }

    registry[t] = pinned_sig ^ (1 + rng.below(0xFFFF_FFFF));

    debug_assert_ne!(registry[t], pinned_sig, "churn must change the planned tool");

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