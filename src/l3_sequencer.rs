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

pub fn a6_witness(io: &[u64], co: &[u64]) -> bool {
    io.len() >= 2 && io.len() == co.len() && io != co
}

#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    Unsequenced,
    Sequenced,
}

// 2026-09-14 round 3. This function used to reshuffle in a `loop` until the
// permutation was NOT the identity, which is the only schedule under which A6
// cannot fire. The unsequenced baseline therefore reported 1000/1000 for every
// seed and every width by construction, and `measure_a6_prevention` asserted
// that result. Removing the rejection makes the baseline a measurement: the
// identity permutation is drawn with probability 1/w!, so the baseline rate is
// 1 - 1/w! and the generator can be checked against that closed form.
// Returns (completion order, precondition): the precondition is whether the
// underlying completion order differed from the issuance order at all. A run in
// which it did not is a run where there was nothing for the sequencer to
// prevent, and it must be counted, not discarded.
fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> (Vec<u64>, bool) {
    let mut sched: Vec<u64> = (0..w as u64).collect();

    for k in (1..w).rev() {
        let j = rng.below((k + 1) as u64) as usize;
        sched.swap(k, j);
    }
    let reordered = sched.iter().enumerate().any(|(p, &v)| v != p as u64);

    match mode {
        Mode::Unsequenced => (sched, reordered),

        Mode::Sequenced => {
            let mut completed = vec![false; w];
            let mut emitted: Vec<u64> = Vec::with_capacity(w);
            let mut next = 0usize;
            for &i in &sched {
                completed[i as usize] = true;
                while next < w && completed[next] {
                    emitted.push(next as u64);
                    next += 1;
                }
            }

            (emitted, reordered)
        }
    }
}

pub struct ExperimentResult {
    pub runs: usize,
    pub a6_positive: usize,
    /// Runs in which the completion order differed from the issuance order,
    /// i.e. runs in which reordering was there to be prevented.
    pub precondition_positive: usize,
}
impl ExperimentResult {
    pub fn a6_rate(&self) -> f64 {
        self.a6_positive as f64 / self.runs as f64
    }
    pub fn precondition_rate(&self) -> f64 {
        self.precondition_positive as f64 / self.runs as f64
    }
}

pub fn run_experiment(runs: usize, width: usize, mode: Mode, seed: u64) -> ExperimentResult {
    let mut rng = XorShift::new(seed);
    let io: Vec<u64> = (0..width as u64).collect();
    let mut pos = 0usize;
    let mut pre = 0usize;
    for _ in 0..runs {
        let (co, reordered) = run_once(width, mode, &mut rng);
        debug_assert_eq!(co.len(), width, "sequencer must emit every effect");
        if reordered {
            pre += 1;
        }
        if a6_witness(&io, &co) {
            pos += 1;
        }
    }
    ExperimentResult { runs, a6_positive: pos, precondition_positive: pre }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn measure_a6_prevention() {
        let runs = 1000;
        for width in [2usize, 4, 8] {
            let base = run_experiment(runs, width, Mode::Unsequenced, 0xC0FFEE + width as u64);
            let seq = run_experiment(runs, width, Mode::Sequenced, 0xC0FFEE + width as u64);
            println!(
                "width={}  reordering present = {}/{} ({:.1}%)   baseline A6 = {}/{} ({:.1}%)   L3 sequencer A6 = {}/{} ({:.1}%)",
                width,
                base.precondition_positive, base.runs, base.precondition_rate() * 100.0,
                base.a6_positive, base.runs, base.a6_rate() * 100.0,
                seq.a6_positive, seq.runs, seq.a6_rate() * 100.0,
            );
            // The unsequenced baseline fires exactly when the completion order
            // differed; that equality is what makes it a measurement of the
            // schedule rather than of the harness.
            assert_eq!(
                base.a6_positive, base.precondition_positive,
                "unsequenced baseline must fire exactly on the reordered runs"
            );
            assert_eq!(seq.a6_positive, 0, "sequencer must always prevent A6");
            assert!(
                base.precondition_positive > 0,
                "the generator never produced a reordered schedule: it cannot discriminate"
            );
        }

        // The discriminating cell. At width 2 the identity schedule is drawn
        // half the time, so a baseline that fires in EVERY run is evidence that
        // the generator, not the runtime, decided the outcome. This assertion
        // is the one that fails if the identity-rejection loop ever returns.
        let w2 = run_experiment(runs, 2, Mode::Unsequenced, 0xC0FFEE + 2);
        assert!(
            w2.precondition_positive < runs,
            "at width 2 the identity schedule must be reachable; got {}/{}",
            w2.precondition_positive, runs
        );
    }

    #[test]
    fn sequencer_emits_identity() {
        let mut rng = XorShift::new(42);
        for width in [2usize, 5, 16] {
            for _ in 0..200 {
                let (co, _) = run_once(width, Mode::Sequenced, &mut rng);
                let expect: Vec<u64> = (0..width as u64).collect();
                assert_eq!(co, expect);
            }
        }
    }
}
