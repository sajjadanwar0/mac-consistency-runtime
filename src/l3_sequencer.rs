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

fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> Vec<u64> {
    let mut sched: Vec<u64> = (0..w as u64).collect();

    loop {
        for k in (1..w).rev() {
            let j = rng.below((k + 1) as u64) as usize;
            sched.swap(k, j);
        }

        if sched.iter().enumerate().any(|(p, &v)| v != p as u64) {
            break;
        }
    }
    match mode {
        Mode::Unsequenced => sched,

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

            emitted
        }
    }
}

pub struct ExperimentResult {
    pub runs: usize,
    pub a6_positive: usize,
}
impl ExperimentResult {
    pub fn a6_rate(&self) -> f64 {
        self.a6_positive as f64 / self.runs as f64
    }
}

pub fn run_experiment(runs: usize, width: usize, mode: Mode, seed: u64) -> ExperimentResult {
    let mut rng = XorShift::new(seed);
    let io: Vec<u64> = (0..width as u64).collect();
    let mut pos = 0usize;
    for _ in 0..runs {
        let co = run_once(width, mode, &mut rng);
        debug_assert_eq!(co.len(), width, "sequencer must emit every effect");
        if a6_witness(&io, &co) {
            pos += 1;
        }
    }
    ExperimentResult { runs, a6_positive: pos }
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
                "width={}  baseline A6 = {}/{} ({:.0}%)   L3 sequencer A6 = {}/{} ({:.0}%)",
                width,
                base.a6_positive, base.runs, base.a6_rate() * 100.0,
                seq.a6_positive, seq.runs, seq.a6_rate() * 100.0,
            );
            assert_eq!(base.a6_positive, runs, "baseline must always admit A6 (non-identity schedules)");
            assert_eq!(seq.a6_positive, 0, "sequencer must always prevent A6");
        }
    }

    #[test]
    fn sequencer_emits_identity() {
        let mut rng = XorShift::new(42);
        for width in [2usize, 5, 16] {
            for _ in 0..200 {
                let co = run_once(width, Mode::Sequenced, &mut rng);
                let expect: Vec<u64> = (0..width as u64).collect();
                assert_eq!(co, expect);
            }
        }
    }
}