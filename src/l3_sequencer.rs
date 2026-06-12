//! L3 commit-order sequencer: an **executable** realisation of the L3 model
//! verified in `verus-detector/src/lib_l3_sequencer.rs` (schedule-level) and
//! `verus-detector/src/lib_l3_exec.rs` (exec-mode data-structure invariant).
//!
//! The A_6 anomaly (tool-effect reordering) is an inversion between issuance
//! order `io` and observable commit order `co` within one operation's effect
//! batch. Theorem L3a prevents it by exclusion (strictly sequential issuance);
//! the SEQUENCER prevents it for genuinely concurrent completions: effects
//! complete in an arbitrary, adversarially reordered schedule, and the
//! sequencer externalizes effect k only once effects 0..k have all completed.
//!
//! Correspondence to the verified artifacts:
//!   * `Sequencer::complete` — the exec-mode pump of `lib_l3_exec.rs`
//!     (`L3Sequencer::complete`), whose invariant pins the emitted order to
//!     the identity prefix; here reimplemented dependency-free for std.
//!   * `a6_witness` — the catalogued A_6 predicate over (io, co): same
//!     multiset, |io| >= 2, co != io.
//!   * `Mode::Unsequenced` — the contrast baseline: externalize-on-completion,
//!     which exhibits A_6 under any non-identity completion schedule. Running
//!     the same adversarial schedules under both modes makes A_6 prevention
//!     **measurable**: the baseline produces witnesses; the sequencer none.
//!
//! As with the L2 pair (lib_l2_exec.rs / l2_causal.rs), the verified exec
//! artifact and this measured twin are two artifacts of one protocol; the
//! guarantee is the Verus theorem, this file corroborates it and exhibits
//! the unguarded baseline's anomaly (paper sec:l2-deployed framing).

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

/// Catalogued A_6 over one operation's effect batch: issuance order `io`
/// versus observable commit order `co`. Same multiset (here: both are
/// permutations of 0..w by construction), at least two effects, orders differ.
pub fn a6_witness(io: &[u64], co: &[u64]) -> bool {
    io.len() >= 2 && io.len() == co.len() && io != co
}

#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    /// Externalize each effect the moment it completes (unguarded baseline).
    Unsequenced,
    /// Commit-order sequencer: externalize effect k once 0..k complete.
    Sequenced,
}

/// One run: `w` effects issued as 0..w; the adversary completes them in a
/// random NON-IDENTITY permutation (re-drawn if identity, so the baseline's
/// schedule always genuinely reorders); returns the externalized order.
fn run_once(w: usize, mode: Mode, rng: &mut XorShift) -> Vec<u64> {
    // Adversarial completion schedule: a uniform non-identity permutation.
    let mut sched: Vec<u64> = (0..w as u64).collect();
    loop {
        // Fisher-Yates
        for k in (1..w).rev() {
            let j = rng.below((k + 1) as u64) as usize;
            sched.swap(k, j);
        }
        if sched.iter().enumerate().any(|(p, &v)| v != p as u64) {
            break; // non-identity guaranteed (w >= 2)
        }
    }
    match mode {
        Mode::Unsequenced => sched, // externalize-on-completion: co == schedule
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

    /// Mirrors measure_a3_prevention (l2_causal.rs): identical adversarial
    /// schedules drive both modes; the unguarded baseline must witness A_6 on
    /// every run (schedules are non-identity by construction), the sequencer
    /// on none. Self-asserting: a regression in either direction fails CI.
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

    /// Completeness guard: the sequencer emits every effect exactly once, in
    /// issuance order (prevention is not achieved by dropping effects).
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