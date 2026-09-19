//! 2026-09-16 round 28: A3 is an externalized operation with an aborted one
//! in its causal closure; the overruled form (a surviving dependent) is
//! printed next to it. The verified runtime releases under output commit and
//! reports what that costs: effects held, and retractions refused.
fn main() {
    use agent_consistency_runtime::l2_measure::run_experiment;
    for depth in [2usize, 3, 5] {
        let g = run_experiment(1000, depth, true);
        let u = run_experiment(1000, depth, false);
        println!(
            "depth {depth}: verified A3 {}/1000 (overruled form {}/1000)   unguarded A3 {}/1000 (overruled form {}/1000)",
            g.a3_hits, g.a3_unpropagated_hits, u.a3_hits, u.a3_unpropagated_hits
        );
        println!(
            "         verified: cascaded {}  refused {}  held {}  released {}/{} live  retractions refused {}/{}",
            g.cascaded, g.refused, g.held, g.released, g.live, g.retractions_refused, g.retractions
        );
    }
}
