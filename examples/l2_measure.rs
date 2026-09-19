//! 2026-09-19 round 33: three arms on the same seeded schedules.
//!   verified   l2_exec::L2Runtime       cascades, releases under output commit
//!   unguarded  l2_unguarded             releases at commit, does not cascade
//!   cascade    l2_cascade               releases at commit AND cascades: the
//!                                       superseded design of rounds <= 22
//! Two A3 predicates are printed for every arm: the current one (an operation
//! whose effects are out while an operation in its causal closure is aborted)
//! and the overruled one (a surviving dependent). Both read flags the runtime
//! under test sets for itself, so `exposed` is printed beside them: effects
//! out although the review asked to withdraw their basis. It reads no flag.
//! The `L2 ...` lines are the machine-readable record the README is checked
//! against. OVERRULED (rounds 28-32): two arms, on which the two predicates
//! could not disagree.
fn main() {
    use agent_consistency_runtime::l2_measure::{run_experiment, Arm};
    for depth in [2usize, 3, 5] {
        let v = run_experiment(1000, depth, Arm::Verified);
        let u = run_experiment(1000, depth, Arm::Unguarded);
        let c = run_experiment(1000, depth, Arm::Cascade);
        println!(
            "depth {depth}: A3, effects out on a retracted basis   verified {}/1000   unguarded {}/1000   cascade {}/1000",
            v.a3_hits, u.a3_hits, c.a3_hits
        );
        println!(
            "         overruled A3, a surviving dependent    verified {}/1000   unguarded {}/1000   cascade {}/1000",
            v.a3_unpropagated_hits, u.a3_unpropagated_hits, c.a3_unpropagated_hits
        );
        println!(
            "         exposed effects (in scenarios)          verified {} ({})   unguarded {} ({})   cascade {} ({})",
            v.exposed, v.exposed_scenarios, u.exposed, u.exposed_scenarios, c.exposed, c.exposed_scenarios
        );
        println!(
            "         relabeled after release                 verified {}   unguarded {}   cascade {}",
            v.relabeled, u.relabeled, c.relabeled
        );
        println!(
            "         verified: cascaded {}  refused {}  held {}  released {}/{} live  retractions refused {}/{}",
            v.cascaded, v.refused, v.held, v.released, v.live, v.retractions_refused, v.retractions
        );
        for s in [&v, &u, &c] {
            println!(
                "L2 depth={} arm={} a3={} a3_overruled={} exposed={} exposed_scenarios={} relabeled={} cascaded={} refused={} held={} released={} live={} retractions={} retractions_refused={}",
                s.depth, s.arm.label(), s.a3_hits, s.a3_unpropagated_hits, s.exposed, s.exposed_scenarios,
                s.relabeled, s.cascaded, s.refused, s.held, s.released, s.live, s.retractions, s.retractions_refused
            );
        }
    }
}
