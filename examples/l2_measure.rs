fn main() {
    for depth in [2usize, 3, 5] {
        let g = agent_consistency_runtime::l2_measure::run_experiment(1000, depth, true);
        let u = agent_consistency_runtime::l2_measure::run_experiment(1000, depth, false);
        println!(
            "depth {depth}: verified {}/1000   unguarded {}/1000   cascaded {}   refused {}",
            g.a3_hits, u.a3_hits, g.cascaded, g.refused
        );
    }
}
