//! A2 (phantom tool) at dispatch on the verified L4 dispatcher, against live
//! and snapshot resolution, over the same seeded churn (src/l4_registry.rs).
//!   cargo run --release --example l4_measure
fn main() {
    use agent_consistency_runtime::l4_registry::{run_experiment, Mode};
    for width in [2usize, 4, 16] {
        let seed = 0xBADC0DE + width as u64;
        let live = run_experiment(1000, width, Mode::LiveResolve, seed);
        let snap = run_experiment(1000, width, Mode::SnapshotResolve, seed);
        let val = run_experiment(1000, width, Mode::Validated, seed);
        println!(
            "width {width}: hazard {}/1000   live A2 {}/1000   snapshot A2 {}/1000   validated A2 {}/1000   validated refused {}   dispatched {}",
            live.hazard, live.a2_positive, snap.a2_positive, val.a2_positive, val.refused(), val.dispatched
        );
    }
}
