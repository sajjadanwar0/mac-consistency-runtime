// examples/l3_deploy.rs  —  place under mac-consistency-runtime/examples/
// Runnable entry point that exercises the crate's own L3 sequencer as a
// deployed runtime. Run with:  cargo run --example l3_deploy
use agent_consistency_runtime::l3_sequencer::{run_experiment, Mode};

fn main() {
    let runs = 1000;
    println!("L3 commit-order sequencer (deployed runtime) — A6 prevention");
    for width in [2usize, 4, 8] {
        let base = run_experiment(runs, width, Mode::Unsequenced, 0xC0FFEE + width as u64);
        let seq  = run_experiment(runs, width, Mode::Sequenced,   0xC0FFEE + width as u64);
        println!(
            "  width={:<2}  baseline A6 = {}/{} ({:.0}%)   L3 sequencer A6 = {}/{} ({:.0}%)",
            width,
            base.a6_positive, base.runs, base.a6_rate() * 100.0,
            seq.a6_positive,  seq.runs,  seq.a6_rate() * 100.0,
        );
    }
}