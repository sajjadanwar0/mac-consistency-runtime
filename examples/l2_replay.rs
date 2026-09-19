//! Replay recorded live sessions through the verified L2 runtime and the two
//! release-at-commit baselines.
//!   cargo run --release --example l2_replay -- tools/live_l2/sessions
//!
//! 2026-09-16 round 28: A3 is the executor's effects out while its plan is
//! retracted; "released" is the share of sessions whose executor's effects
//! left the verified runtime (OVERRULED: "liveness", a surviving executor).
//! 2026-09-19 round 33: a third arm, the superseded design (release at commit
//! AND cascade), scored under both predicates; `REPLAY ...` lines are the
//! machine-readable record the README is checked against.
use std::{collections::BTreeMap, env, fs};

fn main() {
    let dir = env::args().nth(1).unwrap_or_else(|| "tools/live_l2/sessions".into());
    // n, retracted, verified a3, baseline a3, verified released, cascade a3, cascade overruled a3
    let mut per: BTreeMap<String, [u64; 7]> = BTreeMap::new();
    let mut files = 0usize;
    let entries = match fs::read_dir(&dir) {
        Ok(e) => e,
        Err(e) => { eprintln!("cannot read {dir}: {e}"); std::process::exit(2); }
    };
    for ent in entries.flatten() {
        let p = ent.path();
        if p.extension().map_or(true, |x| x != "json") { continue; }
        let txt = match fs::read_to_string(&p) { Ok(t) => t, Err(_) => continue };
        let v: serde_json::Value = match serde_json::from_str(&txt) { Ok(v) => v, Err(_) => continue };
        let s = match agent_consistency_runtime::l2_replay_lib::parse(&v) { Some(s) => s, None => continue };
        files += 1;
        let e = per.entry(s.model.clone()).or_insert([0; 7]);
        e[0] += 1;
        if s.retracted { e[1] += 1; }
        let (g_a3, g_released) = agent_consistency_runtime::l2_replay_lib::replay_guarded(&s);
        let (u_a3, _) = agent_consistency_runtime::l2_replay_lib::replay_unguarded(&s);
        let (c_a3, c_old, _) = agent_consistency_runtime::l2_replay_lib::replay_cascade(&s);
        if s.retracted {
            if g_a3 { e[2] += 1; }
            if u_a3 { e[3] += 1; }
            if c_a3 { e[5] += 1; }
            if c_old { e[6] += 1; }
        }
        if g_released { e[4] += 1; }
    }
    if files == 0 { eprintln!("no sessions found in {dir}"); std::process::exit(2); }
    println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>12} {:>18} {:>10}", "model", "n", "retracted",
             "verified A3", "baseline A3", "cascade A3", "cascade overruled", "released");
    let mut tot = [0u64; 7];
    for (m, e) in &per {
        println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>12} {:>18} {:>9.1}%", m, e[0], e[1],
                 format!("{}/{}", e[2], e[1]), format!("{}/{}", e[3], e[1]),
                 format!("{}/{}", e[5], e[1]), format!("{}/{}", e[6], e[1]),
                 100.0 * e[4] as f64 / e[0].max(1) as f64);
        println!("REPLAY model={} n={} retracted={} verified_a3={} baseline_a3={} cascade_a3={} cascade_overruled={} released={}",
                 m, e[0], e[1], e[2], e[3], e[5], e[6], e[4]);
        for i in 0..7 { tot[i] += e[i]; }
    }
    println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>12} {:>18} {:>9.1}%", "POOLED", tot[0], tot[1],
             format!("{}/{}", tot[2], tot[1]), format!("{}/{}", tot[3], tot[1]),
             format!("{}/{}", tot[5], tot[1]), format!("{}/{}", tot[6], tot[1]),
             100.0 * tot[4] as f64 / tot[0].max(1) as f64);
    println!("REPLAY model=POOLED n={} retracted={} verified_a3={} baseline_a3={} cascade_a3={} cascade_overruled={} released={}",
             tot[0], tot[1], tot[2], tot[3], tot[5], tot[6], tot[4]);
}
