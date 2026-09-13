//! Replay recorded live sessions through the verified L2 runtime.
//!   cargo run --release --example l2_replay -- tools/live_l2/sessions
use std::{collections::BTreeMap, env, fs};

fn main() {
    let dir = env::args().nth(1).unwrap_or_else(|| "tools/live_l2/sessions".into());
    let mut per: BTreeMap<String, [u64; 5]> = BTreeMap::new(); // n, retracted, g_a3, u_a3, g_live
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
        let e = per.entry(s.model.clone()).or_insert([0; 5]);
        e[0] += 1;
        if s.retracted { e[1] += 1; }
        let (g_a3, g_live) = agent_consistency_runtime::l2_replay_lib::replay_guarded(&s);
        let (u_a3, _) = agent_consistency_runtime::l2_replay_lib::replay_unguarded(&s);
        if s.retracted {
            if g_a3 { e[2] += 1; }
            if u_a3 { e[3] += 1; }
        }
        if g_live { e[4] += 1; }
    }
    if files == 0 { eprintln!("no sessions found in {dir}"); std::process::exit(2); }
    println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>10}", "model", "n", "retracted", "verified A3", "baseline A3", "liveness");
    let (mut tn, mut tr, mut tg, mut tu, mut tl) = (0u64, 0u64, 0u64, 0u64, 0u64);
    for (m, e) in &per {
        println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>9.1}%", m, e[0], e[1],
                 format!("{}/{}", e[2], e[1]), format!("{}/{}", e[3], e[1]),
                 100.0 * e[4] as f64 / e[0].max(1) as f64);
        tn += e[0]; tr += e[1]; tg += e[2]; tu += e[3]; tl += e[4];
    }
    println!("{:<24} {:>5} {:>10} {:>12} {:>12} {:>9.1}%", "POOLED", tn, tr,
             format!("{tg}/{tr}"), format!("{tu}/{tr}"), 100.0 * tl as f64 / tn.max(1) as f64);
}
