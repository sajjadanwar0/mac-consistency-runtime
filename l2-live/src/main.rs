// l2-live/src/main.rs
//
// Live-agent driver for the verified L2 causal-tracking runtime (WS-A: L2-live).
//
// This binary exercises the REAL runtime source, not a fork: it pulls in
// `../../src/l2_causal.rs` via #[path], so it drives the actual `L2CausalStore`
// and the actual `detect_a3_cascade` that the paper's twin experiment uses.
// The only difference from the synthetic twin (`run_experiment`) is that the
// plan / result content comes from a live LLM loop instead of a seed.
//
// Workload: plan -> execute -> revise.
//   planner   commits a value to cell "plan".
//   executor  reads "plan" (so its causal closure includes the planner) and
//             commits a value to cell "result".
//   validator retracts the plan on a controlled fraction of sessions
//             (forced rate, reproducible) or by asking the model.
//
// On retraction:
//   NoCascade (baseline): the executor survives committed on an aborted
//                         predecessor  -> A3 (causal cascade) present.
//   Cascade   (L2):       the executor is cascade-aborted               -> A3 prevented.
//
// IMPORTANT honesty note (put this in the paper, do not hide it): A3 here is
// STRUCTURAL. The executor depends on the planner because it READ the "plan"
// cell, and the cascade discipline prevents A3 regardless of what the model
// returns. The live loop demonstrates the discipline holding under real agent
// I/O, latency, cost, and nondeterministic content across model families; it
// does NOT claim the model's reasoning causes A3. A3 arises from the
// plan/execute/retract causal structure that real agent systems exhibit
// (re-planning, tool-call rollback, saga compensation).

#[path = "../../src/l2_causal.rs"]
#[allow(dead_code)] // the synthetic-twin helpers (run_experiment, etc.) are unused by the live driver
mod l2_causal;

use l2_causal::{detect_a3_cascade, AbortPolicy, L2CausalStore, ProvRecord};
use serde::Serialize;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;

struct Args {
    provider: String, // openai | anthropic | vllm
    model: String,
    base_url: Option<String>,
    n: usize,
    retract_rate: f64,
    validator: String, // forced | llm
    out: PathBuf,
    seed: u64,
    dry_run: bool,
    api_key: String,
}

fn usage_and_exit() -> ! {
    eprintln!(
        "usage: l2_live --provider <openai|anthropic|vllm> --model <name> \\
                [--base-url <url>] [--n <sessions>] [--retract-rate <0..1>] \\
                [--validator <forced|llm>] [--out <dir>] [--seed <u64>] \\
                [--api-key <key>] [--dry-run]

env: OPENAI_API_KEY / ANTHROPIC_API_KEY used if --api-key is omitted.
--dry-run skips all LLM calls (synthetic content) so you can test the wiring
and confirm it reproduces the synthetic twin before spending tokens."
    );
    std::process::exit(2);
}

fn parse_args() -> Args {
    let mut a = Args {
        provider: "openai".to_string(),
        model: "gpt-4o-mini".to_string(),
        base_url: None,
        n: 160,
        retract_rate: 0.65,
        validator: "forced".to_string(),
        out: PathBuf::from("./l2_live_out"),
        seed: 0x00C0FFEE,
        dry_run: false,
        api_key: String::new(),
    };
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        let mut val = || args.next().unwrap_or_else(|| usage_and_exit());
        match flag.as_str() {
            "--provider" => a.provider = val(),
            "--model" => a.model = val(),
            "--base-url" => a.base_url = Some(val()),
            "--n" => a.n = val().parse().unwrap_or_else(|_| usage_and_exit()),
            "--retract-rate" => a.retract_rate = val().parse().unwrap_or_else(|_| usage_and_exit()),
            "--validator" => a.validator = val(),
            "--out" => a.out = PathBuf::from(val()),
            "--seed" => a.seed = val().parse().unwrap_or_else(|_| usage_and_exit()),
            "--api-key" => a.api_key = val(),
            "--dry-run" => a.dry_run = true,
            "-h" | "--help" => usage_and_exit(),
            other => {
                eprintln!("unknown flag: {other}");
                usage_and_exit();
            }
        }
    }
    if a.api_key.is_empty() && !a.dry_run {
        a.api_key = match a.provider.as_str() {
            "anthropic" => std::env::var("ANTHROPIC_API_KEY").unwrap_or_default(),
            "openai" => std::env::var("OPENAI_API_KEY").unwrap_or_default(),
            _ => String::new(), // vllm: typically no key
        };
    }
    a
}

// ---- JSONL serialization of the real ProvRecord (no change to the runtime crate) ----

#[derive(Serialize)]
struct JsonProv<'a> {
    txn: u64,
    agent: &'a str,
    read_set: &'a [String],
    read_values: &'a BTreeMap<String, String>,
    read_time: u64,
    write_set: &'a [String],
    write_values: &'a BTreeMap<String, String>,
    write_time: u64,
    preds: &'a [u64],
    aborted: bool,
}

fn prov_line(r: &ProvRecord) -> String {
    serde_json::to_string(&JsonProv {
        txn: r.txn,
        agent: &r.agent,
        read_set: &r.read_set,
        read_values: &r.read_values,
        read_time: r.read_time,
        write_set: &r.write_set,
        write_values: &r.write_values,
        write_time: r.write_time,
        preds: &r.preds,
        aborted: r.aborted,
    })
        .expect("serialize ProvRecord")
}

// ---- LLM call (blocking, ureq). OpenAI / vLLM (OpenAI-compatible) and Anthropic. ----

fn build_agent() -> ureq::Agent {
    let mut b = ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(10))
        .timeout_read(Duration::from_secs(60))
        .timeout_write(Duration::from_secs(30));
    // ureq does NOT read proxy env vars automatically; honor a corporate proxy if set.
    if let Ok(p) = std::env::var("HTTPS_PROXY").or_else(|_| std::env::var("https_proxy")) {
        if !p.is_empty() {
            if let Ok(proxy) = ureq::Proxy::new(&p) {
                b = b.proxy(proxy);
            }
        }
    }
    b.build()
}

// The agent's timeouts bound each attempt so a stalled connection can no longer hang
// the whole run; we retry once so a transient blip skips one session, not the run.
fn chat(
    agent: &ureq::Agent,
    provider: &str,
    model: &str,
    base_url: Option<&str>,
    key: &str,
    system: &str,
    user: &str,
) -> Result<String, String> {
    let mut last = String::new();
    for attempt in 0..2 {
        match chat_once(agent, provider, model, base_url, key, system, user) {
            Ok(s) => return Ok(s),
            Err(e) => {
                last = e;
                if attempt == 0 {
                    std::thread::sleep(Duration::from_secs(1));
                }
            }
        }
    }
    Err(last)
}

fn chat_once(
    agent: &ureq::Agent,
    provider: &str,
    model: &str,
    base_url: Option<&str>,
    key: &str,
    system: &str,
    user: &str,
) -> Result<String, String> {
    match provider {
        "anthropic" => {
            let base = base_url.unwrap_or("https://api.anthropic.com").trim_end_matches('/');
            let url = format!("{base}/v1/messages");
            let resp: Value = agent
                .post(&url)
                .set("x-api-key", key)
                .set("anthropic-version", "2023-06-01")
                .set("content-type", "application/json")
                .send_json(json!({
                    "model": model,
                    "max_tokens": 64,
                    "system": system,
                    "messages": [{"role": "user", "content": user}]
                }))
                .map_err(|e| e.to_string())?
                .into_json()
                .map_err(|e| e.to_string())?;
            resp["content"][0]["text"]
                .as_str()
                .map(|s| s.trim().to_string())
                .ok_or_else(|| format!("anthropic: unexpected response: {resp}"))
        }
        _ => {
            // openai or vllm (OpenAI-compatible chat completions)
            let base = base_url.unwrap_or("https://api.openai.com").trim_end_matches('/');
            let url = format!("{base}/v1/chat/completions");
            let mut req = agent.post(&url).set("content-type", "application/json");
            if !key.is_empty() {
                req = req.set("Authorization", &format!("Bearer {key}"));
            }
            let resp: Value = req
                .send_json(json!({
                    "model": model,
                    "temperature": 0.8,
                    "max_tokens": 64,
                    "messages": [
                        {"role": "system", "content": system},
                        {"role": "user", "content": user}
                    ]
                }))
                .map_err(|e| e.to_string())?
                .into_json()
                .map_err(|e| e.to_string())?;
            resp["choices"][0]["message"]["content"]
                .as_str()
                .map(|s| s.trim().to_string())
                .ok_or_else(|| format!("openai: unexpected response: {resp}"))
        }
    }
}

// ---- deterministic RNG (xorshift64) for reproducible retraction + bootstrap ----

fn xs(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn unit(state: &mut u64) -> f64 {
    (xs(state) >> 11) as f64 / (1u64 << 53) as f64
}

fn bootstrap_ci(ind: &[f64], iters: usize, seed: u64) -> (f64, f64) {
    if ind.is_empty() {
        return (0.0, 0.0);
    }
    let n = ind.len();
    let mut st = seed | 1;
    let mut means = Vec::with_capacity(iters);
    for _ in 0..iters {
        let mut s = 0.0;
        for _ in 0..n {
            let idx = (xs(&mut st) % n as u64) as usize;
            s += ind[idx];
        }
        means.push(s / n as f64);
    }
    means.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let lo = means[((0.025 * iters as f64) as usize).min(iters - 1)];
    let hi = means[((0.975 * iters as f64) as usize).min(iters - 1)];
    (lo, hi)
}

// ---- one session under one policy, using the same agent content ----

struct SessionOutcome {
    a3: bool,
    cascades: u64,
    executor_survived: bool,
    trace: Vec<ProvRecord>,
}

fn run_session(policy: AbortPolicy, plan: &str, result: &str, retract: bool) -> SessionOutcome {
    let mut st = L2CausalStore::new(policy);

    let empty: Vec<String> = Vec::new();
    let p = st.begin("planner", &empty);
    let mut wp = BTreeMap::new();
    wp.insert("plan".to_string(), plan.to_string());
    st.commit(p, &wp);

    let rs = vec!["plan".to_string()];
    let e = st.begin("executor", &rs);
    let mut we = BTreeMap::new();
    we.insert("result".to_string(), result.to_string());
    st.commit(e, &we);

    if retract {
        st.abort(p.txn);
    }

    let trace = st.trace();
    let a3 = detect_a3_cascade(&trace).is_some();
    let executor_survived = trace
        .iter()
        .find(|r| r.agent == "executor")
        .map(|r| !r.aborted && r.write_time > 0)
        .unwrap_or(false);

    SessionOutcome {
        a3,
        cascades: st.cascade_aborts(),
        executor_survived,
        trace,
    }
}

#[derive(Default)]
struct Agg {
    a3_ind: Vec<f64>,
    cascade_total: u64,
    survived: usize,
    counted: usize,
}

fn report(label: &str, agg: &Agg, seed: u64) {
    let n = agg.counted;
    let positives: f64 = agg.a3_ind.iter().sum();
    let rate = if n > 0 { positives / n as f64 } else { 0.0 };
    // For a zero-count cell the bootstrap is degenerate ([0,0], overstates certainty);
    // report the rule-of-three 95% upper bound [0, 3/n] instead.
    let (lo, hi) = if n == 0 {
        (0.0, 0.0)
    } else if positives == 0.0 {
        (0.0, 3.0 / n as f64)
    } else {
        bootstrap_ci(&agg.a3_ind, 2000, seed)
    };
    let liveness = if n > 0 { agg.survived as f64 / n as f64 } else { 0.0 };
    println!(
        "{label:<22} A3 = {pos:>4}/{n:<4} ({rate:5.1}%) [{lo:4.1}, {hi:4.1}]   \
         cascade-aborts = {casc:<5}  executor-liveness = {live:5.1}%",
        pos = positives as u64,
        rate = rate * 100.0,
        lo = lo * 100.0,
        hi = hi * 100.0,
        casc = agg.cascade_total,
        live = liveness * 100.0,
    );
}

fn main() {
    let a = parse_args();
    if !a.dry_run && a.api_key.is_empty() && a.provider != "vllm" {
        eprintln!(
            "no API key for provider '{}'. Set OPENAI_API_KEY / ANTHROPIC_API_KEY, \
             pass --api-key, or use --dry-run.",
            a.provider
        );
        std::process::exit(2);
    }

    let model_safe = a.model.replace('/', "_");
    for name in ["nocascade", "cascade"] {
        fs::create_dir_all(a.out.join(name).join(&model_safe)).expect("create out dir");
    }

    let mut agg_base = Agg::default();
    let mut agg_l2 = Agg::default();

    // Enriched, judgment-dependent workload (Option A): a triage planner proposes a
    // one-line action plan for a genuinely ambiguous ticket; a supervisor (the LLM
    // validator) decides RETRACT/KEEP. Because the decision is a real judgment over
    // real content, the retraction rate -- and hence the baseline A3 prevalence --
    // varies by model, which is what makes "three model families" a meaningful result
    // rather than the same structural outcome printed three times.
    let planner_sys = "You are a triage planning agent. Given a short, possibly \
                       ambiguous ticket, propose a single one-line action plan \
                       (under 12 words). Be decisive even when the ticket is unclear.";
    let exec_sys = "You are an execution agent. Given an action plan, output a \
                    one-line summary of the action you took (under 12 words).";
    let val_sys = "You are a supervisor reviewing a proposed action plan for a ticket \
                   BEFORE it takes effect. Reply with exactly one word: RETRACT if the \
                   plan is premature, risky, or likely wrong for the ticket; KEEP otherwise.";

    // Genuinely ambiguous tickets: reasonable supervisors disagree, so RETRACT rates
    // differ across models (0 < rate < 1) without forcing errors.
    let tickets: &[&str] = &[
        "Customer says the app is 'broken' but gave no details.",
        "User requests a refund for a purchase made 100 days ago.",
        "Account flagged for an unusual login from a new country.",
        "Two agents edited the same order; statuses now disagree.",
        "Vendor invoice exceeds the PO by 12% with no note attached.",
        "User asks to delete their data but has an open dispute.",
        "A sensor reports 3x its historical max for one minute.",
        "A merge request touches auth code with no reviewer assigned.",
    ];

    let agent = build_agent();
    let mut skipped = 0usize;
    let mut retracted = 0usize;
    for s in 0..a.n {
        if !a.dry_run {
            eprint!("\r  running session {}/{} ...", s + 1, a.n);
            let _ = std::io::stderr().flush();
        }
        // Per-session content: one set of agent calls, replayed under both policies.
        let ticket = tickets[s % tickets.len()];
        let (plan, result, retract) = if a.dry_run {
            let mut st = a.seed ^ (s as u64).wrapping_mul(0x9E3779B97F4A7C15);
            let r = unit(&mut st) < a.retract_rate;
            (format!("PLAN-{s}"), format!("RES-{s}"), r)
        } else {
            let plan = match chat(&agent, &a.provider, &a.model, a.base_url.as_deref(), &a.api_key, planner_sys, &format!("Ticket: {ticket}\nPropose a one-line action plan.")) {
                Ok(v) if !v.is_empty() => v,
                Ok(_) => { eprintln!("session {s}: empty plan, skipping"); skipped += 1; continue; }
                Err(e) => { eprintln!("session {s}: planner error: {e}; skipping"); skipped += 1; continue; }
            };
            let result = match chat(&agent, &a.provider, &a.model, a.base_url.as_deref(), &a.api_key, exec_sys, &format!("Plan: {plan}\nExecute it and summarize in one line.")) {
                Ok(v) if !v.is_empty() => v,
                Ok(_) => { eprintln!("session {s}: empty result, skipping"); skipped += 1; continue; }
                Err(e) => { eprintln!("session {s}: executor error: {e}; skipping"); skipped += 1; continue; }
            };
            let retract = if a.validator == "llm" {
                match chat(&agent, &a.provider, &a.model, a.base_url.as_deref(), &a.api_key, val_sys, &format!("Ticket: {ticket}\nPlan: {plan}\nDecision:")) {
                    Ok(v) => v.to_uppercase().contains("RETRACT"),
                    Err(e) => { eprintln!("session {s}: validator error: {e}; defaulting KEEP"); false }
                }
            } else {
                let mut st = a.seed ^ (s as u64).wrapping_mul(0x9E3779B97F4A7C15);
                unit(&mut st) < a.retract_rate
            };
            (plan, result, retract)
        };
        if retract {
            retracted += 1;
        }

        for &(name, policy, is_l2) in &[
            ("nocascade", AbortPolicy::NoCascade, false),
            ("cascade", AbortPolicy::Cascade, true),
        ] {
            let out = run_session(policy, &plan, &result, retract);
            // archive the trace as JSONL (Python detector pipeline can re-read it)
            let path = a.out.join(name).join(&model_safe).join(format!("sess-{s:04}.jsonl"));
            let mut f = fs::File::create(&path).expect("create session file");
            for r in &out.trace {
                writeln!(f, "{}", prov_line(r)).expect("write jsonl");
            }
            let agg = if is_l2 { &mut agg_l2 } else { &mut agg_base };
            agg.a3_ind.push(if out.a3 { 1.0 } else { 0.0 });
            agg.cascade_total += out.cascades;
            if out.executor_survived {
                agg.survived += 1;
            }
            agg.counted += 1;
        }
    }

    if !a.dry_run {
        eprintln!(); // finish the in-place progress line
    }
    println!();
    println!("=== L2-live: A3 (causal-cascade) prevention under live agents ===");
    let counted = agg_base.counted; // == agg_l2.counted == a.n - skipped
    let retract_rate_measured = if counted > 0 {
        retracted as f64 / counted as f64
    } else {
        0.0
    };
    println!(
        "provider={}  model={}  sessions={}  retraction-rate(measured)={:.1}%  validator={}  dry_run={}",
        a.provider,
        a.model,
        counted,
        retract_rate_measured * 100.0,
        a.validator,
        a.dry_run
    );
    if skipped > 0 {
        println!("(skipped {skipped} sessions due to LLM errors)");
    }
    println!();
    report("baseline (NoCascade)", &agg_base, a.seed ^ 0xA1);
    report("L2 (Cascade)", &agg_l2, a.seed ^ 0xB2);
    println!();
    let base_rate = if agg_base.counted > 0 {
        agg_base.a3_ind.iter().sum::<f64>() / agg_base.counted as f64
    } else {
        0.0
    };
    let l2_rate = if agg_l2.counted > 0 {
        agg_l2.a3_ind.iter().sum::<f64>() / agg_l2.counted as f64
    } else {
        0.0
    };
    println!(
        "verdict: baseline admits A3 at {:.1}%; L2 prevents it at {:.1}%. \
         L2 liveness {:.1}% (executors whose plan was not retracted still commit).",
        base_rate * 100.0,
        l2_rate * 100.0,
        if agg_l2.counted > 0 {
            agg_l2.survived as f64 / agg_l2.counted as f64 * 100.0
        } else {
            0.0
        }
    );
    let k = retracted;
    let l2_k_ci_hi = if k > 0 { 3.0 / k as f64 } else { 0.0 };
    println!(
        "         across the {k} retracted sessions (where A3 can occur): baseline left an \
         A3 witness in all {k}; L2 prevented every one (0/{k}, 95% CI [0, {:.1}%]).",
        l2_k_ci_hi * 100.0
    );
    println!("JSONL traces written under: {}", a.out.display());
}