// l3-probe/src/main.rs
//
// NON-VACUITY GATE for L3-live (A6: tool-effect reordering, co != io).
//
// Purpose. Before spending days building a full l3-live driver, answer one
// question with real models: when an agent issues an ORDERED sequence of side
// effects and the runtime commits them in COMPLETION order (the un-disciplined
// baseline an L3 sequencer would fix), do the effects actually land out of
// intended order at a meaningful rate? If yes, A6 is non-vacuous live and the
// full driver is justified. If the rate is ~0, L3-live on this workload would
// be the vacuous, weak result we want to avoid -- keep L3 model-only.
//
// Why this is a faithful probe and NOT staged (put this reasoning in the paper):
//   * The reordering is produced by REAL concurrency and REAL latency, not by
//     injected sleeps. Each step's effect is a real provider call dispatched
//     fire-and-forget; the OS scheduler and real API/inference latency decide
//     completion order. We choose nothing about the latencies.
//   * The intended order io = [0, 1, ..., N-1] is the order the agent ISSUES the
//     effects in a sequential loop. The realistic inter-step gap between
//     dispatches is the latency of a real blocking "advance" call (the agent
//     reasoning to reach the next step) -- so order is usually preserved and
//     only OCCASIONALLY violated, which is exactly the regime where A6 is a
//     real, non-trivial concern (not the trivial all-at-once batch case, where
//     parallel calls are anyway semantically unordered).
//   * The single design choice is: commit effects in completion order with no
//     ordering enforced. That IS the baseline an L3 sequencer disciplines; the
//     probe measures whether that baseline reorders. The verified prevention
//     witness a6_witness is reused verbatim from the runtime (#[path] below).
//
// Honest scope of the estimate. Effects here are HOMOGENEOUS (a uniform provider
// call; latency variance comes only from real API/inference jitter and the
// model's own variable output length). Real agent tools are HETEROGENEOUS (a
// fast cache read vs a slow external API vs an LLM sub-call), which reorders
// MORE. So this probe is a CONSERVATIVE (lower-bound) estimate of A6: a non-zero
// rate here means heterogeneous tools reorder at least this much; a zero rate
// here means L3-live on THIS workload is vacuous (heterogeneous tools might
// still reorder, but that is a different, harder experiment to make non-staged).
//
// Reuse: a6_witness comes from the actual runtime source, the same predicate the
// L3 sequencer and the paper use. The synthetic run_experiment/Mode helpers in
// that file (the seed-driven scheduler) are deliberately NOT used here -- that
// scheduler is the staged mechanism this probe replaces with real latency.

#[path = "../../src/l3_sequencer.rs"]
#[allow(dead_code)] // only a6_witness is used; the synthetic-twin helpers are unused
mod l3_sequencer;

use l3_sequencer::a6_witness;
use serde::Serialize;
use serde_json::{json, Value};
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

struct Args {
    provider: String, // openai | anthropic | vllm
    model: String,
    base_url: Option<String>,
    n: usize,
    width: usize,
    out: PathBuf,
    seed: u64,
    dry_run: bool,
    api_key: String,
}

fn usage_and_exit() -> ! {
    eprintln!(
        "usage: l3_probe --provider <openai|anthropic|vllm> --model <name> \\
                [--base-url <url>] [--n <sessions>] [--width <effects-per-session>] \\
                [--out <dir>] [--seed <u64>] [--api-key <key>] [--dry-run]

env: OPENAI_API_KEY / ANTHROPIC_API_KEY used if --api-key is omitted.
--dry-run skips all LLM calls and uses synthetic per-effect timing purely to
exercise the harness (reorder detection, trace writing). The A6 number printed
under --dry-run is NOT a measurement; it only proves the pipeline works.

cost: each session issues 2*width provider calls (width blocking 'advance' calls
that set the realistic inter-step gap + width fire-and-forget effect calls).
n=30 width=5 is ~300 calls (cents on gpt-4o-mini; free on a local model)."
    );
    std::process::exit(2);
}

fn parse_args() -> Args {
    let mut a = Args {
        provider: "openai".to_string(),
        model: "gpt-4o-mini".to_string(),
        base_url: None,
        n: 30,
        width: 5,
        out: PathBuf::from("./l3_probe_out"),
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
            "--width" => a.width = val().parse().unwrap_or_else(|_| usage_and_exit()),
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
    if a.width < 2 {
        eprintln!("--width must be >= 2 (A6 is undefined for fewer than two effects)");
        std::process::exit(2);
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

// ---- LLM call (blocking, ureq). OpenAI / vLLM (OpenAI-compatible) and Anthropic. ----
// (identical scaffolding to l2-live: bounded timeouts + one retry + proxy support)

fn build_agent() -> ureq::Agent {
    let mut b = ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(10))
        .timeout_read(Duration::from_secs(60))
        .timeout_write(Duration::from_secs(30));
    if let Ok(p) = std::env::var("HTTPS_PROXY").or_else(|_| std::env::var("https_proxy")) {
        if !p.is_empty() {
            if let Ok(proxy) = ureq::Proxy::new(&p) {
                b = b.proxy(proxy);
            }
        }
    }
    b.build()
}

fn chat(
    agent: &ureq::Agent,
    provider: &str,
    model: &str,
    base_url: Option<&str>,
    key: &str,
    system: &str,
    user: &str,
    max_tokens: u32,
) -> Result<String, String> {
    let mut last = String::new();
    for attempt in 0..2 {
        match chat_once(agent, provider, model, base_url, key, system, user, max_tokens) {
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
    max_tokens: u32,
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
                    "max_tokens": max_tokens,
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
                    "max_tokens": max_tokens,
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

// ---- deterministic RNG (xorshift64), only for dry-run synthetic timing + bootstrap ----

fn xs(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
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

// number of out-of-order pairs in the completion order relative to io = 0..N
fn inversions(co: &[u64]) -> usize {
    let mut inv = 0usize;
    for i in 0..co.len() {
        for j in (i + 1)..co.len() {
            if co[i] > co[j] {
                inv += 1;
            }
        }
    }
    inv
}

// ---- one session: a sequential agent loop with fire-and-forget async effects ----

struct SessionTrace {
    io: Vec<u64>,
    co: Vec<u64>,
    timings: Vec<(u64, u128, u128)>, // (step, dispatch_ms, complete_ms)
}

#[allow(clippy::too_many_arguments)]
fn run_session(
    agent: &ureq::Agent,
    provider: &str,
    model: &str,
    base_url: Option<&str>,
    key: &str,
    task: &str,
    width: usize,
    dry_run: bool,
    seed: u64,
) -> SessionTrace {
    let start = Instant::now();
    let co: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(Vec::with_capacity(width)));
    let timings: Arc<Mutex<Vec<(u64, u128, u128)>>> = Arc::new(Mutex::new(Vec::with_capacity(width)));
    let mut handles = Vec::with_capacity(width);

    let advance_sys = "You are an agent executing an ordered plan, one step at a time. \
                       Reply with exactly the single word: READY";
    let effect_sys = "You are a side-effect executor. Perform the described step and reply \
                      with a one-line confirmation of the action taken.";

    for k in 0..width as u64 {
        // (1) BLOCKING advance: the agent reasoning to reach step k. Its real latency is
        //     the inter-step gap that staggers effect dispatches (so order is usually,
        //     not always, preserved). In dry-run, a tiny fixed real delay stands in.
        if !dry_run {
            let _ = chat(
                agent, provider, model, base_url, key, advance_sys,
                &format!("Task: {task}\nYou are about to begin step {} of {width}. Confirm readiness.", k + 1),
                8,
            );
        } else {
            std::thread::sleep(Duration::from_millis(3));
        }

        // (2) dispatch step k's EFFECT fire-and-forget: it races to completion and is
        //     committed to the shared sink in completion order (NO ordering enforced --
        //     this is the baseline the L3 sequencer would discipline).
        let dispatch_ms = start.elapsed().as_millis();
        let agent_c = agent.clone();
        let provider_c = provider.to_string();
        let model_c = model.to_string();
        let base_c = base_url.map(|s| s.to_string());
        let key_c = key.to_string();
        let effect_sys_c = effect_sys.to_string();
        let task_c = task.to_string();
        let co_c = Arc::clone(&co);
        let tim_c = Arc::clone(&timings);
        let start_c = start;
        let dry = dry_run;
        let mut st = seed ^ (k.wrapping_mul(0x9E3779B97F4A7C15)).max(1);

        let h = std::thread::spawn(move || {
            if dry {
                // DRY RUN ONLY: synthetic latency to exercise reorder detection. NOT a measurement.
                let ms = 1 + (xs(&mut st) % 25);
                std::thread::sleep(Duration::from_millis(ms));
            } else {
                let _ = chat(
                    &agent_c, &provider_c, &model_c, base_c.as_deref(), &key_c, &effect_sys_c,
                    &format!("Task: {task_c}\nPerform and log step {} of {width}.", k + 1),
                    128,
                );
            }
            let complete_ms = start_c.elapsed().as_millis();
            // commit to the shared effect sink in completion order
            co_c.lock().unwrap().push(k);
            tim_c.lock().unwrap().push((k, dispatch_ms, complete_ms));
        });
        handles.push(h);
    }
    for h in handles {
        let _ = h.join();
    }

    let io: Vec<u64> = (0..width as u64).collect();
    let co = Arc::try_unwrap(co).unwrap().into_inner().unwrap();
    let mut timings = Arc::try_unwrap(timings).unwrap().into_inner().unwrap();
    timings.sort_by_key(|t| t.2); // display by completion time
    SessionTrace { io, co, timings }
}

#[derive(Serialize)]
struct JsonSession<'a> {
    session: usize,
    io: &'a [u64],
    co: &'a [u64],
    inversions: usize,
    max_inversions: usize,
    a6: bool,
    effects: Vec<JsonEffect>,
}

#[derive(Serialize)]
struct JsonEffect {
    step: u64,
    dispatch_ms: u128,
    complete_ms: u128,
    latency_ms: u128,
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
    fs::create_dir_all(a.out.join(&model_safe)).expect("create out dir");

    // Ordered multi-step tasks. The content only has to be a plausible ordered
    // procedure; it does not affect the timing measurement (we score completion
    // ORDER, not step content), but it keeps the agent loop realistic.
    let tasks: &[&str] = &[
        "Provision a database, then migrate the schema, then seed reference data, then enable backups.",
        "Create a customer record, charge the card, email the receipt, then close the ticket.",
        "Allocate the VM, attach the disk, install the runtime, then register with the load balancer.",
        "Open the incident, page the on-call, post a status update, then start the mitigation.",
        "Reserve inventory, capture payment, generate the shipping label, then notify the warehouse.",
        "Snapshot the volume, detach it, move it to the new host, then re-attach and verify.",
    ];

    let agent = build_agent();
    let max_inv = a.width * (a.width - 1) / 2;

    let mut a6_ind: Vec<f64> = Vec::with_capacity(a.n);
    let mut inv_total: usize = 0;
    let mut lat_samples: Vec<u128> = Vec::new();
    let mut skipped = 0usize;

    for s in 0..a.n {
        if !a.dry_run {
            eprint!("\r  running session {}/{} ...", s + 1, a.n);
            let _ = std::io::stderr().flush();
        }
        let task = tasks[s % tasks.len()];
        let tr = run_session(
            &agent, &a.provider, &a.model, a.base_url.as_deref(), &a.api_key,
            task, a.width, a.dry_run, a.seed ^ (s as u64).wrapping_mul(0x9E3779B97F4A7C15),
        );

        if tr.co.len() != a.width {
            // an effect thread failed to record (e.g., panic); skip for honesty
            skipped += 1;
            continue;
        }

        let inv = inversions(&tr.co);
        let a6 = a6_witness(&tr.io, &tr.co);
        a6_ind.push(if a6 { 1.0 } else { 0.0 });
        inv_total += inv;

        let effects: Vec<JsonEffect> = tr
            .timings
            .iter()
            .map(|&(step, d, c)| {
                lat_samples.push(c.saturating_sub(d));
                JsonEffect { step, dispatch_ms: d, complete_ms: c, latency_ms: c.saturating_sub(d) }
            })
            .collect();

        let path = a.out.join(&model_safe).join(format!("sess-{s:04}.jsonl"));
        let mut f = fs::File::create(&path).expect("create session file");
        let line = serde_json::to_string(&JsonSession {
            session: s,
            io: &tr.io,
            co: &tr.co,
            inversions: inv,
            max_inversions: max_inv,
            a6,
            effects,
        })
            .expect("serialize session");
        writeln!(f, "{line}").expect("write jsonl");
    }

    if !a.dry_run {
        eprintln!();
    }

    let n = a6_ind.len();
    let a6_count: f64 = a6_ind.iter().sum();
    let rate = if n > 0 { a6_count / n as f64 } else { 0.0 };
    let (lo, hi) = if n == 0 {
        (0.0, 0.0)
    } else if a6_count == 0.0 {
        (0.0, 3.0 / n as f64) // rule of three for the zero cell
    } else {
        bootstrap_ci(&a6_ind, 2000, a.seed ^ 0xA6)
    };
    let mean_inv = if n > 0 { inv_total as f64 / n as f64 } else { 0.0 };
    let scramble = if max_inv > 0 { mean_inv / max_inv as f64 } else { 0.0 };
    let mean_lat = if !lat_samples.is_empty() {
        lat_samples.iter().sum::<u128>() as f64 / lat_samples.len() as f64
    } else {
        0.0
    };

    println!();
    println!("=== L3-live non-vacuity probe: does completion-order commit reorder vs intended order (A6)? ===");
    println!(
        "provider={}  model={}  sessions={}  width={}  dry_run={}",
        a.provider, a.model, n, a.width, a.dry_run
    );
    if skipped > 0 {
        println!("(skipped {skipped} sessions due to effect-thread errors)");
    }
    println!(
        "baseline (completion-order commit)   A6 = {pos:>4}/{n:<4} ({rate:5.1}%) [{lo:4.1}, {hi:4.1}]   \
         mean-inversions = {mi:.2}/{maxi} ({scr:.0}% scramble)   mean-effect-latency = {ml:.0} ms",
        pos = a6_count as u64,
        rate = rate * 100.0,
        lo = lo * 100.0,
        hi = hi * 100.0,
        mi = mean_inv,
        maxi = max_inv,
        scr = scramble * 100.0,
        ml = mean_lat,
    );
    println!();

    if a.dry_run {
        println!("DRY RUN: synthetic per-effect timing -- this validates the harness (reorder detection,");
        println!("         trace writing, A6 scoring) only. The A6 figure above is NOT a measurement.");
    } else if rate >= 0.15 {
        println!("VERDICT: baseline reorders at {:.1}% -- A6 is NON-VACUOUS under live agents.", rate * 100.0);
        println!("         Building the full l3-live driver is justified: anchor it to this same");
        println!("         fire-and-forget async-effect loop, add the L3 sequencer (commit in io order),");
        println!("         and report baseline A6 vs L3 0/N with the serialization-latency cost.");
        println!("         Remember this is a CONSERVATIVE rate (homogeneous effects); heterogeneous");
        println!("         real tools reorder more, so the live A6 rate is at least this.");
    } else if rate > 0.0 {
        println!("VERDICT: baseline reorders at {:.1}% -- low but non-zero.", rate * 100.0);
        println!("         Borderline. Homogeneous effects under-estimate A6; a heterogeneous-effect");
        println!("         variant (a slow tool class vs a fast one) would reorder more. Either run that");
        println!("         variant before committing to l3-live, or keep L3 model-only with the caveat.");
    } else {
        println!("VERDICT: baseline reorders at 0% under homogeneous effect latency -- A6 is VACUOUS here.");
        println!("         Do NOT build l3-live on this workload; it would be the weak vacuous result.");
        println!("         Keep L3 model-only with the honest caveat (it is structurally absent from a");
        println!("         runtime whose commit is atomic and ordered). A heterogeneous-tool setting is");
        println!("         the only thing that could change this, and it is harder to make non-staged.");
    }
    println!();
    println!("per-session traces (io, co, inversions, effect timings) under: {}", a.out.display());
}