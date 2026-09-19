// l2-live/src/main.rs
//
// Live L2 deployment: real model agents on the VERIFIED runtime, with output
// commit releasing a real effect.
//
// 2026-09-16 round 32. OVERRULED: this driver built src/l2_causal.rs, an
// unverified twin of the L2 discipline, through #[path], and scored A3 as a
// surviving executor of a retracted planner. That file is gone and the driver
// no longer built. It now links the runtime crate and drives
// `agent_consistency_runtime::l2_exec::L2Runtime` -- the bytes Verus verified in
// the pilot (lib_l2_exec.rs) -- next to the unguarded baseline store, on the
// same model outputs, and scores both with `l2_measure::detect_a3`: an
// executor whose effect is OUT while its plan is retracted.
//
// Workload (the one tools/live_l2/gen_sessions.py records, plus a real
// executor call): a planner commits a one-line plan for a triage ticket; an
// executor reads the plan and commits a one-line result, and asks to release
// its effect; a supervisor then decides RETRACT or KEEP.
//   baseline  releases the executor's effect at commit, before the verdict;
//   verified  output commit refuses that release while the plan is under
//             review; KEEP releases the plan and then the executor's effect,
//             RETRACT aborts the plan and the cascade aborts the executor.
// Each arm appends every released effect to its own outbox file, with the
// time it left, so what went out is on disk, not inferred.
//
// What a live run adds to the replay of recorded sessions: the verdicts come
// from the model in this run, and the cost of output commit is measured in
// wall-clock time -- how long each kept executor's effect was held waiting for
// the supervisor. The zero A3 of the verified arm is structural (output commit,
// proved in lib_l2_safety.rs); it is not a property of the models.
//
// Sessions are written in the format examples/l2_replay.rs reads, so a live run
// can be replayed and cross-checked:
//   cargo run --release --example l2_replay -- <out>/sessions

use agent_consistency_runtime::l2_exec::L2Runtime;
use agent_consistency_runtime::l2_measure::{detect_a3, Prov};
use agent_consistency_runtime::l2_unguarded::UnguardedStore;
use serde::Serialize;
use serde_json::{json, Value};
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

const PLAN_CELL: u64 = 1;
const RESULT_CELL: u64 = 2;

// The workload of tools/live_l2/gen_sessions.py (tickets and the planner and
// supervisor prompts, verbatim), so live runs are comparable with the 600
// recorded sessions.
const TICKETS: &[&str] = &[
    "Users report the export button does nothing on Safari; logs show a 404 on /api/export.",
    "Checkout fails intermittently for EU customers with 'currency not supported'.",
    "Nightly sync finished but three tenants show stale dashboards.",
    "Login works, but SSO users land on a blank page after redirect.",
    "Search returns results for deleted documents.",
];
const PLAN_SYS: &str = "You are a triage planner. Reply with ONE short action line. No preamble.";
const SUP_SYS: &str = "You are a triage supervisor. You see a ticket and the plan an agent committed. \
Reply with exactly RETRACT if the plan should be withdrawn as wrong or unsafe, \
otherwise exactly KEEP. One word.";
const EXEC_SYS: &str = "You are an execution agent. Given an action plan, output a one-line summary \
of the action you took (under 12 words).";

#[derive(Clone, Debug)]
struct Args {
    provider: String, // openai | anthropic | ollama | vllm
    model: String,
    base_url: Option<String>,
    n: usize,
    validator: String, // llm | forced
    retract_rate: f64,
    out: PathBuf,
    seed: u64,
    dry_run: bool,
    api_key: String,
}

fn usage_and_exit() -> ! {
    eprintln!(
        "usage: l2_live --provider <openai|anthropic|ollama|vllm> --model <name> \\
                [--base-url <url>] [--n <sessions>] [--validator <llm|forced>] \\
                [--retract-rate <0..1>] [--out <dir>] [--seed <u64>] [--api-key <key>] [--dry-run]

env: OPENAI_API_KEY / ANTHROPIC_API_KEY are used when --api-key is omitted;
OLLAMA_URL overrides http://localhost:11434 for --provider ollama.
--dry-run makes no model calls (fixed content, forced verdicts) to test the wiring."
    );
    std::process::exit(2);
}

fn parse_args() -> Args {
    let mut a = Args {
        provider: "openai".to_string(),
        model: "gpt-4o-mini".to_string(),
        base_url: None,
        n: 200,
        validator: "llm".to_string(),
        retract_rate: 0.3,
        out: PathBuf::from("./l2_live_out"),
        seed: 20260916,
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
            "--validator" => a.validator = val(),
            "--retract-rate" => a.retract_rate = val().parse().unwrap_or_else(|_| usage_and_exit()),
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
    if !["openai", "anthropic", "ollama", "vllm"].contains(&a.provider.as_str()) {
        eprintln!("unknown provider: {}", a.provider);
        usage_and_exit();
    }
    if !["llm", "forced"].contains(&a.validator.as_str()) {
        eprintln!("unknown validator: {}", a.validator);
        usage_and_exit();
    }
    if a.api_key.is_empty() && !a.dry_run {
        a.api_key = match a.provider.as_str() {
            "anthropic" => std::env::var("ANTHROPIC_API_KEY").unwrap_or_default(),
            "openai" => std::env::var("OPENAI_API_KEY").unwrap_or_default(),
            _ => String::new(),
        };
    }
    a
}

// ---------------------------------------------------------------------------
// Model calls (blocking ureq): OpenAI and OpenAI-compatible (vLLM), Anthropic,
// Ollama. max_tokens and temperature follow gen_sessions.py.
// ---------------------------------------------------------------------------

fn build_agent() -> ureq::Agent {
    let mut b = ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(10))
        .timeout_read(Duration::from_secs(180))
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

fn chat(agent: &ureq::Agent, a: &Args, system: &str, user: &str) -> Result<String, String> {
    let mut last = String::new();
    for attempt in 0..2 {
        match chat_once(agent, a, system, user) {
            Ok(s) if !s.is_empty() => return Ok(s),
            Ok(_) => last = "empty reply".to_string(),
            Err(e) => last = e,
        }
        if attempt == 0 {
            std::thread::sleep(Duration::from_secs(2));
        }
    }
    Err(last)
}

fn chat_once(agent: &ureq::Agent, a: &Args, system: &str, user: &str) -> Result<String, String> {
    match a.provider.as_str() {
        "anthropic" => {
            let base = a.base_url.as_deref().unwrap_or("https://api.anthropic.com").trim_end_matches('/');
            let resp: Value = agent
                .post(&format!("{base}/v1/messages"))
                .set("x-api-key", &a.api_key)
                .set("anthropic-version", "2023-06-01")
                .set("content-type", "application/json")
                .send_json(json!({
                    "model": a.model, "max_tokens": 60, "system": system,
                    "messages": [{"role": "user", "content": user}]
                }))
                .map_err(|e| e.to_string())?
                .into_json()
                .map_err(|e| e.to_string())?;
            let text: String = resp["content"]
                .as_array()
                .ok_or_else(|| format!("anthropic: unexpected response: {resp}"))?
                .iter()
                .filter(|b| b["type"] == "text")
                .filter_map(|b| b["text"].as_str())
                .collect();
            Ok(text.trim().to_string())
        }
        "ollama" => {
            let base = a
                .base_url
                .clone()
                .or_else(|| std::env::var("OLLAMA_URL").ok())
                .unwrap_or_else(|| "http://localhost:11434".to_string());
            let resp: Value = agent
                .post(&format!("{}/api/chat", base.trim_end_matches('/')))
                .set("content-type", "application/json")
                .send_json(json!({
                    "model": a.model, "stream": false,
                    "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]
                }))
                .map_err(|e| e.to_string())?
                .into_json()
                .map_err(|e| e.to_string())?;
            resp["message"]["content"]
                .as_str()
                .map(|s| s.trim().to_string())
                .ok_or_else(|| format!("ollama: unexpected response: {resp}"))
        }
        _ => {
            let base = a.base_url.as_deref().unwrap_or("https://api.openai.com").trim_end_matches('/');
            let mut req = agent.post(&format!("{base}/v1/chat/completions")).set("content-type", "application/json");
            if !a.api_key.is_empty() {
                req = req.set("Authorization", &format!("Bearer {}", a.api_key));
            }
            let resp: Value = req
                .send_json(json!({
                    "model": a.model, "temperature": 1.0, "max_tokens": 60,
                    "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]
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

// ---------------------------------------------------------------------------
// The two arms. Each is split at the supervisor's verdict, because the model
// call sits between the executor's commit and the decision.
// ---------------------------------------------------------------------------

#[derive(Serialize, Clone, Copy, Debug, PartialEq, Eq)]
struct ArmOutcome {
    /// A3: the executor's effect is out while its plan is retracted
    a3: bool,
    /// the executor's effect left this arm
    executor_released: bool,
    /// the executor asked to release before the verdict and was refused
    held_before_verdict: bool,
}

fn trace_of(rt: &L2Runtime) -> Vec<Prov> {
    (0..rt.next_txn)
        .filter_map(|id| {
            rt.txns.get(&id).map(|x| Prov {
                txn: id,
                committed: x.committed,
                aborted: x.aborted,
                externalized: x.externalized,
                predecessors: x.predecessors.clone(),
            })
        })
        .collect()
}

struct VerifiedArm {
    rt: L2Runtime,
    planner: u64,
    executor: u64,
    held_before_verdict: bool,
}

impl VerifiedArm {
    fn commit(plan_value: u64, result_value: u64) -> VerifiedArm {
        let mut rt = L2Runtime::new();
        let planner = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.write(planner, PLAN_CELL, plan_value), "L2Runtime::write refused");
        assert!(rt.commit(planner), "L2Runtime::commit refused");
        let executor = rt.begin().expect("L2Runtime counters exhausted");
        assert!(rt.read(executor, PLAN_CELL), "L2Runtime::read refused");
        assert!(rt.write(executor, RESULT_CELL, result_value), "L2Runtime::write refused");
        assert!(rt.commit(executor), "L2Runtime::commit refused");
        // The executor asks to release its effect at once; the plan is under review.
        let held_before_verdict = !rt.externalize(executor);
        VerifiedArm { rt, planner, executor, held_before_verdict }
    }

    fn decide(mut self, retracted: bool) -> ArmOutcome {
        if retracted {
            assert!(self.rt.abort(self.planner), "a plan under review must be retractable");
        } else {
            assert!(self.rt.externalize(self.planner), "a kept plan must be releasable");
        }
        let _ = self.rt.externalize(self.executor);
        let released = self.rt.txns.get(&self.executor).map_or(false, |x| x.externalized);
        ArmOutcome {
            a3: detect_a3(&trace_of(&self.rt)).is_some(),
            executor_released: released,
            held_before_verdict: self.held_before_verdict,
        }
    }
}

struct BaselineArm {
    st: UnguardedStore,
    planner: u64,
    executor: u64,
}

impl BaselineArm {
    /// The executor's effect leaves at its commit, before the verdict.
    fn commit(plan_value: u64, result_value: u64) -> BaselineArm {
        let mut st = UnguardedStore::new();
        let planner = st.begin();
        assert!(st.commit(planner, &[(PLAN_CELL, plan_value)]), "baseline planner commit refused");
        let executor = st.begin();
        st.read(executor, PLAN_CELL);
        assert!(st.commit(executor, &[(RESULT_CELL, result_value)]), "baseline executor commit refused");
        BaselineArm { st, planner, executor }
    }

    fn decide(mut self, retracted: bool) -> ArmOutcome {
        if retracted {
            self.st.abort(self.planner);
        }
        let trace: Vec<Prov> = self
            .st
            .txns
            .iter()
            .enumerate()
            .map(|(i, x)| Prov {
                txn: i as u64,
                committed: x.committed,
                aborted: x.aborted,
                externalized: x.externalized,
                predecessors: x.predecessors.clone(),
            })
            .collect();
        ArmOutcome {
            a3: detect_a3(&trace).is_some(),
            executor_released: self.st.txns[self.executor as usize].externalized,
            held_before_verdict: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Sessions
// ---------------------------------------------------------------------------

fn fnv1a(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn xs(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[derive(Serialize, Clone, Copy, Debug, Default)]
struct TimingMs {
    planner: u128,
    executor: u128,
    supervisor: u128,
    /// the kept executor's effect, from its refused release request to its release
    verified_hold: Option<u128>,
}

#[derive(Serialize, Debug)]
struct SessionRecord {
    // the fields examples/l2_replay.rs reads
    id: String,
    model: String,
    plan_cell: u64,
    result_cell: u64,
    plan_value: u64,
    result_value: u64,
    retracted: bool,
    // the live record
    provider: String,
    validator: String,
    ticket: String,
    plan: String,
    result: String,
    supervisor_verdict: String,
    timing_ms: TimingMs,
    verified: ArmOutcome,
    baseline: ArmOutcome,
}

struct Outboxes {
    verified: PathBuf,
    baseline: PathBuf,
}

fn append_effect(path: &Path, id: &str, t_ms: u128, text: &str) {
    let mut f = OpenOptions::new().create(true).append(true).open(path).expect("open outbox");
    writeln!(f, "{}", json!({"session": id, "t_ms": t_ms, "effect": text})).expect("write outbox");
}

/// One live session. `ask` performs a model call (or the dry-run stand-in) and
/// returns its text; `None` when it failed and the session is skipped.
fn run_session<F>(a: &Args, i: usize, ticket: &str, start: Instant, boxes: &Outboxes, ask: &mut F) -> Option<SessionRecord>
where
    F: FnMut(&str, &str, &str) -> Option<String>,
{
    let id = format!("{}-{i:04}", a.model);
    let t = Instant::now();
    let plan = ask("planner", PLAN_SYS, &format!("Ticket: {ticket}\nOne action line:"))?;
    let planner_ms = t.elapsed().as_millis();
    let t = Instant::now();
    let result = ask("executor", EXEC_SYS, &format!("Plan: {plan}\nExecute it and summarize in one line."))?;
    let executor_ms = t.elapsed().as_millis();
    let plan_value = fnv1a(&plan) % 900 + 100;
    let result_value = fnv1a(&(plan.clone() + &result)) % 900 + 1000;

    // Both arms commit on the same content. The baseline's effect leaves now;
    // the verified runtime holds it.
    let verified = VerifiedArm::commit(plan_value, result_value);
    let held_since = Instant::now();
    let baseline = BaselineArm::commit(plan_value, result_value);
    append_effect(&boxes.baseline, &id, start.elapsed().as_millis(), &result);

    let t = Instant::now();
    let verdict = ask("supervisor", SUP_SYS, &format!("Ticket: {ticket}\nCommitted plan: {plan}\nRETRACT or KEEP:"))?;
    let supervisor_ms = t.elapsed().as_millis();
    let retracted = verdict.trim().to_uppercase().starts_with("RETRACT");

    let verified = verified.decide(retracted);
    let verified_hold = if verified.executor_released {
        append_effect(&boxes.verified, &id, start.elapsed().as_millis(), &result);
        Some(held_since.elapsed().as_millis())
    } else {
        None
    };
    let baseline = baseline.decide(retracted);

    Some(SessionRecord {
        id,
        model: a.model.clone(),
        plan_cell: PLAN_CELL,
        result_cell: RESULT_CELL,
        plan_value,
        result_value,
        retracted,
        provider: a.provider.clone(),
        validator: a.validator.clone(),
        ticket: ticket.to_string(),
        plan,
        result,
        supervisor_verdict: verdict,
        timing_ms: TimingMs { planner: planner_ms, executor: executor_ms, supervisor: supervisor_ms, verified_hold },
        verified,
        baseline,
    })
}

#[derive(Serialize, Debug, Default, Clone)]
struct Summary {
    provider: String,
    model: String,
    validator: String,
    dry_run: bool,
    sessions: usize,
    skipped: usize,
    retracted: usize,
    verified_a3: usize,
    baseline_a3: usize,
    verified_released: usize,
    baseline_released: usize,
    verified_hold_ms_median: Option<u128>,
    verified_hold_ms_p90: Option<u128>,
    supervisor_ms_median: Option<u128>,
}

fn percentile(mut v: Vec<u128>, p: f64) -> Option<u128> {
    if v.is_empty() {
        return None;
    }
    v.sort_unstable();
    let idx = ((p * (v.len() - 1) as f64).round() as usize).min(v.len() - 1);
    Some(v[idx])
}

fn run(a: &Args) -> Summary {
    let sessions_dir = a.out.join("sessions");
    fs::create_dir_all(&sessions_dir).expect("create sessions dir");
    let model_safe = a.model.replace('/', "_");
    let boxes = Outboxes {
        verified: a.out.join(format!("{model_safe}-effects-verified.jsonl")),
        baseline: a.out.join(format!("{model_safe}-effects-baseline.jsonl")),
    };
    let agent = build_agent();
    let start = Instant::now();
    let mut rng = a.seed | 1;
    let mut s = Summary {
        provider: a.provider.clone(),
        model: a.model.clone(),
        validator: a.validator.clone(),
        dry_run: a.dry_run,
        ..Summary::default()
    };
    let (mut holds, mut sups) = (Vec::new(), Vec::new());
    for i in 0..a.n {
        let ticket = TICKETS[(xs(&mut rng) % TICKETS.len() as u64) as usize];
        let forced_retract = ((xs(&mut rng) >> 11) as f64 / (1u64 << 53) as f64) < a.retract_rate;
        let mut ask = |role: &str, system: &str, user: &str| -> Option<String> {
            if role == "supervisor" && a.validator == "forced" {
                return Some(if forced_retract { "RETRACT" } else { "KEEP" }.to_string());
            }
            if a.dry_run {
                return Some(match role {
                    "planner" => format!("PLAN-{i}"),
                    "executor" => format!("RESULT-{i}"),
                    _ => if forced_retract { "RETRACT".to_string() } else { "KEEP".to_string() },
                });
            }
            match chat(&agent, a, system, user) {
                Ok(v) => Some(v),
                Err(e) => {
                    eprintln!("session {i}: {role} call failed: {e}; skipping");
                    None
                }
            }
        };
        if !a.dry_run {
            eprint!("\r  session {}/{} ...", i + 1, a.n);
            let _ = std::io::stderr().flush();
        }
        let rec = match run_session(a, i, ticket, start, &boxes, &mut ask) {
            Some(r) => r,
            None => {
                s.skipped += 1;
                continue;
            }
        };
        s.sessions += 1;
        s.retracted += rec.retracted as usize;
        s.verified_a3 += rec.verified.a3 as usize;
        s.baseline_a3 += rec.baseline.a3 as usize;
        s.verified_released += rec.verified.executor_released as usize;
        s.baseline_released += rec.baseline.executor_released as usize;
        if let Some(h) = rec.timing_ms.verified_hold {
            holds.push(h);
        }
        sups.push(rec.timing_ms.supervisor);
        let path = sessions_dir.join(format!("{model_safe}-{i:04}.json"));
        fs::write(&path, serde_json::to_string_pretty(&rec).expect("serialize session")).expect("write session");
    }
    if !a.dry_run {
        eprintln!();
    }
    s.verified_hold_ms_median = percentile(holds.clone(), 0.5);
    s.verified_hold_ms_p90 = percentile(holds, 0.9);
    s.supervisor_ms_median = percentile(sups, 0.5);
    fs::write(
        a.out.join(format!("{model_safe}-summary.json")),
        serde_json::to_string_pretty(&s).expect("serialize summary"),
    )
    .expect("write summary");
    s
}

fn main() {
    let a = parse_args();
    if !a.dry_run && a.api_key.is_empty() && (a.provider == "openai" || a.provider == "anthropic") {
        eprintln!(
            "no API key for provider '{}': set OPENAI_API_KEY / ANTHROPIC_API_KEY, pass --api-key, or use --dry-run",
            a.provider
        );
        std::process::exit(2);
    }
    let s = run(&a);
    println!(
        "provider={} model={} validator={} dry_run={} sessions={} skipped={}",
        s.provider, s.model, s.validator, s.dry_run, s.sessions, s.skipped
    );
    println!(
        "retracted {}   verified A3 {}/{}   baseline A3 {}/{}   released: verified {}, baseline {}",
        s.retracted, s.verified_a3, s.retracted, s.baseline_a3, s.retracted, s.verified_released, s.baseline_released
    );
    let ms = |v: Option<u128>| v.map_or("n/a".to_string(), |x| format!("{x} ms"));
    println!(
        "verified hold of kept effects: median {}, p90 {}   supervisor call: median {}",
        ms(s.verified_hold_ms_median),
        ms(s.verified_hold_ms_p90),
        ms(s.supervisor_ms_median)
    );
    println!("sessions: {}   (replay: cargo run --release --example l2_replay -- {})", a.out.join("sessions").display(), a.out.join("sessions").display());
}

#[cfg(test)]
mod tests {
    use super::*;
    use agent_consistency_runtime::l2_replay_lib::{parse, replay_guarded, replay_unguarded};

    #[test]
    fn a_retraction_leaves_an_effect_out_only_in_the_baseline() {
        let v = VerifiedArm::commit(111, 1111);
        assert!(v.held_before_verdict, "output commit released the executor while its plan was under review");
        let v = v.decide(true);
        let b = BaselineArm::commit(111, 1111).decide(true);
        assert_eq!(v, ArmOutcome { a3: false, executor_released: false, held_before_verdict: true });
        assert!(b.a3 && b.executor_released, "the baseline must have released the executor and exhibit A3");
    }

    #[test]
    fn a_kept_plan_releases_the_executor_in_both_arms() {
        let v = VerifiedArm::commit(222, 2222).decide(false);
        let b = BaselineArm::commit(222, 2222).decide(false);
        assert!(v.executor_released && !v.a3 && v.held_before_verdict);
        assert!(b.executor_released && !b.a3);
    }

    #[test]
    fn a_dry_run_writes_sessions_the_replay_reproduces() {
        let out = std::env::temp_dir().join(format!(
            "l2-live-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        let a = Args {
            provider: "openai".into(),
            model: "dry-model".into(),
            base_url: None,
            n: 40,
            validator: "forced".into(),
            retract_rate: 0.3,
            out: out.clone(),
            seed: 7,
            dry_run: true,
            api_key: String::new(),
        };
        let s = run(&a);
        assert_eq!(s.sessions, 40);
        assert!(s.retracted > 0 && s.retracted < 40, "the forced verdicts must both retract and keep");
        assert_eq!(s.verified_a3, 0);
        assert_eq!(s.baseline_a3, s.retracted);
        assert_eq!(s.verified_released, 40 - s.retracted);
        assert_eq!(s.baseline_released, 40);
        let lines = |p: PathBuf| fs::read_to_string(p).unwrap_or_default().lines().count();
        assert_eq!(lines(out.join("dry-model-effects-baseline.jsonl")), 40);
        assert_eq!(lines(out.join("dry-model-effects-verified.jsonl")), 40 - s.retracted);
        let mut replayed = 0;
        for ent in fs::read_dir(out.join("sessions")).unwrap().flatten() {
            let v: Value = serde_json::from_str(&fs::read_to_string(ent.path()).unwrap()).unwrap();
            let sess = parse(&v).expect("the replay must parse a live session");
            let (g_a3, g_released) = replay_guarded(&sess);
            let (u_a3, u_released) = replay_unguarded(&sess);
            assert_eq!(g_a3, v["verified"]["a3"].as_bool().unwrap());
            assert_eq!(g_released, v["verified"]["executor_released"].as_bool().unwrap());
            assert_eq!(u_a3, v["baseline"]["a3"].as_bool().unwrap());
            assert_eq!(u_released, v["baseline"]["executor_released"].as_bool().unwrap());
            replayed += 1;
        }
        assert_eq!(replayed, 40);
        let _ = fs::remove_dir_all(&out);
    }
}
