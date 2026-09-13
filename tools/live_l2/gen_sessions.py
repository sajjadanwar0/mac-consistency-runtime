#!/usr/bin/env python3
"""gen_sessions.py -- drive the Section 5.11 live workload and RECORD it.

The 0/120 live figure was produced by the superseded twin and its sessions
were never committed, so the claim could not be re-checked by anyone. This
harness records every session to JSON, so the replay through the verified
runtime (cargo run --release --example l2_replay) is reproducible forever
after without an API key.

Workload, as Section 5.11 describes it: a planner commits a one-line action
plan for an ambiguous triage ticket; an executor reads the plan (acquiring
the planner as a causal predecessor) and commits a result; a supervisor then
decides, from the ticket and the plan, whether to retract the plan -- the
live analogue of saga compensation. A3 is a surviving executor of a
retracted planner.

Only the supervisor's retract decision is model-dependent, so that is what
is recorded per session, along with the cells and values the replay needs.

  export OPENAI_API_KEY=... ANTHROPIC_API_KEY=...
  python3 gen_sessions.py --provider openai    --model gpt-4o-mini      --n 200 --out sessions
  python3 gen_sessions.py --provider anthropic --model claude-haiku-4-5 --n 200 --out sessions
  python3 gen_sessions.py --provider ollama    --model llama3.2         --n 200 --out sessions
"""
import argparse, json, os, random, sys, time
from pathlib import Path

TICKETS = [
    "Users report the export button does nothing on Safari; logs show a 404 on /api/export.",
    "Checkout fails intermittently for EU customers with 'currency not supported'.",
    "Nightly sync finished but three tenants show stale dashboards.",
    "Login works, but SSO users land on a blank page after redirect.",
    "Search returns results for deleted documents.",
]
PLAN_SYS = "You are a triage planner. Reply with ONE short action line. No preamble."
SUP_SYS = ("You are a triage supervisor. You see a ticket and the plan an agent committed. "
           "Reply with exactly RETRACT if the plan should be withdrawn as wrong or unsafe, "
           "otherwise exactly KEEP. One word.")


def call_openai(model, sys_p, user_p):
    from openai import OpenAI
    c = OpenAI()
    r = c.chat.completions.create(model=model, temperature=1.0, max_tokens=60,
        messages=[{"role": "system", "content": sys_p}, {"role": "user", "content": user_p}])
    return r.choices[0].message.content.strip()


def call_anthropic(model, sys_p, user_p):
    import anthropic
    c = anthropic.Anthropic()
    r = c.messages.create(model=model, max_tokens=60, system=sys_p,
                          messages=[{"role": "user", "content": user_p}])
    return "".join(b.text for b in r.content if b.type == "text").strip()


def call_ollama(model, sys_p, user_p):
    import urllib.request
    body = json.dumps({"model": model, "stream": False,
                       "messages": [{"role": "system", "content": sys_p},
                                    {"role": "user", "content": user_p}]}).encode()
    req = urllib.request.Request(os.environ.get("OLLAMA_URL", "http://localhost:11434") + "/api/chat",
                                 data=body, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=180) as f:
        return json.load(f)["message"]["content"].strip()


CALL = {"openai": call_openai, "anthropic": call_anthropic, "ollama": call_ollama}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", required=True, choices=sorted(CALL))
    ap.add_argument("--model", required=True)
    ap.add_argument("--n", type=int, default=200)
    ap.add_argument("--out", default="sessions")
    ap.add_argument("--seed", type=int, default=20260913)
    a = ap.parse_args()

    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    rng = random.Random(a.seed)
    call = CALL[a.provider]
    retracted = 0
    for i in range(a.n):
        ticket = TICKETS[rng.randrange(len(TICKETS))]
        try:
            plan = call(a.model, PLAN_SYS, f"Ticket: {ticket}\nOne action line:")
            verdict = call(a.model, SUP_SYS, f"Ticket: {ticket}\nCommitted plan: {plan}\nRETRACT or KEEP:")
        except Exception as e:                      # noqa: BLE001
            print(f"  session {i}: {type(e).__name__}: {e}", file=sys.stderr)
            time.sleep(2)
            continue
        r = verdict.upper().startswith("RETRACT")
        retracted += r
        rec = {"id": f"{a.model}-{i:04d}", "model": a.model,
               "plan_cell": 1, "result_cell": 2,
               "plan_value": (abs(hash(plan)) % 900) + 100,
               "result_value": (abs(hash(plan + ticket)) % 900) + 1000,
               "retracted": bool(r),
               "ticket": ticket, "plan": plan, "supervisor_verdict": verdict}
        (out / f"{a.model.replace('/', '_')}-{i:04d}.json").write_text(json.dumps(rec, indent=1))
        if (i + 1) % 25 == 0:
            print(f"  {i+1}/{a.n} sessions, {retracted} retracted", file=sys.stderr)
    print(f"{a.model}: {a.n} sessions, {retracted} retracted -> {out}")


if __name__ == "__main__":
    main()
