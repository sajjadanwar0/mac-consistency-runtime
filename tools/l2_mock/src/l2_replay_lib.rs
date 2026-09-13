//! l2_replay_lib.rs -- replay recorded live sessions through the VERIFIED
//! L2 runtime and through the unguarded baseline.
//!
//! Section 5.11's live figure (0/120 across three model families) was
//! produced by the superseded twin, before the measurement moved onto the
//! verified bytes, and its sessions were never committed. This replays
//! sessions that ARE committed, through `l2_exec::L2Runtime` gated by the
//! verified `can_commit`, so the live claim rests on the same artifact as
//! the synthetic one and can be re-checked without API keys ever again.
//!
//! Session schema (one JSON object per file):
//!   { "id": "...", "model": "...", "plan_cell": 1, "result_cell": 2,
//!     "plan_value": 11, "result_value": 22, "retracted": true|false }
//!
//! The workload is Section 5.11's: a planner commits a plan; an executor
//! reads it (acquiring the planner as a causal predecessor) and commits a
//! result; a supervisor then decides whether to retract the plan. A3 is
//! the surviving executor of a retracted planner.

use crate::l2_exec::L2Runtime;
use crate::l2_unguarded::UnguardedStore;
use crate::l2_measure::{detect_a3, Prov};

#[derive(Debug, Clone)]
pub struct Session {
    pub id: String,
    pub model: String,
    pub plan_cell: u64,
    pub result_cell: u64,
    pub plan_value: u64,
    pub result_value: u64,
    pub retracted: bool,
}

pub fn parse(v: &serde_json::Value) -> Option<Session> {
    Some(Session {
        id: v.get("id")?.as_str()?.to_string(),
        model: v.get("model")?.as_str()?.to_string(),
        plan_cell: v.get("plan_cell")?.as_u64()?,
        result_cell: v.get("result_cell")?.as_u64()?,
        plan_value: v.get("plan_value")?.as_u64()?,
        result_value: v.get("result_value")?.as_u64()?,
        retracted: v.get("retracted")?.as_bool()?,
    })
}

/// Replay through the verified runtime. Returns (a3_fired, executor_survived).
pub fn replay_guarded(s: &Session) -> (bool, bool) {
    let mut rt = L2Runtime::new();
    let planner = rt.begin();
    rt.write(planner, s.plan_cell, s.plan_value);
    if !rt.can_commit(planner) {
        return (false, false);
    }
    rt.commit(planner);

    let executor = rt.begin();
    rt.read(executor, s.plan_cell);
    rt.write(executor, s.result_cell, s.result_value);
    let live = if rt.can_commit(executor) {
        rt.commit(executor);
        true
    } else {
        rt.abort(executor);
        false
    };

    if s.retracted {
        rt.abort(planner);
    }

    let mut trace = Vec::new();
    for id in 0..rt.next_txn {
        if let Some(x) = rt.txns.get(&id) {
            trace.push(Prov {
                txn: id,
                committed: x.committed,
                aborted: x.aborted,
                predecessors: x.predecessors.clone(),
            });
        }
    }
    let survived = rt
        .txns
        .get(&executor)
        .map_or(false, |x| x.committed && !x.aborted);
    (detect_a3(&trace).is_some(), live && survived)
}

/// Replay through the L1-class baseline, which does not cascade.
pub fn replay_unguarded(s: &Session) -> (bool, bool) {
    let mut st = UnguardedStore::new();
    let planner = st.begin();
    if !st.commit(planner, &[(s.plan_cell, s.plan_value)]) {
        return (false, false);
    }
    let executor = st.begin();
    st.read(executor, s.plan_cell);
    let live = st.commit(executor, &[(s.result_cell, s.result_value)]);
    if s.retracted {
        st.abort(planner);
    }
    let trace: Vec<Prov> = st
        .txns
        .iter()
        .enumerate()
        .map(|(i, x)| Prov {
            txn: i as u64,
            committed: x.committed,
            aborted: x.aborted,
            predecessors: x.predecessors.clone(),
        })
        .collect();
    let survived = st.txns[executor as usize].committed && !st.txns[executor as usize].aborted;
    (detect_a3(&trace).is_some(), live && survived)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn sess(retracted: bool) -> Session {
        Session { id: "t".into(), model: "m".into(), plan_cell: 1, result_cell: 2,
                  plan_value: 11, result_value: 22, retracted }
    }
    #[test]
    fn retraction_makes_the_baseline_fail_and_the_verified_runtime_hold() {
        let (g_a3, g_live) = replay_guarded(&sess(true));
        let (u_a3, _) = replay_unguarded(&sess(true));
        assert!(!g_a3, "verified runtime admitted A3 on a retracted session");
        assert!(!g_live, "the cascade must remove the executor when its planner is retracted");
        assert!(u_a3, "the unguarded baseline must exhibit A3, or the comparison is vacuous");
    }
    #[test]
    fn no_retraction_means_no_a3_anywhere_and_the_executor_survives() {
        let (g_a3, g_live) = replay_guarded(&sess(false));
        let (u_a3, u_live) = replay_unguarded(&sess(false));
        assert!(!g_a3 && !u_a3);
        assert!(g_live && u_live, "an unretracted session must keep its executor in both arms");
    }
}
