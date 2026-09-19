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
//! result; a supervisor then decides whether to retract the plan.
//!
//! 2026-09-16 round 28: A3 is an executor whose effects are OUT while its
//! planner is retracted. OVERRULED (rounds <= 26): A3 was a surviving
//! executor of a retracted planner, which the cascade "prevents" by
//! relabeling. Each arm now releases effects the way it would in service:
//! the baseline at commit; the verified runtime through externalize, where
//! the plan is under the supervisor's review until the verdict, so the
//! executor's release is held until KEEP releases the plan, and RETRACT
//! aborts both before anything of either is out. A recorded session holds
//! the verdict, not when effects were released; the release order is this
//! policy, the same for every session.
//!
//! 2026-09-19 round 33: a third arm, the SUPERSEDED design
//! (`l2_cascade::CascadeStore`: release at commit AND cascade). On a retracted
//! session it flags the executor aborted after the executor's effect is out,
//! so the overruled predicate reads clean while the current one fires. With
//! two arms the replay could not show that the definitions differ.

use crate::l2_cascade::CascadeStore;
use crate::l2_exec::L2Runtime;
use crate::l2_unguarded::UnguardedStore;
use crate::l2_measure::{detect_a3, detect_a3_unpropagated, provenance_of, Prov};

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

/// Replay through the verified runtime under output commit.
/// Returns (a3_fired, executor_released).
pub fn replay_guarded(s: &Session) -> (bool, bool) {
    let mut rt = L2Runtime::new();
    let planner = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.write(planner, s.plan_cell, s.plan_value), "L2Runtime::write refused");
    if !rt.can_commit(planner) {
        return (false, false);
    }
    assert!(rt.commit(planner), "L2Runtime::commit refused");
    let executor = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.read(executor, s.plan_cell), "L2Runtime::read refused");
    assert!(rt.write(executor, s.result_cell, s.result_value), "L2Runtime::write refused");
    if rt.can_commit(executor) {
        assert!(rt.commit(executor), "L2Runtime::commit refused");
        // The executor asks to release at once. The plan is under review, so
        // output commit must hold it.
        assert!(!rt.externalize(executor), "output commit released a dependent of a plan under review");
    } else {
        assert!(rt.abort(executor), "L2Runtime::abort refused");
    }

    if s.retracted {
        assert!(rt.abort(planner), "a plan under review must be retractable");
    } else {
        assert!(rt.externalize(planner), "a kept plan must be releasable");
    }
    // After the verdict the executor asks again; refused if the cascade took it.
    let _ = rt.externalize(executor);

    let mut trace = Vec::new();
    for id in 0..rt.next_txn {
        if let Some(x) = rt.txns.get(&id) {
            trace.push(Prov {
                txn: id,
                committed: x.committed,
                aborted: x.aborted,
                externalized: x.externalized,
                predecessors: x.predecessors.clone(),
            });
        }
    }
    let released = rt.txns.get(&executor).map_or(false, |x| x.externalized);
    (detect_a3(&trace).is_some(), released)
}

/// Replay through the L1-class baseline, which releases at commit and does
/// not cascade. Returns (a3_fired, executor_released).
pub fn replay_unguarded(s: &Session) -> (bool, bool) {
    let mut st = UnguardedStore::new();
    let planner = st.begin();
    if !st.commit(planner, &[(s.plan_cell, s.plan_value)]) {
        return (false, false);
    }
    let executor = st.begin();
    st.read(executor, s.plan_cell);
    st.commit(executor, &[(s.result_cell, s.result_value)]);
    if s.retracted {
        st.abort(planner);
    }
    let trace = provenance_of(&st);
    (detect_a3(&trace).is_some(), st.txns[executor as usize].externalized)
}

/// Replay through the SUPERSEDED design, which releases at commit and
/// cascades. Returns (a3_fired, overruled_a3_fired, executor_released).
pub fn replay_cascade(s: &Session) -> (bool, bool, bool) {
    let mut st = CascadeStore::new();
    let planner = st.begin();
    if !st.commit(planner, &[(s.plan_cell, s.plan_value)]) {
        return (false, false, false);
    }
    let executor = st.begin();
    st.read(executor, s.plan_cell);
    st.commit(executor, &[(s.result_cell, s.result_value)]);
    if s.retracted {
        st.abort(planner);
    }
    let trace = provenance_of(&st.inner);
    (
        detect_a3(&trace).is_some(),
        detect_a3_unpropagated(&trace).is_some(),
        st.inner.txns[executor as usize].externalized,
    )
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
        let (g_a3, g_released) = replay_guarded(&sess(true));
        let (u_a3, u_released) = replay_unguarded(&sess(true));
        assert!(!g_a3, "verified runtime admitted A3 on a retracted session");
        assert!(!g_released, "output commit released the executor of a retracted plan");
        assert!(u_a3, "the unguarded baseline must exhibit A3, or the comparison is vacuous");
        assert!(u_released, "the baseline releases at commit");
    }
    #[test]
    fn the_superseded_design_relabels_the_executor_after_its_effect_is_out() {
        let (a3, overruled, released) = replay_cascade(&sess(true));
        assert!(released, "this design releases at commit");
        assert!(!overruled, "the cascade flags the executor, so the overruled predicate is satisfied");
        assert!(a3, "and the executor's effect is out on a retracted plan all the same");
        let (a3, overruled, released) = replay_cascade(&sess(false));
        assert!(!a3 && !overruled && released, "a kept plan is clean under every predicate");
    }
    #[test]
    fn no_retraction_means_no_a3_anywhere_and_the_executor_releases() {
        let (g_a3, g_released) = replay_guarded(&sess(false));
        let (u_a3, u_released) = replay_unguarded(&sess(false));
        assert!(!g_a3 && !u_a3);
        assert!(g_released && u_released, "a kept plan must release its executor in both arms");
    }
}
