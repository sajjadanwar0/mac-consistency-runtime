// lib_l4_exec.rs
// ---------------------------------------------------------------------------
// Exec-mode L_4: an EXECUTABLE registry and dispatcher, verified to dispatch
// a call only against the live binding its operation planned for, under
// arbitrary registry churn (re-signing and revocation).
//
// COMPILE
//   verus --crate-type=lib src/lib_l4_exec.rs
//
// RELATION TO THE MODEL (lib_l4_safety.rs)
//   The model proves validation at dispatch as an invariant over executions
//   with churn, and exhibits A_2 for unvalidated and snapshot-resolved
//   dispatch. This file is its executable counterpart: PinnedOp::dispatch
//   decides commit_valid against the live registry and refuses otherwise.
//   Self-contained (no `mod`, no textual re-inclusion); the correspondence
//   to the model's steps is by inspection.
//
// 2026-09-16  round 29 (audit finding G2). OVERRULED: the previous exec
//   capstone dispatched from the operation's own snapshot and proved
//   `!a2_witness_exec(planned, pinned_sig, snapshot)` -- the snapshot compared
//   with itself -- while the live registry was not an input at all. A call
//   resolved from a snapshot still reaches the live tool, so that dispatcher
//   is exactly the one that calls revoked or re-signed tools.
//
// THEOREMS
//   * L4Registry::resign / revoke: churn, with the precondition checked at
//     run time rather than required;
//   * PinnedOp::pin: the pinned signature is the live signature at plan time;
//   * PinnedOp::dispatch: returns Some exactly when dispatching against the
//     live registry is not an A_2 witness, and then returns the pinned
//     signature;
//   * lemma_revocation_after_pin_is_a2 / lemma_resigning_after_pin_is_a2: a
//     dispatcher that does not consult the live registry (a snapshot) calls a
//     phantom after either kind of churn;
//   * revoked_tool_is_refused / resigned_tool_is_refused /
//     unchanged_tool_is_dispatched: concrete executions of the runtime.
//
// TRUST BASE: zero axioms, zero external_body, zero assume, zero admit.
// ---------------------------------------------------------------------------

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

/// A_2 at the exec representation: dispatching `planned` against the live
/// registry `live` reaches a tool that is missing, revoked, or re-signed
/// since the operation pinned `pinned`.
pub open spec fn a2_witness_exec(planned: usize, pinned: u64, live: Seq<Option<u64>>) -> bool {
    planned as int >= live.len() || live[planned as int] != Some(pinned)
}

pub struct L4Registry {
    /// sigs[t] = Some(current signature of tool t), or None once revoked
    pub sigs: Vec<Option<u64>>,
}

impl L4Registry {
    pub fn new(n: usize, init: u64) -> (r: Self)
        ensures
            r.sigs@.len() == n as int,
            forall |t: int| 0 <= t < n as int ==> #[trigger] r.sigs@[t] == Some(init),
    {
        let mut sigs: Vec<Option<u64>> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                sigs@.len() == k as int,
                forall |t: int| 0 <= t < k as int ==> #[trigger] sigs@[t] == Some(init),
            decreases n - k,
        {
            sigs.push(Some(init));
            k = k + 1;
        }
        L4Registry { sigs }
    }

    /// Churn: re-sign tool `t`, at any time, including between an
    /// operation's plan and its dispatch.
    pub fn resign(&mut self, t: usize, sig: u64) -> (ok: bool)
        ensures
            ok == ((t as int) < old(self).sigs@.len()),
            ok ==> final(self).sigs@ =~= old(self).sigs@.update(t as int, Some(sig)),
            !ok ==> final(self).sigs@ =~= old(self).sigs@,
    {
        if t >= self.sigs.len() {
            return false;
        }
        self.sigs.set(t, Some(sig));
        true
    }

    /// Churn: revoke tool `t`.
    pub fn revoke(&mut self, t: usize) -> (ok: bool)
        ensures
            ok == ((t as int) < old(self).sigs@.len()),
            ok ==> final(self).sigs@ =~= old(self).sigs@.update(t as int, None),
            !ok ==> final(self).sigs@ =~= old(self).sigs@,
    {
        if t >= self.sigs.len() {
            return false;
        }
        self.sigs.set(t, None);
        true
    }
}

pub struct PinnedOp {
    pub planned_tool: usize,
    pub pinned_sig:   u64,
}

impl PinnedOp {
    /// PLAN: pin the live signature of the planned tool; None if the tool is
    /// not live.
    pub fn pin(reg: &L4Registry, tool: usize) -> (r: Option<PinnedOp>)
        ensures
            (r is Some) == ((tool as int) < reg.sigs@.len() && reg.sigs@[tool as int] is Some),
            r is Some ==> r->0.planned_tool == tool && reg.sigs@[tool as int] == Some(r->0.pinned_sig),
    {
        if tool >= reg.sigs.len() {
            return None;
        }
        match reg.sigs[tool] {
            Some(sig) => Some(PinnedOp { planned_tool: tool, pinned_sig: sig }),
            None => None,
        }
    }

    /// DISPATCH, validated against the LIVE registry at call time: Some(sig)
    /// is the binding the call may use; None means the tool was revoked or
    /// re-signed since the plan, and the caller aborts instead of calling.
    pub fn dispatch(&self, reg: &L4Registry) -> (r: Option<u64>)
        ensures
            (r is Some) == !a2_witness_exec(self.planned_tool, self.pinned_sig, reg.sigs@),
            r is Some ==> r->0 == self.pinned_sig,
    {
        if self.planned_tool >= reg.sigs.len() {
            return None;
        }
        match reg.sigs[self.planned_tool] {
            Some(sig) => {
                if sig == self.pinned_sig {
                    Some(sig)
                } else {
                    None
                }
            }
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Non-vacuity: a dispatcher that ignores the live registry calls a phantom
// ---------------------------------------------------------------------------

pub proof fn lemma_revocation_after_pin_is_a2(live0: Seq<Option<u64>>, t: usize, pinned: u64)
    requires
        (t as int) < live0.len(),
        live0[t as int] == Some(pinned),
    ensures
        !a2_witness_exec(t, pinned, live0),
        a2_witness_exec(t, pinned, live0.update(t as int, None)),
{
    let live1 = live0.update(t as int, None);
    assert(live1.len() == live0.len());
    assert(live1[t as int] == None::<u64>);
}

pub proof fn lemma_resigning_after_pin_is_a2(live0: Seq<Option<u64>>, t: usize, pinned: u64, new_sig: u64)
    requires
        (t as int) < live0.len(),
        live0[t as int] == Some(pinned),
        new_sig != pinned,
    ensures
        a2_witness_exec(t, pinned, live0.update(t as int, Some(new_sig))),
{
    let live1 = live0.update(t as int, Some(new_sig));
    assert(live1.len() == live0.len());
    assert(live1[t as int] == Some(new_sig));
}

// ---------------------------------------------------------------------------
// Concrete executions of the runtime
// ---------------------------------------------------------------------------

/// Plan against tool 1, revoke it, dispatch: refused.
pub fn revoked_tool_is_refused() -> (r: Option<u64>)
    ensures
        r is None,
{
    let mut reg = L4Registry::new(2, 5);
    match PinnedOp::pin(&reg, 1) {
        Some(op) => {
            let _ = reg.revoke(1);
            op.dispatch(&reg)
        }
        None => None,
    }
}

/// Plan against tool 1, re-sign it, dispatch: refused.
pub fn resigned_tool_is_refused() -> (r: Option<u64>)
    ensures
        r is None,
{
    let mut reg = L4Registry::new(2, 5);
    match PinnedOp::pin(&reg, 1) {
        Some(op) => {
            let _ = reg.resign(1, 6);
            op.dispatch(&reg)
        }
        None => None,
    }
}

/// Plan against tool 1, churn tool 0 only, dispatch: the planned binding.
pub fn unchanged_tool_is_dispatched() -> (r: Option<u64>)
    ensures
        r == Some(5u64),
{
    let mut reg = L4Registry::new(2, 5);
    let pinned = PinnedOp::pin(&reg, 1);
    assert(pinned is Some);
    match pinned {
        Some(op) => {
            let _ = reg.revoke(0);
            op.dispatch(&reg)
        }
        None => None,
    }
}

} // verus!
