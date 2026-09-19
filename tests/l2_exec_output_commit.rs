//! 2026-09-16  round 26. Output commit and the self-checking entry points of
//! src/l2_exec.rs (the bytes Verus verified in the pilot), driven through the
//! public L2Runtime API.
//!
//! A committed transaction's effects may leave the runtime only once every
//! transaction in its causal closure has left (externalize), and from then on
//! it cannot be retracted. An erased build does not check `requires`, so every
//! mutating entry point checks its own precondition, returns whether it acted,
//! and leaves the runtime unchanged when it refuses.

use agent_consistency_runtime::l2_exec::L2Runtime;

fn begin(rt: &mut L2Runtime) -> u64 {
    rt.begin().expect("L2Runtime counters exhausted")
}

fn committed_writer(rt: &mut L2Runtime, cell: u64, value: u64) -> u64 {
    let w = begin(rt);
    assert!(rt.write(w, cell, value), "write refused");
    assert!(rt.commit(w), "commit refused");
    w
}

#[test]
fn a_dependent_externalizes_only_after_its_predecessor() {
    let mut rt = L2Runtime::new();
    let w = committed_writer(&mut rt, 1, 10);
    let d = begin(&mut rt);
    assert!(rt.read(d, 1), "read refused");
    assert!(rt.write(d, 2, 20), "write refused");
    assert!(rt.commit(d), "commit refused");

    assert!(!rt.can_externalize(d), "can_externalize admitted a dependent before its predecessor");
    assert!(!rt.externalize(d), "externalize let a dependent out before its predecessor");
    assert!(rt.externalize(w), "a committed transaction with no predecessors must be able to externalize");
    assert!(rt.can_externalize(d), "can_externalize refused a dependent whose predecessor is out");
    assert!(rt.externalize(d), "externalize refused a dependent whose predecessor is out");
}

#[test]
fn an_externalized_transaction_cannot_be_retracted() {
    let mut rt = L2Runtime::new();
    let w = committed_writer(&mut rt, 1, 10);
    assert!(rt.externalize(w), "externalize refused");
    let now = rt.now;
    assert!(!rt.abort(w), "abort retracted a transaction whose effects are out");
    assert_eq!(rt.now, now, "a refused abort changed the runtime");
    assert!(!rt.txns.get(&w).unwrap().aborted, "a refused abort marked the transaction aborted");
}

#[test]
fn retraction_before_externalization_aborts_the_dependent() {
    let mut rt = L2Runtime::new();
    let w = committed_writer(&mut rt, 1, 10);
    let d = begin(&mut rt);
    assert!(rt.read(d, 1), "read refused");
    assert!(rt.commit(d), "commit refused");

    assert!(rt.abort(w), "a committed transaction that has not externalized must stay retractable");
    assert!(rt.txns.get(&d).unwrap().aborted, "the cascade did not reach the dependent");
    assert!(!rt.externalize(d), "a dependent of a retracted transaction got out");
    assert!(!rt.externalize(w), "a retracted transaction got out");
}

#[test]
fn every_entry_point_refuses_without_changing_the_runtime() {
    let mut rt = L2Runtime::new();
    let w = committed_writer(&mut rt, 1, 10);
    let r = begin(&mut rt);
    let now = rt.now;
    assert!(!rt.write(w, 1, 11), "write accepted a committed transaction");
    assert!(!rt.write(999, 1, 11), "write accepted an unknown transaction");
    assert!(!rt.read(r, 42), "read accepted a cell with no committed value");
    assert!(!rt.read(999, 1), "read accepted an unknown transaction");
    assert!(!rt.commit(999), "commit accepted an unknown transaction");
    assert!(!rt.abort(999), "abort accepted an unknown transaction");
    assert!(!rt.externalize(999), "externalize accepted an unknown transaction");
    assert!(!rt.externalize(r), "externalize accepted an uncommitted transaction");
    assert_eq!(rt.now, now, "a refused call changed the runtime");
}

#[test]
fn commit_decides_commit_valid_itself() {
    let mut rt = L2Runtime::new();
    committed_writer(&mut rt, 1, 10);
    let stale = begin(&mut rt);
    assert!(rt.read(stale, 1), "read refused");
    committed_writer(&mut rt, 1, 11);
    let now = rt.now;
    assert!(!rt.commit(stale), "commit accepted a stale read; before round 26 only can_commit checked");
    assert_eq!(rt.now, now, "a refused commit changed the runtime");
    assert!(!rt.txns.get(&stale).unwrap().committed, "a refused commit marked the transaction committed");
}

#[test]
fn begin_refuses_when_its_counters_are_exhausted() {
    let mut rt = L2Runtime::new();
    // `now` is a public field; setting it is the only way to reach an
    // exhausted counter in a test.
    rt.now = u64::MAX;
    assert!(rt.begin().is_none(), "begin handed out a transaction with its clock exhausted");
    assert_eq!(rt.next_txn, 0, "a refused begin allocated an id");
}
