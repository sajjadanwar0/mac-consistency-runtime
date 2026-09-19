//! 2026-09-15  round 21. can_commit's predecessor refusal, driven through the
//! public L2Runtime API of src/l2_exec.rs (the bytes Verus verified in the pilot).
//!
//! The existing L2 tests retract a writer AFTER its reader has read. The abort
//! cascade then marks that reader aborted, and can_commit refuses on the reader's
//! own `aborted` flag, so the branch that refuses because a PREDECESSOR is aborted
//! was never reached: with that branch disabled in src/l2_exec.rs, all 32 tests
//! still passed. Reading a retracted writer's published value reaches it -- the
//! cascade has already run, the reader is not marked, and only the predecessor
//! check stands between it and a commit.
//!
//! Every call is one the runtime accepts, and the tests assert that it did:
//! since round 26 each entry point checks its own precondition and refuses
//! otherwise.

use agent_consistency_runtime::l2_exec::L2Runtime;

#[test]
fn a_reader_of_a_retracted_writer_cannot_commit() {
    let mut rt = L2Runtime::new();
    let w = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.write(w, 7, 70), "L2Runtime::write refused");
    assert!(rt.can_commit(w), "a writer with no reads must be committable");
    assert!(rt.commit(w), "L2Runtime::commit refused");
    let clean = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.read(clean, 7), "L2Runtime::read refused");
    assert!(
        rt.can_commit(clean),
        "a reader of a committed, unretracted writer must be committable, or the refusal below proves nothing"
    );

    assert!(rt.abort(w), "L2Runtime::abort refused");
    let r = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.read(r, 7), "L2Runtime::read refused");
    assert!(
        !rt.can_commit(r),
        "can_commit admitted a reader whose predecessor was aborted"
    );
}

#[test]
fn a_reader_two_hops_from_a_retracted_writer_cannot_commit() {
    let mut rt = L2Runtime::new();
    let w = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.write(w, 1, 10), "L2Runtime::write refused");
    assert!(rt.can_commit(w), "a writer with no reads must be committable");
    assert!(rt.commit(w), "L2Runtime::commit refused");
    let m = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.read(m, 1), "L2Runtime::read refused");
    assert!(rt.write(m, 2, 20), "L2Runtime::write refused");
    assert!(rt.can_commit(m), "a reader of a committed, unretracted writer must be committable");
    assert!(rt.commit(m), "L2Runtime::commit refused");
    assert!(rt.abort(w), "L2Runtime::abort refused");
    let r = rt.begin().expect("L2Runtime counters exhausted");
    assert!(rt.read(r, 2), "L2Runtime::read refused");
    assert!(
        !rt.can_commit(r),
        "can_commit admitted a reader whose predecessor's predecessor was aborted"
    );
}
