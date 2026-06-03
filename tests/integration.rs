//! End-to-end integration test: run an edit-review pattern through all
//! three runtimes and assert detector outcomes match the paper's claims.

use agent_consistency_runtime::{
    classify_level, Agent, PessimisticStore, SnapshotIsolationStore, Store, VanillaStore,
    VecEmitter,
};
use std::sync::Arc;

fn run_edit_review(store: Arc<dyn Store>) -> (Vec<u8>, u64, u64) {
    let emitter = Arc::new(VecEmitter::new());
    let editor = Agent::new(
        "editor",
        store.clone(),
        emitter.clone(),
        vec!["code".to_string(), "review".to_string()],
    );
    let reviewer = Agent::new(
        "reviewer",
        store.clone(),
        emitter.clone(),
        vec!["code".to_string(), "review".to_string()],
    );

    // Both agents begin reading 'doc' at the same snapshot.
    editor.begin(&["doc".to_string()], None).unwrap();
    reviewer.begin(&["doc".to_string()], None).unwrap();

    // Editor commits a write to 'doc'.
    editor
        .commit(
            &[("doc".to_string(), "draft v1".to_string())],
            None,
        )
        .unwrap();

    // Reviewer attempts to commit a different write to 'doc'.
    reviewer
        .commit(
            &[("doc".to_string(), "review v1".to_string())],
            None,
        )
        .unwrap();

    let records = emitter.drain();
    let levels: Vec<u8> = vec![classify_level(&records)];
    (levels, store.aborts(), store.begin_conflicts())
}

#[test]
fn vanilla_admits_a1() {
    let (levels, _, _) = run_edit_review(Arc::new(VanillaStore::new()));
    // L_0 means A_1 fired.
    assert_eq!(levels, vec![0], "vanilla edit-review should produce A_1");
}

#[test]
fn pessimistic_blocks_at_begin() {
    let (levels, _aborts, conflicts) = run_edit_review(Arc::new(PessimisticStore::new()));
    // Reviewer's begin failed (cell held by editor); reviewer's commit dropped.
    // Trace has only editor's record; classify_level should be L_4 (clean).
    assert_eq!(levels, vec![4], "pessimistic should produce a clean trace");
    assert!(
        conflicts >= 1,
        "pessimistic should report at least one begin conflict"
    );
}

#[test]
fn si_aborts_on_validation() {
    let (levels, aborts, _) = run_edit_review(Arc::new(SnapshotIsolationStore::new()));
    // Both agents read the same snapshot; editor commits first; reviewer's
    // commit fails validation (editor's write is at commit_time > read_time).
    // Trace has only editor's record.
    assert_eq!(levels, vec![4], "SI should produce a clean trace");
    assert!(aborts >= 1, "SI should report at least one validation abort");
}

#[test]
fn si_default_misses_no_write_stale() {
    // Reproduce the SI/triage 3% finding (SI default does not validate
    // no-write commits).
    let store: Arc<dyn Store> = Arc::new(SnapshotIsolationStore::new());
    let emitter = Arc::new(VecEmitter::new());
    let reporter = Agent::new("rep", store.clone(), emitter.clone(), vec![]);
    let triager = Agent::new("tri", store.clone(), emitter.clone(), vec![]);

    reporter.begin(&[], None).unwrap();
    reporter
        .commit(&[("ticket".to_string(), "v0".to_string())], None)
        .unwrap();
    reporter.begin(&[], None).unwrap();

    // Triager begins between reporter's two writes.
    triager.begin(&["ticket".to_string()], None).unwrap();

    // Reporter writes 'ticket' again.
    reporter
        .commit(&[("ticket".to_string(), "v1".to_string())], None)
        .unwrap();

    // Triager commits with no writes — SI default does NOT validate.
    let success = triager.no_write_commit(None).unwrap();
    assert!(
        success,
        "SI default should let the no-write commit succeed (this is the gap)"
    );

    let records = emitter.drain();
    // Detector should fire A_1 on this trace.
    let level = classify_level(&records);
    assert_eq!(level, 0, "A_1 should fire on the SI/triage shape");
}

#[test]
fn ssi_mode_closes_no_write_gap() {
    let store: Arc<dyn Store> = Arc::new(SnapshotIsolationStore::with_ssi(true));
    let emitter = Arc::new(VecEmitter::new());
    let reporter = Agent::new("rep", store.clone(), emitter.clone(), vec![]);
    let triager = Agent::new("tri", store.clone(), emitter.clone(), vec![]);

    reporter.begin(&[], None).unwrap();
    reporter
        .commit(&[("ticket".to_string(), "v0".to_string())], None)
        .unwrap();

    triager.begin(&["ticket".to_string()], None).unwrap();

    reporter.begin(&[], None).unwrap();
    reporter
        .commit(&[("ticket".to_string(), "v1".to_string())], None)
        .unwrap();

    // Under SSI mode, the triager's no-write commit DOES validate, sees
    // the concurrent write, and aborts.
    let success = triager.no_write_commit(None).unwrap();
    assert!(!success, "SSI should abort the no-write commit");

    let records = emitter.drain();
    // Trace has only the reporter's records: detector should NOT fire A_1.
    let level = classify_level(&records);
    assert_eq!(level, 4, "SSI should prevent A_1 in this scenario");
    assert!(store.aborts() >= 1);
}
