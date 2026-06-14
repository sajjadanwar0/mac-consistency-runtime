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

    editor.begin(&["doc".to_string()], None).unwrap();
    reviewer.begin(&["doc".to_string()], None).unwrap();

    editor
        .commit(
            &[("doc".to_string(), "draft v1".to_string())],
            None,
        )
        .unwrap();

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
    assert_eq!(levels, vec![0], "vanilla edit-review should produce A_1");
}

#[test]
fn pessimistic_blocks_at_begin() {
    let (levels, _aborts, conflicts) = run_edit_review(Arc::new(PessimisticStore::new()));

    assert_eq!(levels, vec![4], "pessimistic should produce a clean trace");
    assert!(
        conflicts >= 1,
        "pessimistic should report at least one begin conflict"
    );
}

#[test]
fn si_aborts_on_validation() {
    let (levels, aborts, _) = run_edit_review(Arc::new(SnapshotIsolationStore::new()));
    assert_eq!(levels, vec![4], "SI should produce a clean trace");
    assert!(aborts >= 1, "SI should report at least one validation abort");
}

#[test]
fn si_default_misses_no_write_stale() {
    let store: Arc<dyn Store> = Arc::new(SnapshotIsolationStore::new());
    let emitter = Arc::new(VecEmitter::new());
    let reporter = Agent::new("rep", store.clone(), emitter.clone(), vec![]);
    let triager = Agent::new("tri", store.clone(), emitter.clone(), vec![]);

    reporter.begin(&[], None).unwrap();
    reporter
        .commit(&[("ticket".to_string(), "v0".to_string())], None)
        .unwrap();
    reporter.begin(&[], None).unwrap();

    triager.begin(&["ticket".to_string()], None).unwrap();

    reporter
        .commit(&[("ticket".to_string(), "v1".to_string())], None)
        .unwrap();

    let success = triager.no_write_commit(None).unwrap();
    assert!(
        success,
        "SI default should let the no-write commit succeed (this is the gap)"
    );

    let records = emitter.drain();

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

    let success = triager.no_write_commit(None).unwrap();
    assert!(!success, "SSI should abort the no-write commit");

    let records = emitter.drain();
    let level = classify_level(&records);
    assert_eq!(level, 4, "SSI should prevent A_1 in this scenario");
    assert!(store.aborts() >= 1);
}
