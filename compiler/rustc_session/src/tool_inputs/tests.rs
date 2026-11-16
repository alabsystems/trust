use super::*;

#[test]
#[allow(rustc::bad_opt_access)]
fn parsed_native_v2_mode_is_explicit_and_hosted_v3_never_downgrades() {
    let mut opts = crate::config::Options::default();
    assert_eq!(local_profile_for_options(&opts), Some(Profile::LocalUnixNativeV1));
    opts.resource_worker_v2 = true;
    assert_eq!(local_profile_for_options(&opts), Some(Profile::LocalUnixNativeResourceV2));
    opts.resource_worker_v3 = true;
    assert_eq!(local_profile_for_options(&opts), None);
    opts.resource_worker_v2 = false;
    assert_eq!(local_profile_for_options(&opts), None);
}

#[test]
fn disabled_collection_never_publishes_a_marker() {
    let mut collection = Collection::new(false);
    collection.unavailable();
    assert!(!collection.started());
    assert!(collection.terminal().is_none());
}

#[test]
fn completed_no_link_unit_uses_the_actual_shared_empty_envelope() {
    let mut collection = Collection::new(true);
    let Some(Terminal::Available(bytes)) = collection.terminal() else {
        panic!("completed no-link unit lost its empty envelope");
    };
    assert!(ToolInputs::decode(&bytes).unwrap().records().is_empty());
    assert!(matches!(collection.terminal(), Some(Terminal::Unavailable)));
}

#[test]
fn missing_owning_wait_and_capture_failure_remain_unavailable() {
    let mut unwaited = Collection::new(true);
    assert!(unwaited.started());
    assert!(matches!(unwaited.terminal(), Some(Terminal::Unavailable)));

    let mut failed = Collection::new(true);
    assert!(failed.started());
    failed.finished(None);
    assert!(!failed.started());
    assert!(matches!(failed.terminal(), Some(Terminal::Unavailable)));
}

#[test]
fn attempt_limit_withholds_collection_instead_of_growing_without_bound() {
    let mut collection = Collection::new(true);
    for _ in 0..MAX_RECORDS {
        assert!(collection.started());
    }
    assert!(!collection.started());
    assert!(matches!(collection.terminal(), Some(Terminal::Unavailable)));
}
