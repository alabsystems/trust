use std::time::Duration;

use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};

use super::*;

fn actual() -> (tempfile::TempDir, CommandOwner) {
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "embedded Preparation ownership control".into(),
        contract: "actual manager exclusion only; no Host/SDK/release authority".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected original fixture contention"),
    };
    (root, Arc::new(CommandOwnership::new(lease)))
}

fn plan(root: &std::path::Path) -> Plan {
    Plan {
        source: root.to_owned(),
        output: root.join("out"),
        jobs: 1,
        llvm_link_jobs: Some(1),
        frontend_threads: Some(1),
        dry_run: false,
        native_object_leaf: false,
    }
}

fn isolated(name: &str) -> bool {
    const ROLE: &str = "TRUST_ENGINE_SCOPE_TEST_ACTOR";
    if std::env::var(ROLE).as_deref() == Ok(name) {
        return false;
    }
    let result = crate::test_entry::uncaptured_actor(std::process::Command::new(
        std::env::current_exe().unwrap(),
    ))
    .args(["--exact", name, "--nocapture"])
    .env(ROLE, name)
    .output()
    .unwrap();
    assert!(result.status.success(), "actual ownership actor failed: {result:?}");
    assert!(String::from_utf8(result.stdout).unwrap().contains("scope-control-checked"));
    true
}

#[test]
fn preparation_requires_the_same_actual_owner_and_never_releases_on_unknown_drop() {
    if isolated(
        "engine::scope::tests::preparation_requires_the_same_actual_owner_and_never_releases_on_unknown_drop",
    ) {
        return;
    }
    let (root, original) = actual();
    let (_other_root, other) = actual();
    let mut prepared = Preparation::new(plan(root.path()), Some(&original))
        .protect(Instant::now() + Duration::from_secs(20))
        .unwrap();
    let output_root = tempfile::tempdir().unwrap();
    let output = Arc::new(
        build_helper::trust_output_lock::OutputLock::try_acquire(output_root.path())
            .unwrap()
            .unwrap(),
    );
    let actual_output = Arc::downgrade(&output);
    prepared
        .retain_build_ownership(Arc::new(
            BuildOwnership::new(output, Arc::clone(&original)).unwrap(),
        ))
        .unwrap();
    let dispatch = prepared.scope.as_ref().unwrap().dispatcher();
    // Reject BEFORE installing the process-wide dispatcher. Equal paths,
    // records or an unrelated actual lease cannot replace original custody.
    assert!(prepared.install(Some(&other)).is_err());
    assert!(
        Preparation::new(plan(root.path()), Some(&original))
            .protect(Instant::now() + Duration::from_secs(20))
            .is_err()
    );
    drop(crate::engine::Outcome::in_scope(None, prepared));
    assert!(dispatch.register_launch().is_err(), "abandonment must seal existing aliases");
    drop(original);
    actual_output
        .upgrade()
        .expect("unknown closure must retain the SAME actual output guard")
        .check_current()
        .unwrap();
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("scope-control-checked");
}

#[test]
fn expired_preparation_refuses_before_withholding_the_unused_actual_lease() {
    if isolated(
        "engine::scope::tests::expired_preparation_refuses_before_withholding_the_unused_actual_lease",
    ) {
        return;
    }
    let (root, original) = actual();
    assert!(Preparation::new(plan(root.path()), Some(&original)).protect(Instant::now()).is_err());
    drop(original);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("scope-control-checked");
}

#[test]
fn foreign_configured_source_refuses_before_changing_the_actual_unused_lease() {
    if isolated(
        "engine::scope::tests::foreign_configured_source_refuses_before_changing_the_actual_unused_lease",
    ) {
        return;
    }
    let (root, original) = actual();
    let foreign = tempfile::tempdir().unwrap();
    let info = root.path().join(".trust-build-lock/info");
    let before = std::fs::read(&info).unwrap();
    assert!(
        Preparation::new(plan(foreign.path()), Some(&original))
            .protect(Instant::now() + Duration::from_secs(20))
            .is_err()
    );
    assert_eq!(std::fs::read(&info).unwrap(), before);
    original.check_original_source(root.path()).unwrap();
    // A correct subsequent preparation consumes the same still-unused Lease.
    let scope = Preparation::new(plan(root.path()), Some(&original))
        .protect(Instant::now() + Duration::from_secs(20))
        .unwrap();
    assert_eq!(scope.source_root.as_ref().unwrap().path(), root.path().canonicalize().unwrap());
    drop(scope);
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("scope-control-checked");
}
