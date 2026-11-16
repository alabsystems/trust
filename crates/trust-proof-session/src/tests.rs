use super::*;

#[test]
fn distinct_original_sessions_have_fresh_private_inputs() {
    let parent = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let parent = parent.path().canonicalize().unwrap();
    let first = VerificationSession::create_in(&parent).unwrap();
    let second = VerificationSession::create_in(&parent).unwrap();
    assert_ne!(first.id(), second.id());
    for session in [&first, &second] {
        assert_eq!(session.id().len(), 64);
        assert!(
            session
                .id()
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        );
        session.check_current().unwrap();
        assert!(session.artifact_root().starts_with(&parent));
        assert!(session.artifact_root().is_dir());
    }
    assert_ne!(first.artifact_root(), second.artifact_root());
    let original = first.artifact_root().to_owned();
    drop(first);
    assert!(!original.exists());
    second.check_current().unwrap();
}

#[cfg(unix)]
#[test]
fn original_session_refuses_replacement_and_restoration_without_deleting_foreign_bytes() {
    let parent = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let parent = parent.path().canonicalize().unwrap();
    let session = VerificationSession::create_in(&parent).unwrap();
    let original = session.artifact_root().to_owned();
    let displaced = parent.join("actual-original");
    fs::write(original.join("original-input"), b"actual original").unwrap();
    fs::rename(&original, &displaced).unwrap();
    fs::create_dir(&original).unwrap();
    use std::os::unix::fs::PermissionsExt as _;
    fs::set_permissions(&original, fs::Permissions::from_mode(0o700)).unwrap();
    fs::write(original.join("foreign-input"), b"keep foreign").unwrap();
    assert!(session.check_current().is_err());
    drop(session);
    assert_eq!(
        fs::read(original.join("foreign-input")).unwrap(),
        b"keep foreign"
    );
    assert_eq!(
        fs::read(displaced.join("original-input")).unwrap(),
        b"actual original"
    );

    let restored = VerificationSession::create_in(&parent).unwrap();
    let named = restored.artifact_root().to_owned();
    let away = parent.join("restore-original");
    fs::rename(&named, &away).unwrap();
    assert!(restored.check_current().is_err());
    fs::rename(&away, &named).unwrap();
    assert!(
        restored.check_current().is_err(),
        "a restored namespace cannot erase observed loss"
    );
    drop(restored);
    assert!(named.is_dir(), "poisoned original inputs stay available");
}

#[cfg(unix)]
#[test]
fn original_session_privacy_failure_is_sticky() {
    use std::os::unix::fs::PermissionsExt as _;
    let session = VerificationSession::create().unwrap();
    fs::set_permissions(session.artifact_root(), fs::Permissions::from_mode(0o755)).unwrap();
    assert!(session.check_current().is_err());
    fs::set_permissions(session.artifact_root(), fs::Permissions::from_mode(0o700)).unwrap();
    assert!(session.check_current().is_err());
    let path = session.artifact_root().to_owned();
    drop(session);
    assert!(path.is_dir());
    fs::remove_dir(path).unwrap();
}

#[cfg(unix)]
#[test]
fn session_output_does_not_follow_a_parent_alias() {
    let parent = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let actual = parent.path().canonicalize().unwrap();
    let alias = actual.join("alias");
    std::os::unix::fs::symlink(&actual, &alias).unwrap();
    assert!(VerificationSession::create_in(&alias).is_err());
    assert!(VerificationSession::create_in(Path::new("relative")).is_err());
}

#[test]
fn hint_session_prepares_only_bounded_untrusted_storage() {
    let home = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let home = home.path().canonicalize().unwrap();
    let session = VerificationSession::create()
        .unwrap()
        .with_proof_store(Some(&home));
    let pool = session.artifact_root().join(storage::DIRECTORY);
    assert!(pool.join("pool.json").is_file());
    assert_eq!(fs::read_dir(pool.join("incoming")).unwrap().count(), 0);
    let store = ProofArtifactStore::open(&home).unwrap();
    assert!(
        store
            .prune_to_budget(storage::MAX_SNAPSHOT_FILES + 1, storage::MAX_SNAPSHOT_BYTES)
            .is_err()
    );
    assert!(
        store
            .import(session.artifact_root(), "../pool.json")
            .is_err()
    );
    // Bytes in a hint store are deliberately not a favorable proof result.
    let name = format!("{}.json", "1".repeat(64));
    fs::write(store.objects_directory().join(&name), b"not a proof").unwrap();
    let imported = store
        .import(session.artifact_root(), &name)
        .unwrap()
        .unwrap();
    assert_eq!(fs::read(imported).unwrap(), b"not a proof");
}

#[cfg(unix)]
#[test]
fn native_relative_session_requires_actual_parent_and_retains_its_metadata_inputs() {
    use std::os::fd::AsFd as _;
    let container = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let base = container.path().canonicalize().unwrap();
    let root = base.join("actual-output");
    let foreign = base.join("foreign-output");
    fs::create_dir(&root).unwrap();
    fs::create_dir(&foreign).unwrap();
    let parent = File::open(&root).unwrap();
    let wrong_parent = File::open(&foreign).unwrap();
    assert!(VerificationSession::create_at(wrong_parent.as_fd(), &root).is_err());
    assert_eq!(fs::read_dir(&root).unwrap().count(), 0);
    assert_eq!(fs::read_dir(&foreign).unwrap().count(), 0);

    let session = VerificationSession::create_at(parent.as_fd(), &root).unwrap();
    let private = session.artifact_root().to_owned();
    let metadata = session.prepare_metadata().unwrap();
    assert!(
        session.prepare_metadata().is_err(),
        "an existing namespace is not fresh preparation"
    );
    fs::write(
        metadata.path().join("original-input"),
        b"retained actual metadata",
    )
    .unwrap();
    session.check_current().unwrap();
    metadata.check_current().unwrap();
    drop(metadata);
    drop(session);
    assert_eq!(
        fs::read(private.join("metadata/original-input")).unwrap(),
        b"retained actual metadata"
    );
    // Native output retirement/maintenance owns deletion, not this input Drop.
    assert!(private.is_dir());
}

#[cfg(unix)]
#[test]
fn native_parent_and_metadata_replacements_refuse_and_cannot_revive_after_restoration() {
    use std::os::fd::AsFd as _;
    let container = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let base = container.path().canonicalize().unwrap();
    let root = base.join("actual-output");
    fs::create_dir(&root).unwrap();
    let parent = File::open(&root).unwrap();
    let session = VerificationSession::create_at(parent.as_fd(), &root).unwrap();
    let metadata = session.prepare_metadata().unwrap();
    let original = metadata.path().to_owned();
    let displaced = session.artifact_root().join("held-metadata");
    fs::rename(&original, &displaced).unwrap();
    fs::create_dir(&original).unwrap();
    assert!(metadata.check_current().is_err());
    fs::remove_dir(&original).unwrap();
    fs::rename(&displaced, &original).unwrap();
    assert!(
        metadata.check_current().is_err(),
        "observed metadata loss stays failed"
    );
    drop(metadata);

    let held_root = base.join("held-original-output");
    fs::rename(&root, &held_root).unwrap();
    fs::create_dir(&root).unwrap();
    assert!(VerificationSession::create_at(parent.as_fd(), &root).is_err());
    assert_eq!(
        fs::read_dir(&root).unwrap().count(),
        0,
        "a wrong location cannot redirect mkdir"
    );
    assert!(session.check_current().is_err());
    fs::remove_dir(&root).unwrap();
    fs::rename(&held_root, &root).unwrap();
    assert!(
        session.check_current().is_err(),
        "the same name cannot reset the original failure"
    );
}

#[test]
fn hint_scan_refuses_excess_population_before_copy_or_deletion() {
    let home = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let home = home.path().canonicalize().unwrap();
    let store = ProofArtifactStore::open(&home).unwrap();
    let copy_parent = home.join("copy-parent");
    storage::private_dir(&copy_parent).unwrap();
    let output = copy_parent.join("output");
    storage::private_dir(&output).unwrap();
    let hint = format!("{}.json", "1".repeat(64));
    fs::write(
        store.objects_directory().join(&hint),
        b"untrusted mathematical bytes",
    )
    .unwrap();
    // Unrelated files count too: rejecting only after collecting matching keys leaves
    // the operation unbounded when a preexisting or concurrent producer adds junk.
    for index in 0..storage::MAX_DIRECTORY_ENTRIES {
        fs::write(
            store.objects_directory().join(format!("unrelated-{index}")),
            b"",
        )
        .unwrap();
    }
    assert!(storage::proof_files(store.objects_directory()).is_err());
    assert!(
        store
            .copy_to(store.objects_directory(), &output)
            .unwrap_err()
            .to_string()
            .contains("population exceeds bounded scan")
    );
    assert!(store.prune_to_budget(0, 0).is_err());
    assert_eq!(fs::read_dir(&output).unwrap().count(), 0);
    assert_eq!(
        fs::read(store.objects_directory().join(&hint)).unwrap(),
        b"untrusted mathematical bytes"
    );
    fs::remove_file(store.objects_directory().join("unrelated-0")).unwrap();
    assert_eq!(
        storage::proof_files(store.objects_directory())
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        store.copy_to(store.objects_directory(), &output).unwrap(),
        1
    );
    store.prune_to_budget(0, 0).unwrap();
    assert!(!store.objects_directory().join(&hint).exists());
    assert_eq!(
        fs::read(output.join(&hint)).unwrap(),
        b"untrusted mathematical bytes"
    );
}

#[cfg(unix)]
#[test]
fn native_relative_drop_closes_inputs_without_starting_deferred_hint_maintenance() {
    use std::os::fd::AsFd as _;
    let home = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let base = home.path().canonicalize().unwrap();
    let root = base.join("original-output");
    fs::create_dir(&root).unwrap();
    let parent = File::open(&root).unwrap();
    let store = ProofArtifactStore::open(&base).unwrap();
    let native = VerificationSession::create_at(parent.as_fd(), &root)
        .unwrap()
        .with_proof_store(Some(&base));
    let hint = store
        .objects_directory()
        .join(format!("{}.json", "2".repeat(64)));
    // A sparse oversized hint meaningfully distinguishes actual maintenance
    // from closing descriptors, without creating a large shared fixture.
    File::create(&hint)
        .unwrap()
        .set_len(storage::MAX_ARTIFACT_BYTES + 1)
        .unwrap();
    drop(native);
    assert!(
        hint.is_file(),
        "native deferred Drop cannot start unadmitted store I/O"
    );
    store.maintain().unwrap();
    assert!(
        !hint.exists(),
        "explicit native caller preparation owns maintenance"
    );

    let ordinary = VerificationSession::create()
        .unwrap()
        .with_proof_store(Some(&base));
    File::create(&hint)
        .unwrap()
        .set_len(storage::MAX_ARTIFACT_BYTES + 1)
        .unwrap();
    drop(ordinary);
    assert!(
        !hint.exists(),
        "ordinary frontend destructor behavior remains intact"
    );
}
