//! Actual source-scope controls only. No fixture fabricates a Host, SDK,
//! CompletedObjectCompile, foreign retirement or published object owner.
use std::time::Duration;

use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};

use super::*;

#[test]
fn object_deadline_is_one_restriction_inside_long_or_short_original_root_lifetime() {
    let started = Instant::now();
    let hour = Duration::from_nanos(object::MAX_COMPILE_NS);
    let long_root = started + hour + hour;
    assert_eq!(operation_deadline(long_root, started).unwrap(), started + hour);
    let short_root = started + Duration::from_secs(30);
    assert_eq!(operation_deadline(short_root, started).unwrap(), short_root);
    assert_eq!(
        operation_deadline(Instant::now(), started).unwrap_err().kind(),
        io::ErrorKind::TimedOut
    );
}

#[test]
fn actual_source_directory_restore_cannot_reuse_original_parent_bookends() {
    let directory = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(directory.path()).unwrap();
    std::fs::create_dir_all(root.join("src/bootstrap")).unwrap();
    std::fs::write(root.join("src/bootstrap/native_object.rs"), object::SOURCE_BYTES).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual source parent ABA control".into(),
            contract: "same original source owner; no Host/SDK/release grant".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let until = Instant::now() + Duration::from_secs(60);
    let scope = ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), until).unwrap();
    let original = scope.original_source(&root).unwrap();
    let (file, parents) = open_source(&original, until).unwrap();
    parents.check(&original, until).unwrap();
    let root_before = fd_stamp(original.directory().unwrap()).unwrap();
    let file_before = source_stamp(&file.metadata().unwrap());
    let selected = root.join("src/bootstrap");
    let saved = root.join("src/original-bootstrap");
    std::fs::rename(&selected, &saved).unwrap();
    std::fs::create_dir(&selected).unwrap();
    std::fs::write(
        selected.join("native_object.rs"),
        b"different source visible during the compiler read",
    )
    .unwrap();
    std::fs::remove_dir_all(&selected).unwrap();
    std::fs::rename(&saved, &selected).unwrap();
    assert_eq!(
        fd_stamp(original.directory().unwrap()).unwrap(),
        root_before,
        "Root/File-only stamps miss this actual nested namespace mutation"
    );
    assert_eq!(source_stamp(&file.metadata().unwrap()), file_before);
    let (restored, restored_parents) = open_source(&original, until).unwrap();
    assert_eq!(
        source_stamp(&restored.metadata().unwrap()),
        file_before,
        "a fresh source lookup sees restored original A"
    );
    assert!(
        parents.check(&original, until).is_err(),
        "the originally retained parent descriptions must permanently refuse ABA"
    );
    drop((restored, restored_parents, file, parents, original));
    drop(scope.seal().join().unwrap());
}

#[test]
fn actual_source_parent_identities_cannot_be_the_mutating_output_root() {
    let directory = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(directory.path()).unwrap();
    std::fs::create_dir_all(root.join("src/bootstrap")).unwrap();
    std::fs::write(root.join("src/bootstrap/native_object.rs"), object::SOURCE_BYTES).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual source/output namespace control".into(),
            contract: "identity restriction only".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let until = Instant::now() + Duration::from_secs(60);
    let scope = ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), until).unwrap();
    let original = scope.original_source(&root).unwrap();
    let (file, parents) = open_source(&original, until).unwrap();
    for observed in [&parents.root, &parents.src_stamp, &parents.bootstrap_stamp] {
        assert!(
            parents
                .exclude_output(trust_resource_controller::FileIdentity {
                    device: observed.0,
                    inode: observed.1
                })
                .is_err()
        );
    }
    let output = tempfile::tempdir().unwrap();
    let meta = std::fs::metadata(output.path()).unwrap();
    parents
        .exclude_output(trust_resource_controller::FileIdentity {
            device: meta.dev(),
            inode: meta.ino(),
        })
        .unwrap();
    parents.check(&original, until).unwrap();
    drop((file, parents, original));
    drop(scope.seal().join().unwrap());
}

#[test]
fn actual_selected_file_uses_original_manager_root_and_retains_its_captured_stamp() {
    let directory = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(directory.path()).unwrap();
    std::fs::create_dir_all(root.join("src/bootstrap")).unwrap();
    let path = root.join("src/bootstrap/native_object.rs");
    std::fs::write(&path, object::SOURCE_BYTES).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual native object source control".into(),
            contract: "source ownership only; no SDK, Host, CPU return or release".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected actual fixture contention"),
    };
    let scope = ProtectedWorkScope::new(
        Arc::new(lease.into_withheld().unwrap()),
        Instant::now() + Duration::from_secs(60),
    )
    .unwrap();
    let original = scope.original_source(&root).unwrap();
    let (file, parents) = open_source(&original, Instant::now() + Duration::from_secs(60)).unwrap();
    let captured = source_stamp(&file.metadata().unwrap());
    assert_eq!(captured.0, std::fs::metadata(&path).unwrap().dev());
    assert_eq!(captured.1, std::fs::metadata(&path).unwrap().ino());
    assert_eq!(unsafe { libc::lseek(file.as_raw_fd(), 7, libc::SEEK_SET) }, 7);
    let mut bytes = [0; object::SOURCE_BYTES.len()];
    file.read_exact_at(&mut bytes, 0).unwrap();
    assert_eq!(bytes.as_slice(), object::SOURCE_BYTES);
    assert_eq!(source_stamp(&file.metadata().unwrap()), captured);
    assert_eq!(unsafe { libc::lseek(file.as_raw_fd(), 0, libc::SEEK_CUR) }, 7);
    let mut changed = object::SOURCE_BYTES.to_vec();
    changed[0] ^= 1;
    std::fs::write(&path, &changed).unwrap();
    assert_ne!(
        source_stamp(&file.metadata().unwrap()),
        captured,
        "same-size mutation must invalidate the held original"
    );
    std::fs::write(&path, object::SOURCE_BYTES).unwrap();
    assert_ne!(
        source_stamp(&file.metadata().unwrap()),
        captured,
        "restored bytes cannot restore original ctime/bookend"
    );
    let bootstrap = root.join("src/bootstrap");
    std::fs::rename(&bootstrap, root.join("saved-bootstrap")).unwrap();
    std::os::unix::fs::symlink(root.join("saved-bootstrap"), &bootstrap).unwrap();
    assert!(
        open_source(&original, Instant::now() + Duration::from_secs(60)).is_err(),
        "actual parent alias must refuse"
    );
    drop((file, parents, original));
    drop(scope.seal().join().unwrap()); // Local zero-work join is NOT Host closure/release.
}
