use std::fs;
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;
use std::time::{Duration, Instant};

use super::*;
use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager, WithheldLease};

fn original() -> (tempfile::TempDir, Arc<WithheldLease>) {
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "original source directory custody control".into(),
        contract: "same original directory only; no Host or release authority".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    (root, Arc::new(lease.into_withheld().unwrap()))
}

fn isolated(name: &str) -> bool {
    const ROLE: &str = "TRUST_ORIGINAL_SOURCE_ROOT_ACTOR";
    if std::env::var(ROLE).as_deref() == Ok(name) {
        return false;
    }
    let result = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", name, "--nocapture"])
        .env(ROLE, name)
        .output()
        .unwrap();
    assert!(result.status.success(), "actual source custody actor failed: {result:?}");
    assert!(String::from_utf8(result.stdout).unwrap().contains("source-root-checked"));
    true
}

fn isolated_current() -> bool {
    let current = std::thread::current();
    isolated(current.name().unwrap())
}

#[test]
fn close_only_offer_duplicates_actual_readonly_originals_without_moving_cursors() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let original = &scope.inner.original;
    let descriptors = [
        &original.original.manager.root.file,
        &original.original.held.directory,
        &original.original.held.file,
        &original.held.file,
    ];
    let flags = descriptors.map(|file| unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) });
    let local = descriptors.map(|file| unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) });
    for (index, descriptor) in descriptors.iter().enumerate().skip(2) {
        // Test setup gives each original a distinct cursor. Production offer
        // reads must be positional and its duplicates must share those OFDs.
        assert_eq!(
            unsafe { libc::lseek(descriptor.as_raw_fd(), index as i64, libc::SEEK_SET) },
            index as i64
        );
    }
    let offer = source.close_only_offer().unwrap();
    assert!(Arc::ptr_eq(&offer.inner, &scope.inner));
    assert_eq!(offer.identity(), scope.identity());
    assert_eq!(offer.deadline(), scope.inner.deadline);
    offer
        .with_descriptions(|offered, data| {
            assert_eq!(data.holder_leaf(), ".trust-build-lock");
            assert!(data.description_metadata()[0].is_dir());
            assert!(data.description_metadata()[1].is_dir());
            assert_eq!(
                data.description_metadata()[2].nlink(),
                0,
                "acquired info is genuinely unlinked"
            );
            assert_eq!(data.description_metadata()[3].nlink(), 1);
            assert!(data.original_record() == original.original.held.text.as_bytes());
            assert!(data.withheld_record() == original.held.text.as_bytes());
            assert!(data.original_record().len() <= 16 * 1024);
            assert!(data.withheld_record().len() <= 16 * 1024);
            for index in 0..4 {
                assert_ne!(offered[index].as_raw_fd(), descriptors[index].as_raw_fd());
                assert!(crate::trust_repo_lock::same_inode(
                    &data.description_metadata()[index],
                    Some(&descriptors[index].metadata()?)
                ));
                assert_eq!(
                    unsafe { libc::fcntl(offered[index].as_raw_fd(), libc::F_GETFL) },
                    flags[index]
                );
                assert_eq!(flags[index] & libc::O_ACCMODE, libc::O_RDONLY);
                assert_ne!(
                    unsafe { libc::fcntl(offered[index].as_raw_fd(), libc::F_GETFD) }
                        & libc::FD_CLOEXEC,
                    0
                );
                if index >= 2 {
                    assert_eq!(
                        unsafe { libc::lseek(offered[index].as_raw_fd(), 0, libc::SEEK_CUR) },
                        index as i64
                    );
                }
            }
            Ok(())
        })
        .unwrap();
    let failed: io::Result<()> = offer.with_descriptions(|_, _| {
        Err(io::Error::new(io::ErrorKind::Interrupted, "unchanged callback failure"))
    });
    assert_eq!(failed.unwrap_err().kind(), io::ErrorKind::Interrupted);
    offer.check_current().unwrap();
    drop(offer);
    for index in 0..4 {
        assert_eq!(
            unsafe { libc::fcntl(descriptors[index].as_raw_fd(), libc::F_GETFL) },
            flags[index]
        );
        assert_eq!(
            unsafe { libc::fcntl(descriptors[index].as_raw_fd(), libc::F_GETFD) },
            local[index]
        );
        if index >= 2 {
            assert_eq!(
                unsafe { libc::lseek(descriptors[index].as_raw_fd(), 0, libc::SEEK_CUR) },
                index as i64
            );
        }
    }
    source.check_current().unwrap();
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn writable_live_record_cannot_be_reopened_or_attenuated_by_an_offer() {
    if isolated_current() {
        return;
    }
    let (root, mut withheld) = original();
    // Reproduce the old live O_RDWR retention at the actual owner boundary.
    // Exact bytes/inode still validate; export must reject this access mode,
    // rather than manufacture a different readonly description at offer time.
    Arc::get_mut(&mut withheld).unwrap().held.file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(root.path().join(".trust-build-lock/info"))
        .unwrap();
    withheld.check_current().unwrap();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let error = match source.close_only_offer() {
        Err(error) => error,
        Ok(_) => panic!("writable original was exported"),
    };
    assert!(error.to_string().contains("readonly original"));
    source.check_current().unwrap();
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn offer_failed_callback_still_detects_changed_record_and_keeps_failure_sticky() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let foreign = tempfile::tempdir().unwrap();
    assert!(scope.original_source(foreign.path()).is_err());
    let offer = source.close_only_offer().unwrap();
    let info = root.path().join(".trust-build-lock/info");
    let bytes = fs::read(&info).unwrap();
    let result: io::Result<()> = offer.with_descriptions(|_, _| {
        fs::write(&info, b"changed actual publication\n")?;
        Err(io::Error::new(io::ErrorKind::Interrupted, "callback failure"))
    });
    assert!(result.is_err());
    assert_ne!(result.unwrap_err().kind(), io::ErrorKind::Interrupted);
    fs::write(&info, &bytes).unwrap();
    scope.inner.original.check_current().unwrap();
    assert!(offer.check_current().is_err());
    assert!(source.close_only_offer().is_err());
    println!("source-root-checked");
}

#[test]
fn offer_uses_original_deadline_including_after_a_failed_callback() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    // Far enough ahead that the scope, the source and the offer are made before
    // it on a loaded machine; the callback then sleeps past it.
    let scope = ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(5)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let offer = source.close_only_offer().unwrap();
    let result: io::Result<()> = offer.with_descriptions(|_, _| {
        std::thread::sleep(
            offer.deadline().saturating_duration_since(Instant::now()) + Duration::from_millis(2),
        );
        Err(io::Error::new(io::ErrorKind::Interrupted, "callback failure"))
    });
    assert_eq!(result.unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert!(source.close_only_offer().is_err());
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn offer_callback_unwind_permanently_withholds_the_original_scope() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let offer = source.close_only_offer().unwrap();
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _: io::Result<()> =
            offer.with_descriptions(|_, _| panic!("actual offer callback panic"));
    }));
    assert!(panic.is_err());
    // Native custody remains valid, but callback unwind permanently vetoes
    // dispatch/offer reuse even when an outer caller catches that same panic.
    scope.inner.original.check_current().unwrap();
    assert!(offer.check_current().is_err());
    assert!(source.close_only_offer().is_err());
    assert!(scope.dispatcher().register_launch().is_err());
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn retained_offer_does_not_hide_original_scope_owner_loss() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let offer = source.close_only_offer().unwrap();
    drop(source);
    offer.check_current().unwrap();
    drop(scope);
    assert!(offer.check_current().is_err());
    let mut called = false;
    assert!(
        offer
            .with_descriptions(|_, _| {
                called = true;
                Ok(())
            })
            .is_err()
    );
    assert!(!called);
    drop(offer);
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn forked_offer_cannot_mint_or_borrow_descriptions_from_the_original_creator() {
    if isolated_current() {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let offer = source.close_only_offer().unwrap();
    let child = unsafe { libc::fork() };
    assert!(child >= 0);
    if child == 0 {
        let mut called = false;
        let refused = source.close_only_offer().is_err()
            && offer
                .with_descriptions(|_, _| {
                    called = true;
                    Ok(())
                })
                .is_err()
            && !called;
        unsafe { libc::_exit(if refused { 0 } else { 91 }) };
    }
    let mut status = 0;
    loop {
        if unsafe { libc::waitpid(child, &mut status, 0) } == child {
            break;
        }
        assert_eq!(io::Error::last_os_error().kind(), io::ErrorKind::Interrupted);
    }
    assert!(libc::WIFEXITED(status));
    assert_eq!(libc::WEXITSTATUS(status), 0);
    offer.check_current().unwrap();
    println!("source-root-checked");
}

#[test]
fn source_borrows_the_same_original_directory_without_allocating_or_changing_flags() {
    if isolated(
        "trust_repo_lock::management::lease::withholding::protected_scope::input::tests::source_borrows_the_same_original_directory_without_allocating_or_changing_flags",
    ) {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let original = scope.inner.original.original.manager.root.file.as_raw_fd();
    let flags = unsafe { libc::fcntl(original, libc::F_GETFL) };
    let local = unsafe { libc::fcntl(original, libc::F_GETFD) };
    let source = scope.original_source(root.path()).unwrap();
    assert_eq!(source.identity(), scope.identity());
    assert_eq!(source.path(), root.path().canonicalize().unwrap());
    assert_eq!(source.directory().unwrap().as_raw_fd(), original);
    assert_eq!(unsafe { libc::fcntl(original, libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::fcntl(original, libc::F_GETFD) }, local);
    let foreign = tempfile::tempdir().unwrap();
    assert!(scope.original_source(foreign.path()).is_err());
    source.check_current().unwrap();
    // Sealing local dispatch cannot release custody or keep source work Open.
    let joined = scope.seal().join().unwrap();
    assert!(source.directory().is_err());
    drop((source, joined));
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    println!("source-root-checked");
}

#[test]
fn replaced_source_name_never_redirects_the_original_and_restore_does_not_clear_failure() {
    if isolated(
        "trust_repo_lock::management::lease::withholding::protected_scope::input::tests::replaced_source_name_never_redirects_the_original_and_restore_does_not_clear_failure",
    ) {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let original = source.directory().unwrap().as_raw_fd();
    let sibling = root.path().with_extension("retained-original");
    fs::rename(root.path(), &sibling).unwrap();
    fs::create_dir(root.path()).unwrap();
    assert!(source.directory().is_err());
    assert_eq!(scope.inner.original.original.manager.root.file.as_raw_fd(), original);
    fs::remove_dir(root.path()).unwrap();
    fs::rename(&sibling, root.path()).unwrap();
    assert!(source.check_current().is_err(), "an observed failure is permanent");
    assert!(scope.dispatcher().register_launch().is_err());
    println!("source-root-checked");
}

#[test]
fn drift_observed_while_binding_source_stays_failed_after_the_original_name_returns() {
    if isolated(
        "trust_repo_lock::management::lease::withholding::protected_scope::input::tests::drift_observed_while_binding_source_stays_failed_after_the_original_name_returns",
    ) {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let fd = source.directory().unwrap().as_raw_fd();
    // Exercise the actual selection phase after its first dispatcher bookend.
    scope.dispatcher().check_current().unwrap();
    let sibling = root.path().with_extension("binding-original");
    fs::rename(root.path(), &sibling).unwrap();
    fs::create_dir(root.path()).unwrap();
    assert!(scope.bind_original_source(root.path()).is_err());
    fs::remove_dir(root.path()).unwrap();
    fs::rename(&sibling, root.path()).unwrap();
    // Physical restoration itself is valid. The independently observed
    // failure must still veto work on the SAME original retained directory.
    scope.inner.original.original.manager.root.check_current().unwrap();
    assert_eq!(scope.inner.original.original.manager.root.file.as_raw_fd(), fd);
    assert!(source.directory().is_err());
    assert!(scope.dispatcher().register_launch().is_err());
    println!("source-root-checked");
}

#[test]
fn failed_selector_cannot_hide_actual_root_drift_at_the_final_binding_bookend() {
    if isolated(
        "trust_repo_lock::management::lease::withholding::protected_scope::input::tests::failed_selector_cannot_hide_actual_root_drift_at_the_final_binding_bookend",
    ) {
        return;
    }
    let (root, withheld) = original();
    let scope =
        ProtectedWorkScope::new(withheld, Instant::now() + Duration::from_secs(30)).unwrap();
    let source = scope.original_source(root.path()).unwrap();
    let sibling = root.path().with_extension("selection-original");
    scope.dispatcher().check_current().unwrap();
    // The native selection closure runs strictly between the two actual root
    // bookends. It observes a real missing-selector error during real drift.
    let error = scope
        .inner
        .original
        .original
        .manager
        .root
        .check_expected_during(|| {
            fs::rename(root.path(), &sibling).unwrap();
            fs::create_dir(root.path()).unwrap();
            fs::canonicalize(root.path().join("missing-selector"))
                .map(|_| ())
                .map_err(|error| error.to_string())
        })
        .expect_err("the actual changed root must refuse");
    assert!(matches!(error, crate::trust_repo_lock::ExpectedRootError::Current(_)));
    let _observed = scope.source_check_error(error);
    fs::remove_dir(root.path()).unwrap();
    fs::rename(&sibling, root.path()).unwrap();
    scope.inner.original.original.manager.root.check_current().unwrap();
    assert!(source.directory().is_err());
    assert!(scope.dispatcher().register_launch().is_err());
    println!("source-root-checked");
}
