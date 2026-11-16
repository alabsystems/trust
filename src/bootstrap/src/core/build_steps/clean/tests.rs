// Trust: this file is Trust-owned. It pins `x clean --all` on the Spotlight
// layout, where `build` is a symlink to a real `build.noindex`
// (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/").

use std::fs;

use super::*;

// Trust: re-exec a real independent process, so flock contention cannot be a
// same-process alias artifact. The actor is inert in an ordinary test run.
#[cfg(unix)]
#[test]
fn output_lock_probe_actor() {
    let Some(out) = std::env::var_os("TRUST_TEST_CLEAN_OUTPUT_LOCK") else { return };
    let out = Path::new(&out);
    fs::create_dir_all(out).unwrap();
    let file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(out.join("lock"))
        .unwrap();
    let code = match file.try_lock() {
        Ok(()) => 0,
        Err(std::fs::TryLockError::WouldBlock) => 73,
        Err(error) => panic!("output-lock probe failed: {error}"),
    };
    std::process::exit(code);
}

#[cfg(unix)]
fn output_lock_probe(out: &Path) -> std::process::ExitStatus {
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    let mut child =
        crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", "core::build_steps::clean::tests::output_lock_probe_actor"])
            .env("TRUST_TEST_CLEAN_OUTPUT_LOCK", out)
            .stdout(Stdio::null())
            .spawn()
            .unwrap();
    // This is only a watchdog. Passing depends on actual lock state and inode
    // identity, never on speed. This child remains ours and unreaped until wait.
    let end = Instant::now() + Duration::from_secs(15);
    loop {
        match child.try_wait().unwrap() {
            Some(status) => return status,
            None if Instant::now() < end => std::thread::sleep(Duration::from_millis(10)),
            None => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("owned output-lock probe exceeded its watchdog");
            }
        }
    }
}

#[cfg(unix)]
#[test]
fn clean_all_retains_locked_namespace_for_real_and_sanctioned_output_roots() {
    crate::utils::tests::isolated(|| {
        use std::os::unix::fs::{MetadataExt, symlink};
        for linked in [false, true] {
            let temp = tempfile::TempDir::new().unwrap();
            let out = temp.path().join("build");
            let physical = if linked { temp.path().join("build.noindex") } else { out.clone() };
            fs::create_dir_all(physical.join("host/stage2")).unwrap();
            fs::write(physical.join("host/stage2/artifact"), b"remove").unwrap();
            let outside = temp.path().join("outside");
            fs::create_dir(&outside).unwrap();
            fs::write(outside.join("keep"), b"outside the output tree").unwrap();
            symlink(&outside, physical.join("nested-link")).unwrap();
            if linked {
                symlink("build.noindex", &out).unwrap();
            }
            let held = fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(false)
                .open(out.join("lock"))
                .unwrap();
            held.try_lock().unwrap();
            let root = physical.metadata().unwrap();
            let lock = held.metadata().unwrap();

            rm_rf_build_dir(&out);

            assert_eq!(
                output_lock_probe(&out).code(),
                Some(73),
                "a new inode admitted a contender"
            );
            let current_root = physical.metadata().unwrap();
            let current_lock = out.join("lock").symlink_metadata().unwrap();
            assert_eq!((root.dev(), root.ino()), (current_root.dev(), current_root.ino()));
            assert_eq!((lock.dev(), lock.ino()), (current_lock.dev(), current_lock.ino()));
            let entries: Vec<_> =
                fs::read_dir(&physical).unwrap().map(|entry| entry.unwrap().file_name()).collect();
            assert_eq!(entries, ["lock"]);
            assert_eq!(fs::read(outside.join("keep")).unwrap(), b"outside the output tree");
            if linked {
                assert_eq!(fs::read_link(&out).unwrap(), Path::new("build.noindex"));
            }
            drop(held);
            assert_eq!(
                output_lock_probe(&out).code(),
                Some(0),
                "closed owner still excludes a successor"
            );
        }
    });
}

#[cfg(unix)]
#[test]
fn default_and_stage_cleanup_remove_nested_links_without_deleting_their_targets() {
    use std::os::unix::fs::{MetadataExt, symlink};

    use crate::utils::tests::TestCtx;

    for stage in [None, Some(0)] {
        let context = TestCtx::new();
        let mut session = Session::new(context.config("clean").create_config());
        let out = context.dir().join("fixture-output");
        session.config.out = out.clone();
        let host = out.join(session.host_target);
        fs::create_dir_all(host.join("stage1/bin")).unwrap();
        fs::write(host.join("stage1/bin/trustc"), b"artifact").unwrap();
        fs::create_dir_all(host.join("llvm")).unwrap();
        fs::write(host.join("llvm/keep"), b"cached LLVM").unwrap();
        let outside = context.dir().join("outside");
        fs::create_dir(&outside).unwrap();
        fs::write(outside.join("keep"), b"not an output artifact").unwrap();
        symlink(&out, host.join("stage1-ancestor")).unwrap();
        symlink(&outside, host.join("stage1-external")).unwrap();
        // An unrelated replacement of the convenience alias cannot turn it
        // into permission to clean a different tree.
        symlink(&outside, out.join("host")).unwrap();
        let held = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(out.join("lock"))
            .unwrap();
        held.try_lock().unwrap();
        let root = out.metadata().unwrap();
        let lock = held.metadata().unwrap();

        if let Some(stage) = stage {
            clean_specific_stage(&session, stage);
        } else {
            clean_default(&session);
        }

        assert!(!host.join("stage1").exists());
        assert!(host.join("stage1-ancestor").symlink_metadata().is_err());
        assert!(host.join("stage1-external").symlink_metadata().is_err());
        assert_eq!(fs::read(outside.join("keep")).unwrap(), b"not an output artifact");
        assert_eq!(fs::read(host.join("llvm/keep")).unwrap(), b"cached LLVM");
        let current_root = out.metadata().unwrap();
        let current_lock = out.join("lock").metadata().unwrap();
        assert_eq!((root.dev(), root.ino()), (current_root.dev(), current_root.ino()));
        assert_eq!((lock.dev(), lock.ino()), (current_lock.dev(), current_lock.ino()));
        assert_eq!(output_lock_probe(&out).code(), Some(73));
    }
}

#[cfg(unix)]
#[test]
fn malformed_cleanup_hosts_refuse_before_touching_any_output() {
    use crate::core::config::TargetSelection;
    use crate::utils::cache::INTERNER;
    use crate::utils::tests::TestCtx;

    for stage in [None, Some(0)] {
        for name in ["", ".", "..", "../fixture-output", "fixture-output/..", "nested/host", "/"] {
            let context = TestCtx::new();
            let mut session = Session::new(context.config("clean").create_config());
            let out = context.dir().join("fixture-output");
            fs::create_dir_all(out.join("tmp")).unwrap();
            fs::write(out.join("tmp/keep"), b"untouched temporary artifact").unwrap();
            let host = out.join(session.host_target);
            fs::create_dir_all(host.join("stage1")).unwrap();
            fs::write(host.join("stage1/keep"), b"untouched stage artifact").unwrap();
            session.config.out = out.clone();
            // Keep a valid host first: no earlier host may be cleaned before a
            // later malformed selection is discovered. Construct raw triples
            // for existing paths too (from_user reduces target files to stems).
            let malformed =
                TargetSelection { triple: INTERNER.intern_str(name), file: None, synthetic: false };
            if name == "../fixture-output" {
                assert_eq!(TargetSelection::from_user(name), malformed);
            }
            session.config.hosts = vec![session.host_target, malformed];
            let held =
                build_helper::trust_output_lock::OutputLock::try_acquire(&out).unwrap().unwrap();

            let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                if let Some(stage) = stage {
                    clean_specific_stage(&session, stage);
                } else {
                    clean_default(&session);
                }
            }));
            assert!(refused.is_err(), "malformed host {name:?} was admitted");
            held.check_current().unwrap();
            assert_eq!(output_lock_probe(&out).code(), Some(73));
            assert_eq!(fs::read(out.join("tmp/keep")).unwrap(), b"untouched temporary artifact");
            assert_eq!(fs::read(host.join("stage1/keep")).unwrap(), b"untouched stage artifact");

            if stage.is_none() {
                // The implicit build host is deletion authority as well.
                session.config.hosts.truncate(1);
                session.config.host_target = malformed;
                assert!(
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        clean_default(&session);
                    }))
                    .is_err()
                );
                held.check_current().unwrap();
                assert_eq!(
                    fs::read(out.join("tmp/keep")).unwrap(),
                    b"untouched temporary artifact"
                );
                assert_eq!(
                    fs::read(host.join("stage1/keep")).unwrap(),
                    b"untouched stage artifact"
                );
            }
        }
    }
}

#[cfg(unix)]
#[test]
fn default_and_stage_cleanup_do_not_traverse_linked_host_roots() {
    use std::os::unix::fs::symlink;

    use crate::utils::tests::TestCtx;

    for stage in [None, Some(0)] {
        for ancestor in [false, true] {
            let context = TestCtx::new();
            let mut session = Session::new(context.config("clean").create_config());
            let out = context.dir().join("fixture-output");
            fs::create_dir(&out).unwrap();
            session.config.out = out.clone();
            let outside = context.dir().join("outside");
            fs::create_dir_all(outside.join("stage1")).unwrap();
            fs::write(outside.join("stage1/keep"), b"shared artifact").unwrap();
            let host = out.join(session.host_target);
            symlink(if ancestor { &out } else { &outside }, &host).unwrap();
            fs::write(out.join("lock"), b"coordination").unwrap();

            if let Some(stage) = stage {
                clean_specific_stage(&session, stage);
            } else {
                clean_default(&session);
            }

            assert!(host.symlink_metadata().is_err());
            assert_eq!(fs::read(out.join("lock")).unwrap(), b"coordination");
            assert_eq!(fs::read(outside.join("stage1/keep")).unwrap(), b"shared artifact");
        }
    }
}

#[cfg(unix)]
#[test]
fn clean_all_empties_the_directory_a_symlinked_build_names_and_keeps_the_link() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::TempDir::new().unwrap();
    let physical = temp.path().join("build.noindex");
    let stage2 = physical.join("host/stage2/bin");
    fs::create_dir_all(&stage2).unwrap();
    fs::write(stage2.join("trustc"), b"artifact").unwrap();
    fs::write(physical.join("config.toml"), b"artifact").unwrap();
    // A link INSIDE the build directory is removed, never entered.
    let outside = temp.path().join("outside");
    fs::create_dir(&outside).unwrap();
    fs::write(outside.join("keep"), b"not a build artifact").unwrap();
    symlink(&outside, physical.join("linked-elsewhere")).unwrap();
    let build = temp.path().join("build");
    symlink("build.noindex", &build).unwrap();

    rm_rf_build_dir(&build);

    assert!(build.symlink_metadata().unwrap().file_type().is_symlink(), "the link is kept");
    assert_eq!(fs::read_link(&build).unwrap(), Path::new("build.noindex"));
    assert!(physical.is_dir(), "the linked directory itself is kept");
    assert_eq!(fs::read_dir(&physical).unwrap().count(), 0, "every artifact is removed");
    assert_eq!(fs::read(outside.join("keep")).unwrap(), b"not a build artifact");
}

#[test]
fn clean_all_empties_a_real_build_directory_but_preserves_its_root() {
    let temp = tempfile::TempDir::new().unwrap();
    let build = temp.path().join("build");
    fs::create_dir_all(build.join("host/stage2/bin")).unwrap();
    fs::write(build.join("host/stage2/bin/trustc"), b"artifact").unwrap();

    rm_rf_build_dir(&build);

    assert!(build.is_dir(), "the coordination root survives artifact cleanup");
    assert_eq!(fs::read_dir(&build).unwrap().count(), 0);
}

#[cfg(unix)]
#[test]
fn clean_all_removes_a_dangling_build_link() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::TempDir::new().unwrap();
    let build = temp.path().join("build");
    symlink("build.noindex", &build).unwrap();

    rm_rf_build_dir(&build);

    assert!(build.symlink_metadata().is_err());
}

/// Only the sanctioned link is emptied through. A `build` link to any other
/// directory (a shared build tree, another volume), or to a `build.noindex` that
/// is itself a link, keeps upstream behavior: the link goes, the target stays.
#[cfg(unix)]
#[test]
fn clean_all_never_deletes_through_an_unsanctioned_build_link() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::TempDir::new().unwrap();
    let shared = temp.path().join("shared-build");
    fs::create_dir_all(shared.join("host/stage2/bin")).unwrap();
    fs::write(shared.join("host/stage2/bin/trustc"), b"someone else's artifact").unwrap();
    let checkout = temp.path().join("checkout");
    fs::create_dir(&checkout).unwrap();
    let build = checkout.join("build");

    // `build` -> a directory that is not the sibling `build.noindex`.
    symlink(&shared, &build).unwrap();
    rm_rf_build_dir(&build);
    assert!(build.symlink_metadata().is_err(), "the link itself is removed");
    assert!(shared.join("host/stage2/bin/trustc").is_file(), "nothing behind it is deleted");

    // `build` -> `build.noindex`, but `build.noindex` is itself a link.
    symlink(&shared, checkout.join("build.noindex")).unwrap();
    symlink("build.noindex", &build).unwrap();
    rm_rf_build_dir(&build);
    assert!(build.symlink_metadata().is_err(), "the link itself is removed");
    assert!(shared.join("host/stage2/bin/trustc").is_file(), "nothing behind it is deleted");
}
