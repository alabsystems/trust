// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io::Read as _;
use std::os::unix::fs::symlink;
use std::time::Duration;

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
fn fixture() -> (tempfile::TempDir, File, PathBuf) {
    let scratch = tempfile::tempdir().unwrap();
    let target = scratch.path().join("lib/rustlib").join(TARGET);
    std::fs::create_dir_all(target.join("lib/self-contained")).unwrap();
    std::fs::create_dir_all(target.join("bin")).unwrap();
    std::fs::write(target.join("lib/original.rlib"), b"held original bytes").unwrap();
    std::fs::write(target.join("lib/empty.rmeta"), b"").unwrap();
    let root = File::open(scratch.path()).unwrap();
    (scratch, root, target)
}
fn capture(root: &File, path: &Path) -> Namespace {
    Namespace::capture(root, path, deadline(), MAX_DESCRIPTORS, |_| {}).unwrap()
}

#[test]
fn expired_consumer_does_not_poison_unchanged_target_but_observed_drift_stays_terminal() {
    let (scratch, root, target) = fixture();
    let held = Arc::new(capture(&root, scratch.path()));
    let next = held.clone();
    assert_eq!(held.validate(&root, Instant::now()).unwrap_err().kind(), io::ErrorKind::TimedOut);
    next.validate(&root, deadline()).unwrap();

    let added = target.join("lib/changed-after-expired-consumer.rmeta");
    std::fs::write(&added, b"new actual namespace member").unwrap();
    assert!(next.validate(&root, deadline()).is_err());
    std::fs::remove_file(added).unwrap();
    assert!(held.validate(&root, deadline()).is_err());
}

#[test]
fn complete_target_retains_original_bytes_empty_directories_and_negative_names() {
    let (scratch, root, target) = fixture();
    let held = Arc::new(capture(&root, scratch.path()));
    let second_unit = Arc::clone(&held);
    assert!(Arc::ptr_eq(&held, &second_unit));
    assert_eq!(held.files.len(), 2);
    assert!(
        held.directories
            .contains_key(&PathBuf::from("lib/rustlib").join(TARGET).join("lib/self-contained"))
    );
    let file = &held.files[&PathBuf::from("lib/rustlib").join(TARGET).join("lib/original.rlib")];
    let mut actual = [0; 19];
    assert_eq!(file.file.read_at(&mut actual, 0).unwrap(), actual.len());
    assert_eq!(&actual, b"held original bytes");
    held.validate(&root, deadline()).unwrap();
    std::fs::create_dir(target.join("codegen-backends")).unwrap();
    assert!(second_unit.validate(&root, deadline()).is_err());
    std::fs::remove_dir(target.join("codegen-backends")).unwrap();
    assert!(
        held.validate(&root, deadline()).is_err(),
        "absence cannot be repaired into success after an observed failure"
    );
}

#[test]
fn live_target_read_scope_excludes_sdk_siblings_and_cannot_outlive_failed_originals() {
    let (scratch, root, target) = fixture();
    let sibling = scratch.path().join("unowned-sdk-sibling");
    std::fs::write(&sibling, b"outside the selected target namespace").unwrap();
    let held = Arc::new(capture(&root, scratch.path()));
    let second = held.clone();
    let selected = held.selected_directory(&root, deadline()).unwrap();
    assert_eq!(selected, target);
    assert_ne!(selected, scratch.path());
    assert!(!sibling.starts_with(&selected));
    assert!(target.join("lib/original.rlib").starts_with(&selected));
    // This owner does not retain/hash sibling contents. A recursive SDK-root
    // read grant would incorrectly authorize those unrelated bytes.
    std::fs::write(&sibling, b"still outside this original scope").unwrap();
    assert_eq!(second.selected_directory(&root, deadline()).unwrap(), selected);
    std::fs::write(target.join("lib/late.rmeta"), b"new selected member").unwrap();
    assert!(second.selected_directory(&root, deadline()).is_err());
    std::fs::remove_file(target.join("lib/late.rmeta")).unwrap();
    assert!(held.selected_directory(&root, deadline()).is_err(), "failed namespace is terminal");
}

#[test]
fn original_target_refuses_content_replacement_and_parent_aba() {
    for change in 0..3 {
        let (scratch, root, target) = fixture();
        let held = capture(&root, scratch.path());
        let original = target.join("lib/original.rlib");
        match change {
            0 => {
                std::fs::write(&original, b"same length altered").unwrap();
            }
            1 => {
                std::fs::rename(&original, original.with_extension("old")).unwrap();
                std::fs::write(&original, b"held original bytes").unwrap();
            }
            _ => {
                std::fs::rename(target.join("lib"), target.join("away")).unwrap();
                std::fs::rename(target.join("away"), target.join("lib")).unwrap();
            }
        }
        assert!(held.validate(&root, deadline()).is_err(), "actual input mutation {change}");
    }
}

#[test]
fn target_capture_refuses_symlinks_special_files_and_membership_races() {
    let (scratch, root, target) = fixture();
    symlink("original.rlib", target.join("lib/alias")).unwrap();
    assert!(
        Namespace::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |_| {}).is_err()
    );
    std::fs::remove_file(target.join("lib/alias")).unwrap();
    let fifo = CString::new(target.join("lib/pipe").as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    assert!(
        Namespace::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |_| {}).is_err()
    );
    std::fs::remove_file(target.join("lib/pipe")).unwrap();
    let relative = PathBuf::from("lib/rustlib").join(TARGET).join("lib");
    let result = Namespace::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |path| {
        if path == relative {
            std::fs::write(target.join("lib/late.rmeta"), b"late input").unwrap();
        }
    });
    assert!(
        result.is_err(),
        "an actual entry added after listing cannot disappear from complete coverage"
    );
}

#[test]
fn target_directory_component_symlink_and_timeout_cannot_gain_custody() {
    let (scratch, root, target) = fixture();
    std::fs::rename(&target, target.with_extension("original")).unwrap();
    symlink(target.with_extension("original"), &target).unwrap();
    assert!(
        Namespace::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |_| {}).is_err()
    );
    std::fs::remove_file(&target).unwrap();
    std::fs::rename(target.with_extension("original"), &target).unwrap();
    let held = capture(&root, scratch.path());
    assert!(held.validate(&root, Instant::now()).is_err());
    held.validate(&root, deadline()).unwrap();
    std::fs::rename(&target, target.with_extension("original")).unwrap();
    symlink(target.with_extension("original"), &target).unwrap();
    assert!(held.validate(&root, deadline()).is_err());
    std::fs::remove_file(&target).unwrap();
    std::fs::rename(target.with_extension("original"), &target).unwrap();
    assert!(
        held.validate(&root, deadline()).is_err(),
        "observed namespace substitution remains terminal after restoration"
    );
}

#[test]
fn compiler_selection_refuses_real_argfile_and_foreign_sysroot_target_backend_environment() {
    let scratch = tempfile::tempdir().unwrap();
    let argfile = scratch.path().join("args");
    std::fs::write(&argfile, b"--sysroot /unowned").unwrap();
    let root = scratch.path();
    let original = vec![
        b"--sysroot".to_vec(),
        root.as_os_str().as_bytes().to_vec(),
        b"--target=aarch64-apple-darwin".to_vec(),
    ];
    assert!(selection(root, &original, &[]).unwrap());
    let mut from_file = original.clone();
    from_file.push([b"@".as_slice(), argfile.as_os_str().as_bytes()].concat());
    assert!(selection(root, &from_file, &[]).is_err());
    let mut hidden_file = original.clone();
    hidden_file
        .extend([b"-Z".to_vec(), [b"@".as_slice(), argfile.as_os_str().as_bytes()].concat()]);
    assert!(selection(root, &hidden_file, &[]).is_err(), "expansion happens before option parsing");
    let mut other = original.clone();
    other.extend([b"--sysroot".to_vec(), b"/unowned".to_vec()]);
    assert!(selection(root, &other, &[]).is_err());
    assert!(selection(root, &[b"--target=foreign.json".to_vec()], &[]).is_err());
    assert!(
        selection(root, &[b"-Z".to_vec(), b"codegen_backend=/unowned.dylib".to_vec()], &[])
            .is_err()
    );
    assert!(
        selection(
            root,
            &original,
            &[(b"RUST_TARGET_PATH".to_vec(), scratch.path().as_os_str().as_bytes().to_vec())]
        )
        .is_err()
    );
}

#[test]
fn codegen_aliases_cannot_select_unowned_backend_plugins_or_llvm_arguments() {
    let root = Path::new("/original-sdk");
    let original =
        vec![b"--sysroot=/original-sdk".to_vec(), b"--target=aarch64-apple-darwin".to_vec()];
    for key in [
        "codegen-backend",
        "llvm-plugins",
        "llvm-args",
        "codegen_backend",
        "llvm_plugins",
        "llvm_args",
    ] {
        let value = format!("{key}=/unowned").into_bytes();
        for options in [
            vec![[b"-C".as_slice(), value.as_slice()].concat()],
            vec![b"-C".to_vec(), value.clone()],
            vec![[b"--codegen=".as_slice(), value.as_slice()].concat()],
            vec![b"--codegen".to_vec(), value.clone()],
            vec![[b"-Z".as_slice(), value.as_slice()].concat()],
            vec![b"-Z".to_vec(), value.clone()],
        ] {
            let mut args = original.clone();
            args.extend(options);
            assert!(selection(root, &args, &[]).is_err(), "unowned selection accepted: {args:?}");
        }
    }
    for options in [
        vec![b"--codegen".to_vec()],
        vec![b"--codegen=".to_vec()],
        vec![b"--codegen".to_vec(), Vec::new()],
    ] {
        let mut args = original.clone();
        args.extend(options);
        assert!(
            selection(root, &args, &[]).is_err(),
            "incomplete codegen option accepted: {args:?}"
        );
    }
    for options in [
        vec![b"--codegen=opt-level=1".to_vec()],
        vec![b"--codegen".to_vec(), b"opt-level=1".to_vec()],
    ] {
        let mut args = original.clone();
        args.extend(options);
        assert!(selection(root, &args, &[]).unwrap());
    }
}

struct Actor {
    child: std::process::Child,
    readers: Vec<std::thread::JoinHandle<io::Result<Vec<u8>>>>,
}
impl Drop for Actor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        for reader in self.readers.drain(..) {
            let _ = reader.join();
        }
    }
}
fn read_actor(
    mut stream: impl io::Read + Send + 'static,
) -> std::thread::JoinHandle<io::Result<Vec<u8>>> {
    std::thread::spawn(move || {
        let mut output = Vec::new();
        io::Read::take(&mut stream, 1024 * 1024 + 1).read_to_end(&mut output)?;
        Ok(output)
    })
}

#[test]
fn nofile_256_refuses_complete_507_file_target_instead_of_truncating_it() {
    const ACTOR: &str = "TRUST_TARGET_SYSROOT_NOFILE_ACTOR";
    if std::env::var_os(ACTOR).is_none() {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "program::target_sysroot::tests::nofile_256_refuses_complete_507_file_target_instead_of_truncating_it", "--nocapture"])
            .env(ACTOR, "1").stdin(std::process::Stdio::null()).stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped()).spawn().unwrap();
        let readers = vec![
            read_actor(child.stdout.take().unwrap()),
            read_actor(child.stderr.take().unwrap()),
        ];
        let mut actor = Actor { child, readers };
        let expires = deadline();
        let status = loop {
            if let Some(status) = actor.child.try_wait().unwrap() {
                break status;
            }
            assert!(
                Instant::now() < expires,
                "NOFILE actor hang detector expired; owning Drop kills/reaps and joins readers"
            );
            // Polling is only a hang detector; elapsed time establishes none
            // of the namespace/capacity postconditions checked by the actor.
            std::thread::sleep(Duration::from_millis(5));
        };
        let stdout = actor.readers.remove(0).join().unwrap().unwrap();
        let stderr = actor.readers.remove(0).join().unwrap().unwrap();
        assert!(stdout.len() <= 1024 * 1024 && stderr.len() <= 1024 * 1024);
        let stdout = String::from_utf8(stdout).unwrap();
        let stderr = String::from_utf8(stderr).unwrap();
        assert!(status.success(), "stdout={stdout} stderr={stderr}");
        assert!(
            stdout.contains("running 1 test") && stdout.contains("1 passed; 0 failed"),
            "wrong actor test selection: {stdout}"
        );
        assert_eq!(
            stderr.matches("TARGET_SYSROOT_NOFILE_ASSERTIONS_PASSED").count(),
            1,
            "actor assertions did not complete: {stderr}"
        );
        return;
    }
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) }, 0);
    let mut limit = unsafe { limit.assume_init() };
    assert!(
        limit.rlim_cur >= 256,
        "COULD NOT RUN exact NOFILE256 actor: inherited soft limit is below256; test never raises it"
    );
    limit.rlim_cur = 256;
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
    let (scratch, root, target) = fixture();
    for index in 0..505 {
        std::fs::write(target.join("lib").join(format!("original-{index}.rmeta")), b"").unwrap();
    }
    let error = Namespace::capture(&root, scratch.path(), deadline(), budget().unwrap(), |_| {})
        .err()
        .unwrap();
    assert!(error.to_string().contains("descriptor capacity unavailable"), "{error}");
    eprintln!("TARGET_SYSROOT_NOFILE_ASSERTIONS_PASSED");
}

#[test]
fn live_plan_refuses_between_phase_mutation_and_cannot_renew_a_failed_bookend() {
    let (scratch, root, target) = fixture();
    let plan =
        NamespacePlan::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |_| {}).unwrap();
    assert_eq!(plan.planned.len(), 2);
    std::fs::write(target.join("lib/original.rlib"), b"same length altered").unwrap();
    assert!(plan.validate(&root, deadline()).is_err());
    assert!(plan.materialize(&root, deadline(), MAX_DESCRIPTORS).is_err());
    let plan =
        NamespacePlan::capture(&root, scratch.path(), deadline(), MAX_DESCRIPTORS, |_| {}).unwrap();
    assert!(plan.validate(&root, Instant::now()).is_err());
    assert!(
        plan.validate(&root, deadline()).is_err(),
        "later success cannot clear unknown/late plan validation"
    );
    assert!(plan.materialize(&root, deadline(), MAX_DESCRIPTORS).is_err());
}
