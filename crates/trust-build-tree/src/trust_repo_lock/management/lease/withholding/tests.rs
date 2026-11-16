use std::fs;
use std::io::{BufRead, Write};
use std::process::{Command, Stdio};
use std::time::Duration;

use super::*;
use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager, Release};

fn request(token: Option<String>) -> Acquire {
    Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "durable withholding native control".into(),
        contract: "original exclusion only; Host closure unavailable".into(),
        wait: Duration::ZERO,
        inherited_token: token,
        break_reason: None,
    }
}

fn grant(root: &std::path::Path, token: Option<String>) -> Lease {
    match Manager::open(root).unwrap().acquire_lease(&request(token)).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("owned native fixture unexpectedly busy"),
    }
}

#[test]
fn owned_transition_pins_same_originals_and_drop_never_releases() {
    use std::os::unix::fs::MetadataExt;
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let token = lease.token.clone();
    let original_directory = lease.held.identity.ino();
    let original_info = lease.held.metadata.ino();
    let original_bytes = lease.held.text.clone();
    let withheld = lease.into_withheld().unwrap();
    for file in [&withheld.original.held.file, &withheld.held.file] {
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        assert!(flags >= 0);
        assert_eq!(flags & libc::O_ACCMODE, libc::O_RDONLY);
    }
    assert_eq!(withheld.original.held.file.metadata().unwrap().nlink(), 0);
    assert_eq!(withheld.held.file.metadata().unwrap().nlink(), 1);
    assert_eq!(withheld.original.held.identity.ino(), original_directory);
    assert_eq!(withheld.held.identity.ino(), original_directory);
    assert_eq!(withheld.original.held.metadata.ino(), original_info);
    assert_ne!(withheld.held.metadata.ino(), original_info);
    assert_eq!(withheld.original.held.text, original_bytes);
    withheld.check_current().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    assert!(manager.status().unwrap().holder.unwrap().is_withheld());
    assert_eq!(manager.release(&token).unwrap(), Release::ParentManaged);
    assert!(manager.break_holder("a sentence is not Host closure").is_err());
    let mut forced = request(None);
    forced.break_reason = Some("a sentence cannot grant work".into());
    assert!(matches!(manager.acquire(&forced).unwrap(), super::super::super::Acquisition::Busy(_)));
    drop(withheld);
    assert!(!manager.status().unwrap().is_free());
    assert_eq!(manager.release(&token).unwrap(), Release::ParentManaged);
}

#[test]
fn staged_record_publishes_the_same_checked_readonly_description() {
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let staged = StagedRecord::new(&lease.held.directory, "bounded staged bytes\n").unwrap();
    let original_fd = staged.file().as_raw_fd();
    let original_metadata = staged.file().metadata().unwrap();
    assert_eq!(
        unsafe { libc::fcntl(original_fd, libc::F_GETFL) } & libc::O_ACCMODE,
        libc::O_RDONLY
    );
    let published = staged.publish().unwrap();
    assert_eq!(published.as_raw_fd(), original_fd);
    assert!(same_inode(&original_metadata, Some(&published.metadata().unwrap())));
    let mut bytes = [0; 21];
    published.read_exact_at(&mut bytes, 0).unwrap();
    assert_eq!(&bytes, b"bounded staged bytes\n");
    assert_eq!(unsafe { libc::write(published.as_raw_fd(), b"x".as_ptr().cast(), 1) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EBADF));
    assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
}

#[test]
fn original_withheld_publication_preserves_repository_config_parent_origin() {
    let name = std::thread::current().name().unwrap().to_owned();
    crate::trust_output_lock::tests::isolated_case(&name, || {
        use std::os::unix::fs::MetadataExt as _;
        fn origin(meta: &fs::Metadata) -> (u64, u64, u32, u32, u32, u64, u64, i64, i64, i64, i64) {
            (
                meta.dev(),
                meta.ino(),
                meta.mode(),
                meta.uid(),
                meta.gid(),
                meta.nlink(),
                meta.len(),
                meta.mtime(),
                meta.mtime_nsec(),
                meta.ctime(),
                meta.ctime_nsec(),
            )
        }
        let root = tempfile::tempdir().unwrap();
        let lease = grant(root.path(), None);
        let config = root.path().join("bootstrap.toml");
        fs::write(&config, b"[build]\nbuild-dir='build'\n").unwrap();
        let config_file = fs::File::open(&config).unwrap();
        let config_before = origin(&config_file.metadata().unwrap());
        let info_before = lease.held.metadata.ino();
        let holder_before = lease.held.identity.ino();
        let before = origin(&fs::metadata(root.path()).unwrap());
        let held = lease.into_withheld().unwrap();
        held.check_current().unwrap();
        let after = origin(&fs::metadata(root.path()).unwrap());
        eprintln!("ACTUAL-WITHHELD-ROOT-ORIGINS before={before:?} after={after:?}");
        assert_eq!(held.original.held.metadata.ino(), info_before);
        assert_eq!(held.held.identity.ino(), holder_before);
        assert_ne!(held.held.metadata.ino(), info_before);
        assert!(held.held.parse().unwrap().is_withheld());
        assert_eq!(origin(&config_file.metadata().unwrap()), config_before);
        assert_eq!(origin(&fs::metadata(&config).unwrap()), config_before);
        assert_eq!(fs::read(&config).unwrap(), b"[build]\nbuild-dir='build'\n");
        // No expected origin refresh: the actual original parent must remain
        // stable while only its already-held holder directory is published.
        assert_eq!(after, before, "owned info replacement changed the retained config parent");
        eprintln!("ACTUAL-WITHHELD-ROOT-ORIGINS-ASSERTIONS-COMPLETE");
    });
}

#[test]
fn staged_record_collision_never_overwrites_an_existing_entry() {
    let name = std::thread::current().name().unwrap().to_owned();
    crate::trust_output_lock::tests::isolated_case(&name, || {
        let root = tempfile::tempdir().unwrap();
        let lease = grant(root.path(), None);
        let path = root.path().join(".trust-build-lock/existing-stage");
        fs::write(&path, b"existing foreign bytes").unwrap();
        let error = StagedRecord::create(
            &lease.held.directory,
            CString::new("existing-stage").unwrap(),
            "new record",
        )
        .err()
        .unwrap();
        assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(fs::read(&path).unwrap(), b"existing foreign bytes");
        lease.check_current().unwrap();
        fs::remove_file(path).unwrap();
    });
}

#[test]
fn replaced_stage_name_refuses_publication_and_drop_preserves_foreign_entries() {
    let name = std::thread::current().name().unwrap().to_owned();
    crate::trust_output_lock::tests::isolated_case(&name, || {
        use std::os::unix::ffi::OsStrExt as _;
        for link in [false, true] {
            let root = tempfile::tempdir().unwrap();
            let lease = grant(root.path(), None);
            let holder = root.path().join(".trust-build-lock");
            let original_info = fs::read(holder.join("info")).unwrap();
            let staged =
                StagedRecord::new(&lease.held.directory, "original staged record").unwrap();
            let path = holder.join(std::ffi::OsStr::from_bytes(staged.name.as_bytes()));
            let moved = holder.join("original-stage");
            fs::rename(&path, &moved).unwrap();
            let target = root.path().join("foreign-target");
            if link {
                fs::write(&target, b"foreign target bytes").unwrap();
                std::os::unix::fs::symlink(&target, &path).unwrap();
            } else {
                fs::write(&path, b"foreign replacement bytes").unwrap();
            }
            assert!(staged.publish().is_err());
            assert_eq!(fs::read(&moved).unwrap(), b"original staged record");
            if link {
                assert!(fs::symlink_metadata(&path).unwrap().file_type().is_symlink());
                assert_eq!(fs::read(&target).unwrap(), b"foreign target bytes");
            } else {
                assert_eq!(fs::read(&path).unwrap(), b"foreign replacement bytes");
            }
            assert_eq!(fs::read(holder.join("info")).unwrap(), original_info);
            lease.check_current().unwrap();
            fs::remove_file(path).unwrap();
            fs::remove_file(moved).unwrap();
        }
    });
}

#[test]
fn actual_borrowed_child_cannot_promote_or_release_original() {
    const NAME: &str = "trust_repo_lock::management::lease::withholding::tests::actual_borrowed_child_cannot_promote_or_release_original";
    const ROOT: &str = "TRUST_WITHHOLD_BORROW_ROOT";
    if let Some(root) = std::env::var_os(ROOT) {
        let lease = grant(
            std::path::Path::new(&root),
            Some(std::env::var("TRUST_WITHHOLD_BORROW_TOKEN").unwrap()),
        );
        assert!(lease.is_borrowed());
        let failed = lease.into_withheld().unwrap_err();
        assert_eq!(failed.publication(), WithholdPublication::NotAttempted);
        failed.check_original_current().unwrap();
        let lease = failed.try_recover_unpublished().unwrap();
        assert!(lease.is_borrowed());
        drop(lease);
        return;
    }
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let before = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
    let status = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", NAME, "--nocapture"])
        .env(ROOT, root.path())
        .env("TRUST_WITHHOLD_BORROW_TOKEN", &lease.token)
        .status()
        .unwrap();
    assert!(status.success());
    assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), before);
    lease.check_current().unwrap();
    drop(lease);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn replacement_and_mutation_refuse_conversion_without_releasing_inputs() {
    for replace in [false, true] {
        let root = tempfile::tempdir().unwrap();
        let lease = grant(root.path(), None);
        let directory = root.path().join(".trust-build-lock");
        let mut expected = fs::read(directory.join("info")).unwrap();
        if replace {
            fs::rename(&directory, root.path().join("original-holder")).unwrap();
            fs::create_dir(&directory).unwrap();
        } else {
            expected.extend_from_slice(b"unknown_future=retained\n");
        }
        fs::write(directory.join("info"), &expected).unwrap();
        let failed = lease.into_withheld().unwrap_err();
        assert_eq!(failed.publication(), WithholdPublication::NotAttempted);
        assert!(failed.try_recover_unpublished().is_err());
        assert_eq!(fs::read(directory.join("info")).unwrap(), expected);
    }
}

#[test]
fn forked_original_cannot_publish_or_release() {
    crate::trust_output_lock::tests::isolated_case(
        "trust_repo_lock::management::lease::withholding::tests::forked_original_cannot_publish_or_release",
        || {
            let root = tempfile::tempdir().unwrap();
            let lease = grant(root.path(), None);
            let before = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
            // Isolated native ownership check; the child fails before namespace IO.
            let child = unsafe { libc::fork() };
            assert!(child >= 0);
            if child == 0 {
                let result = lease.into_withheld();
                let code = match result {
                    Err(failed) if failed.publication() == WithholdPublication::NotAttempted => 0,
                    _ => 91,
                };
                unsafe { libc::_exit(code) };
            }
            let mut status = 0;
            loop {
                let waited = unsafe { libc::waitpid(child, &mut status, 0) };
                if waited == child {
                    break;
                }
                assert_eq!(std::io::Error::last_os_error().kind(), std::io::ErrorKind::Interrupted);
            }
            assert!(libc::WIFEXITED(status));
            assert_eq!(libc::WEXITSTATUS(status), 0);
            assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), before);
            lease.check_current().unwrap();
        },
    );
}

#[test]
fn post_replace_failure_and_unwind_never_restore_ordinary_release() {
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let token = lease.token.clone();
    FAIL_AFTER_REPLACE.with(|fault| fault.set(true));
    let failed = lease.into_withheld().unwrap_err();
    FAIL_AFTER_REPLACE.with(|fault| fault.set(false));
    assert_eq!(failed.publication(), WithholdPublication::Attempted);
    assert!(failed.error().to_string().contains("after actual info replacement"));
    assert!(failed.check_original_current().is_err());
    failed.check_current().unwrap();
    let failed = match failed.try_recover_unpublished() {
        Err(failed) => failed,
        Ok(_) => panic!("attempted publication recovered ordinary release"),
    };
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _retained = failed;
        panic!("native failed owner unwind control");
    }));
    let manager = Manager::open(root.path()).unwrap();
    assert!(manager.status().unwrap().holder.unwrap().is_withheld());
    assert_eq!(manager.release(&token).unwrap(), Release::ParentManaged);
    assert!(manager.break_holder("unknown publication is not quiet closure").is_err());
}

#[test]
fn unpublished_failure_retains_original_until_explicit_checked_recovery() {
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let original = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
    FAIL_BEFORE_REPLACE.with(|fault| fault.set(true));
    let failed = lease.into_withheld().unwrap_err();
    FAIL_BEFORE_REPLACE.with(|fault| fault.set(false));
    assert_eq!(failed.publication(), WithholdPublication::NotAttempted);
    failed.check_original_current().unwrap();
    assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), original);
    let lease = failed.try_recover_unpublished().unwrap();
    lease.check_current().unwrap();
    assert!(!lease.is_borrowed());
    drop(lease);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn withheld_rechecks_exact_record_inode_root_and_version() {
    for mode in ["bytes", "inode", "root", "future"] {
        let parent = tempfile::tempdir().unwrap();
        let root = parent.path().join("root");
        fs::create_dir(&root).unwrap();
        let withheld = grant(&root, None).into_withheld().unwrap();
        let info = root.join(".trust-build-lock/info");
        let original = fs::read(&info).unwrap();
        match mode {
            "bytes" => {
                fs::write(&info, [original.as_slice(), b"unknown=changed\n"].concat()).unwrap()
            }
            "inode" => {
                fs::rename(&info, root.join("retained-info")).unwrap();
                fs::write(&info, &original).unwrap();
            }
            "root" => {
                fs::rename(&root, parent.path().join("original-root")).unwrap();
                fs::create_dir(&root).unwrap();
            }
            _ => fs::write(
                &info,
                String::from_utf8(original)
                    .unwrap()
                    .replace("withheld_version=1", "withheld_version=2"),
            )
            .unwrap(),
        }
        assert!(withheld.check_current().is_err(), "{mode}");
        drop(withheld);
        if mode != "root" {
            assert!(info.exists(), "{mode} was released");
        }
    }
}

#[test]
fn actual_owner_death_and_lost_host_transport_leave_native_withheld() {
    const NAME: &str = "trust_repo_lock::management::lease::withholding::tests::actual_owner_death_and_lost_host_transport_leave_native_withheld";
    const ROOT: &str = "TRUST_WITHHOLD_DEATH_ROOT";
    if let Some(root) = std::env::var_os(ROOT) {
        let withheld = grant(std::path::Path::new(&root), None).into_withheld().unwrap();
        withheld.check_current().unwrap();
        println!("ACTUAL-WITHHELD-READY");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();
        // Simulate original owner death without destructors after actual
        // host-transport EOF. Neither observation authorizes release.
        std::process::exit(7);
    }
    let root = tempfile::tempdir().unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", NAME, "--nocapture"])
        .env(ROOT, root.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut reader = std::io::BufReader::new(child.stdout.take().unwrap());
    loop {
        let mut line = String::new();
        assert_ne!(reader.read_line(&mut line).unwrap(), 0);
        if line.contains("ACTUAL-WITHHELD-READY") {
            break;
        }
    }
    drop(child.stdin.take());
    assert_eq!(child.wait().unwrap().code(), Some(7));
    let manager = Manager::open(root.path()).unwrap();
    let holder = manager.status().unwrap().holder.unwrap();
    assert_eq!(holder.liveness, crate::trust_repo_lock::management::Liveness::Gone);
    assert!(matches!(
        manager.acquire(&request(None)).unwrap(),
        super::super::super::Acquisition::Busy(_)
    ));
    assert_eq!(manager.release(&holder.token).unwrap(), Release::ParentManaged);
    assert!(manager.break_holder("dead Host and owner are not original closure").is_err());
    {
        let original = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
        let own_pid = std::process::id().to_string();
        for args in [
            vec!["acquire", "--kind", "build", "--pid", &own_pid],
            vec!["release", &holder.token],
            vec!["break", "--reason", "a reason is not closure"],
            vec![
                "acquire",
                "--kind",
                "build",
                "--pid",
                &own_pid,
                "--break",
                "--reason",
                "a reason is not closure",
            ],
        ] {
            let output = crate::trust_repo_lock::tests::namespace::command(root.path(), &args)
                .output()
                .unwrap();
            assert!(!output.status.success(), "native CLI released: {output:?}");
            let diagnostic = String::from_utf8_lossy(&output.stderr).to_ascii_lowercase();
            assert!(
                diagnostic.contains("withheld")
                    || (args[0] == "release"
                        && output.status.code() == Some(4)
                        && diagnostic.contains("parent-managed")),
                "wrong native refusal: {output:?}"
            );
            assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), original);
        }
        let unknown = String::from_utf8(original)
            .unwrap()
            .replace("withheld_version=1", "withheld_version=2");
        fs::write(root.path().join(".trust-build-lock/info"), &unknown).unwrap();
        assert!(manager.acquire(&request(None)).is_err());
        assert!(manager.release(&holder.token).is_err());
        assert!(manager.break_holder("future state cannot be recovered from text").is_err());
        let output = crate::trust_repo_lock::tests::namespace::command(
            root.path(),
            &["break", "--reason", "future is not closure"],
        )
        .output()
        .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).to_ascii_lowercase().contains("withheld"));
        assert_eq!(
            fs::read_to_string(root.path().join(".trust-build-lock/info")).unwrap(),
            unknown
        );
    }
}

#[test]
fn native_cli_read_failure_cannot_erase_actual_withheld_exclusion() {
    use std::os::unix::fs::PermissionsExt;
    assert_ne!(
        unsafe { libc::geteuid() },
        0,
        "this actual unreadable fixture requires a non-root owner"
    );
    const ACTOR: &str = "trust_repo_lock::management::lease::withholding::tests::actual_owner_death_and_lost_host_transport_leave_native_withheld";
    let own_pid = std::process::id().to_string();
    for damage in ["unreadable", "malformed", "missing"] {
        for operation in ["release", "break", "acquire", "acquire-break"] {
            let root = tempfile::tempdir().unwrap();
            let actor = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", ACTOR, "--nocapture"])
                .env("TRUST_WITHHOLD_DEATH_ROOT", root.path())
                .stdin(Stdio::null())
                .output()
                .unwrap();
            assert_eq!(actor.status.code(), Some(7), "{actor:?}");
            let manager = Manager::open(root.path()).unwrap();
            let token = manager.status().unwrap().holder.unwrap().token;
            let holder = root.path().join(".trust-build-lock");
            let info = holder.join("info");
            let bytes = fs::read(&info).unwrap();
            match damage {
                "unreadable" => {
                    fs::set_permissions(&info, fs::Permissions::from_mode(0o0)).unwrap()
                }
                "malformed" => fs::write(&info, b"unknown incomplete holder\n").unwrap(),
                _ => {
                    fs::remove_file(&info).unwrap();
                    fs::write(holder.join("unknown"), b"retain unknown original contents").unwrap();
                }
            }
            let args = match operation {
                "release" => vec!["release", &token],
                "break" => vec!["break", "--reason", "unreadable does not mean closed"],
                "acquire" => vec!["acquire", "--kind", "build", "--pid", &own_pid],
                _ => vec![
                    "acquire",
                    "--kind",
                    "build",
                    "--pid",
                    &own_pid,
                    "--break",
                    "--reason",
                    "unknown is not closure",
                ],
            };
            let observed = crate::trust_repo_lock::tests::namespace::command(root.path(), &args)
                .output()
                .unwrap();
            eprintln!(
                "actual native CLI {damage}/{operation}: {:?}; {}",
                observed.status,
                String::from_utf8_lossy(&observed.stderr)
            );
            assert!(
                !observed.status.success(),
                "{damage}/{operation} granted recovery: {observed:?}"
            );
            assert!(holder.is_dir(), "{damage}/{operation} erased actual original holder");
            let acquisition = matches!(operation, "acquire" | "acquire-break");
            let expected = if damage == "missing" && acquisition { 3 } else { 2 };
            assert_eq!(
                observed.status.code(),
                Some(expected),
                "{damage}/{operation}: {observed:?}"
            );
            let diagnostic = String::from_utf8_lossy(&observed.stderr);
            let expected_diagnostic = match damage {
                "unreadable" => "Permission denied",
                "malformed" => "malformed holder field",
                _ if acquisition => "incomplete holder retained",
                _ if operation == "release" => "holder metadata is missing",
                _ => "unknown contents",
            };
            assert!(diagnostic.contains(expected_diagnostic), "unrelated refusal: {observed:?}");
            match damage {
                "unreadable" => {
                    fs::set_permissions(&info, fs::Permissions::from_mode(0o600)).unwrap();
                    assert_eq!(fs::read(&info).unwrap(), bytes);
                }
                "malformed" => assert_eq!(fs::read(&info).unwrap(), b"unknown incomplete holder\n"),
                _ => assert_eq!(
                    fs::read(holder.join("unknown")).unwrap(),
                    b"retain unknown original contents"
                ),
            }
        }
    }
}

#[test]
fn native_cli_matching_token_cannot_borrow_incomplete_or_future_withheld() {
    for future in [false, true] {
        let root = tempfile::tempdir().unwrap();
        let withheld = grant(root.path(), None).into_withheld().unwrap();
        let manager = Manager::open(root.path()).unwrap();
        let token = manager.status().unwrap().holder.unwrap().token;
        let info = root.path().join(".trust-build-lock/info");
        let mut incomplete =
            fs::read_to_string(&info).unwrap().replace("release_parent_pid=\n", "");
        if future {
            incomplete = incomplete.replace("withheld_version=1", "withheld_version=2");
        }
        fs::write(&info, &incomplete).unwrap();
        assert!(withheld.check_current().is_err());
        assert!(manager.acquire(&request(Some(token.clone()))).is_err());
        let observed = crate::trust_repo_lock::tests::namespace::command(
            root.path(),
            &["acquire", "--kind", "build", "--pid", &std::process::id().to_string()],
        )
        .env("TRUST_BUILD_LOCK_TOKEN", token)
        .env_remove("TRUST_BUILD_LOCK_BREAK")
        .env_remove("TRUST_BUILD_LOCK_WAIT")
        .output()
        .unwrap();
        if observed.status.success() {
            let retained = root.keep();
            panic!(
                "actual incomplete WITHHELD false borrow; future={future}; original failed inputs retained at {}; raw={observed:?}",
                retained.display()
            );
        }
        assert!(
            String::from_utf8_lossy(&observed.stderr).to_ascii_lowercase().contains("withheld"),
            "wrong refusal: {observed:?}"
        );
        assert_eq!(fs::read_to_string(&info).unwrap(), incomplete);
    }
}
