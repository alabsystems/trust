use super::BuildLease;

#[test]
fn native_holder_excludes_peers_and_publishes_existing_protocol() {
    let root = tempfile::tempdir().unwrap();
    let lease = BuildLease::acquire(root.path()).unwrap();
    let info = std::fs::read_to_string(root.path().join(".trust-build-lock/info")).unwrap();
    let pid = std::process::id().to_string();
    assert!(info.contains(&format!("pid={pid}\n")));
    assert!(info.contains("kind=build\n"));
    // Trust: EW18-LOCKUTC-1. Both start fields: the zoned `pstart` for readers that
    // predate the zone-free one, and `pstart_utc`, which reads the same in every
    // time zone and locale.
    assert!(info.contains(&format!("\npstart={}\n", super::ps("lstart=", &pid).unwrap())));
    assert!(info.contains(&format!("\npstart_utc={}\n", zoned_start(&pid, "UTC0", Some("C")))));
    assert!(BuildLease::acquire(root.path()).is_err());
    drop(lease);
    assert!(!root.path().join(".trust-build-lock").exists());
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn holder_is_never_group_writable_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "trust_repo_lock::tests::holder_is_never_group_writable_under_a_group_writable_umask",
        || {
            use std::os::unix::fs::PermissionsExt as _;
            let root = tempfile::tempdir().unwrap();
            let lease = BuildLease::acquire(root.path()).unwrap();
            let holder = std::fs::symlink_metadata(root.path().join(".trust-build-lock")).unwrap();
            assert_eq!(holder.permissions().mode() & 0o777, 0o755);
            // The native manager's status refuses a group-writable holder directory.
            let manager = super::management::Manager::open(root.path()).unwrap();
            assert_eq!(manager.status().unwrap().holder.unwrap().pid, std::process::id());
            drop(lease);
            assert!(!root.path().join(".trust-build-lock").exists());
        },
    );
}

#[test]
fn existing_and_legacy_holders_are_never_removed() {
    let root = tempfile::tempdir().unwrap();
    let lock = root.path().join(".trust-build-lock");
    std::fs::create_dir(&lock).unwrap();
    std::fs::write(lock.join("info"), "peer holder").unwrap();
    assert!(BuildLease::acquire(root.path()).is_err());
    assert_eq!(std::fs::read_to_string(lock.join("info")).unwrap(), "peer holder");
    std::fs::remove_file(lock.join("info")).unwrap();
    std::fs::remove_dir(lock).unwrap();
    std::fs::write(root.path().join(".trust-measurement-in-flight"), "peer").unwrap();
    assert!(BuildLease::acquire(root.path()).is_err());
    assert!(root.path().join(".trust-measurement-in-flight").exists());
}

#[test]
fn validated_parent_handoff_retains_holder_until_outer_release() {
    const ROOT: &str = "TRUST_NATIVE_REPO_HANDOFF_CONTROL_ROOT";
    const MODE: &str = "TRUST_NATIVE_REPO_HANDOFF_CONTROL_MODE";
    const NAME: &str =
        "trust_repo_lock::tests::validated_parent_handoff_retains_holder_until_outer_release";
    if let Some(root) = std::env::var_os(ROOT) {
        let root = std::path::Path::new(&root);
        let held = BuildLease::acquire_for_parent(root);
        if matches!(std::env::var(MODE).unwrap().as_str(), "valid" | "valid-across-zones") {
            drop(held.unwrap());
            assert!(root.join(".trust-build-lock/info").is_file());
        } else {
            assert!(held.is_err());
            assert!(!root.join(".trust-build-lock").exists());
        }
        println!("native parent handoff control executed");
        return;
    }

    let parent = std::process::id().to_string();
    let start = super::ps("lstart=", &parent).unwrap();
    // Trust: EW18-LOCKUTC-1. The parent's start as a parent in Los Angeles reads
    // it, and as it reads in no zone at all.
    let start_la = zoned_start(&parent, "America/Los_Angeles", None);
    let start_utc = zoned_start(&parent, "UTC0", Some("C"));
    let mut records = Vec::new();
    for mode in [
        "valid",
        "valid-across-zones",
        "wrong-parent",
        "wrong-start",
        "wrong-start-utc",
        "empty-start-utc",
        "wrong-token",
        "empty-token",
        "partial",
        "absent",
    ] {
        let root = tempfile::tempdir().unwrap();
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env(ROOT, root.path())
            .env(MODE, mode)
            .env("TRUST_NATIVE_REPO_PARENT_PID", &parent)
            .env("TRUST_NATIVE_REPO_PARENT_START", &start)
            .env("TRUST_NATIVE_REPO_PARENT_TOKEN", "trust-native-repo-owner-control")
            .env_remove("TRUST_NATIVE_REPO_PARENT_START_UTC")
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        match mode {
            // Trust: EW18-LOCKUTC-1. A parent in Los Angeles hands off to a child
            // in Tokyo with a French locale. The zoned start differs between them
            // (asserted below), so only the zone-free start identifies the parent.
            "valid-across-zones" => {
                command
                    .env("TRUST_NATIVE_REPO_PARENT_START", &start_la)
                    .env("TRUST_NATIVE_REPO_PARENT_START_UTC", &start_utc)
                    .env("TZ", "Asia/Tokyo")
                    .env("LC_ALL", "fr_FR.UTF-8");
            }
            // When the zone-free start is present it is the one judged: a wrong one
            // is refused even though the zoned start matches, and so is an empty
            // one, which identifies nothing (fail-closed, not the zoned fallback).
            "wrong-start-utc" => {
                command.env("TRUST_NATIVE_REPO_PARENT_START_UTC", "previous parent process");
            }
            "empty-start-utc" => {
                command.env("TRUST_NATIVE_REPO_PARENT_START_UTC", "");
            }
            "wrong-parent" => {
                command.env("TRUST_NATIVE_REPO_PARENT_PID", "1");
            }
            "wrong-start" => {
                command.env("TRUST_NATIVE_REPO_PARENT_START", "previous parent process");
            }
            "wrong-token" => {
                command.env("TRUST_NATIVE_REPO_PARENT_TOKEN", "inherited-boolean");
            }
            "empty-token" => {
                command.env("TRUST_NATIVE_REPO_PARENT_TOKEN", "trust-native-repo-owner-");
            }
            "partial" => {
                command.env_remove("TRUST_NATIVE_REPO_PARENT_TOKEN");
            }
            "absent" => {
                command
                    .env_remove("TRUST_NATIVE_REPO_PARENT_PID")
                    .env_remove("TRUST_NATIVE_REPO_PARENT_START")
                    .env_remove("TRUST_NATIVE_REPO_PARENT_TOKEN");
            }
            _ => {}
        }
        let mut child = command.spawn().unwrap();
        let pid = child.id();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            match child.try_wait() {
                Ok(Some(_)) => {
                    let output = child.wait_with_output().unwrap();
                    assert!(output.status.success(), "{mode}: {output:?}");
                    assert!(
                        String::from_utf8_lossy(&output.stdout)
                            .contains("native parent handoff control executed"),
                        "zero executed controls cannot pass: {mode}: {output:?}"
                    );
                    break;
                }
                Ok(None) if std::time::Instant::now() < deadline => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                state => {
                    let killed = child.kill();
                    let output = child.wait_with_output().unwrap();
                    panic!(
                        "handoff control did not complete: {mode}: {state:?}; kill={killed:?}; {output:?}"
                    );
                }
            }
        }
        if mode == "valid" || mode == "valid-across-zones" {
            let info = std::fs::read_to_string(root.path().join(".trust-build-lock/info")).unwrap();
            assert!(info.contains(&format!("pid={pid}\n")));
            assert!(info.contains(&format!("release_parent_pid={parent}\n")));
            // The zoned start the parent sent is carried verbatim: the parent
            // compares it with its own copy of the same string.
            let sent = if mode == "valid" { &start } else { &start_la };
            assert!(info.contains(&format!("release_parent_start={sent}\n")));
            assert!(info.contains("release_token=trust-native-repo-owner-control\n"));
            records.push((mode, info));
        }
    }
    // The cross-zone mode is no control unless the zoned starts really differ.
    assert_ne!(start_la, zoned_start(&parent, "Asia/Tokyo", Some("fr_FR.UTF-8")));
    // Each accepted child recorded its own zone-free start beside the zoned one.
    for (mode, info) in records {
        assert!(
            info.lines()
                .any(|line| line.strip_prefix("pstart_utc=").is_some_and(|v| !v.is_empty())),
            "{mode}: {info}"
        );
    }
}

// Trust: EW18-LOCKUTC-1. `ps -o lstart=` for `pid` as a caller in `zone` (and,
// when given, `locale`) reads it.
fn zoned_start(pid: &str, zone: &str, locale: Option<&str>) -> String {
    let mut command = std::process::Command::new("ps");
    command.args(["-o", "lstart=", "-p", pid]).env("TZ", zone).env_remove("LC_ALL");
    if let Some(locale) = locale {
        command.env("LC_ALL", locale);
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

#[cfg(unix)]
pub(crate) mod namespace;

#[cfg(unix)]
const INDEPENDENT_ROOT: &str = "TRUST_SHARED_BUILD_LEASE_CONTROL_ROOT";
#[cfg(unix)]
const INDEPENDENT_MODE: &str = "TRUST_SHARED_BUILD_LEASE_CONTROL_MODE";

/// Trust: keep the actual test child until positive reap, including on failure.
#[cfg(unix)]
struct OwnedActor(Option<std::process::Child>);

#[cfg(unix)]
impl OwnedActor {
    fn spawn(command: &mut std::process::Command) -> Self {
        Self(Some(
            command
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap(),
        ))
    }

    fn finish(mut self) -> std::process::Output {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        loop {
            if self.0.as_mut().unwrap().try_wait().unwrap().is_some() {
                return self.0.take().unwrap().wait_with_output().unwrap();
            }
            assert!(std::time::Instant::now() < deadline, "shared build-lease actor hung");
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}

#[cfg(unix)]
impl Drop for OwnedActor {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

#[cfg(unix)]
fn actor_command(name: &str, root: &std::path::Path, mode: &str) -> std::process::Command {
    let mut command = std::process::Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", name, "--nocapture", "--test-threads=1"])
        .env(INDEPENDENT_ROOT, root)
        .env(INDEPENDENT_MODE, mode)
        .env_remove("TRUST_NATIVE_REPO_PARENT_PID")
        .env_remove("TRUST_NATIVE_REPO_PARENT_START")
        .env_remove("TRUST_NATIVE_REPO_PARENT_START_UTC")
        .env_remove("TRUST_NATIVE_REPO_PARENT_TOKEN");
    command
}

#[cfg(unix)]
#[test]
fn check_current_rejects_changed_holder_bytes_and_replaced_file_directory_or_root() {
    const NAME: &str = "trust_repo_lock::tests::check_current_rejects_changed_holder_bytes_and_replaced_file_directory_or_root";
    if let Some(root) = std::env::var_os(INDEPENDENT_ROOT) {
        use std::fs;
        let root = std::path::PathBuf::from(root);
        let mode = std::env::var(INDEPENDENT_MODE).unwrap();
        let lease = BuildLease::acquire_independent(&root, "guard identity control", "native test")
            .unwrap();
        lease.check_current().unwrap();
        let directory = root.join(".trust-build-lock");
        let info = directory.join("info");
        let original = fs::read(&info).unwrap();
        let expected = match mode.as_str() {
            "unchanged" => {
                lease.check_current().unwrap();
                drop(lease);
                assert!(!directory.exists());
                println!("shared build-lease identity control executed: {mode}");
                return;
            }
            "bytes" => {
                let mut replacement = original.clone();
                let purpose = b"purpose=";
                let value =
                    replacement.windows(purpose.len()).position(|part| part == purpose).unwrap()
                        + purpose.len();
                assert_eq!(replacement[value], b'g');
                replacement[value] = b'G';
                assert_eq!(replacement.len(), original.len(), "exercise exact bytes, not length");
                fs::write(&info, &replacement).unwrap();
                replacement
            }
            // Each replacement has the original's mode: the info 0600, as the
            // persisted temporary file, and the holder as `create_holder_directory`
            // makes it. `same_inode` compares modes too, so only (dev, ino) differs
            // and the refusal is about identity under any umask. The root is made
            // as the parent made the original, under the same inherited umask.
            "file" => {
                fs::rename(&info, root.join("preserved-original-info")).unwrap();
                crate::owner_only::write(&info, &original);
                original.clone()
            }
            "directory" => {
                fs::rename(&directory, root.join("preserved-original-holder")).unwrap();
                super::create_holder_directory(&directory).unwrap();
                crate::owner_only::write(&info, &original);
                original.clone()
            }
            "root" => {
                let old = root.with_file_name("preserved-original-root");
                fs::rename(&root, &old).unwrap();
                fs::create_dir(&root).unwrap();
                super::create_holder_directory(&directory).unwrap();
                crate::owner_only::write(&info, &original);
                assert_eq!(fs::read(old.join(".trust-build-lock/info")).unwrap(), original);
                original.clone()
            }
            _ => panic!("unknown identity control {mode}"),
        };
        assert!(lease.check_current().is_err(), "accepted changed {mode}");
        // A failed observation still owns the original lease. Dropping it may
        // not release any replacement, including a byte-identical new inode.
        assert_eq!(fs::read(&info).unwrap(), expected);
        drop(lease);
        assert_eq!(fs::read(&info).unwrap(), expected, "released changed {mode}");
        println!("shared build-lease identity control executed: {mode}");
        return;
    }
    for mode in ["unchanged", "bytes", "file", "directory", "root"] {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("tree");
        std::fs::create_dir(&root).unwrap();
        let output = OwnedActor::spawn(&mut actor_command(NAME, &root, mode)).finish();
        assert!(output.status.success(), "{mode}: {output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains(&format!("shared build-lease identity control executed: {mode}")),
            "zero executed identity controls cannot pass: {mode}: {output:?}"
        );
    }
}

// The identity control's actors inherit the umask of the process that runs it,
// so this runs it, and a plain acquisition and release, in a process whose
// umask is 002, where a std-created directory is group writable.
#[cfg(unix)]
#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "trust_repo_lock::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            native_holder_excludes_peers_and_publishes_existing_protocol();
            check_current_rejects_changed_holder_bytes_and_replaced_file_directory_or_root();
        },
    );
}

#[cfg(unix)]
#[test]
fn independent_acquisition_never_adopts_an_inherited_parent_release_handoff() {
    const NAME: &str = "trust_repo_lock::tests::independent_acquisition_never_adopts_an_inherited_parent_release_handoff";
    if let Some(root) = std::env::var_os(INDEPENDENT_ROOT) {
        let root = std::path::PathBuf::from(root);
        let mode = std::env::var(INDEPENDENT_MODE).unwrap();
        if mode == "valid" {
            super::require_parent_handoff().expect("the actual parent's tuple is valid");
        } else {
            assert!(super::require_parent_handoff().is_err(), "{mode}");
        }
        let lease =
            BuildLease::acquire_independent(&root, "independent consumer", "native control")
                .expect("independent acquisition does not interpret inherited handoff settings");
        lease.check_current().unwrap();
        let info = std::fs::read_to_string(root.join(".trust-build-lock/info")).unwrap();
        assert!(info.contains(&format!("pid={}\n", std::process::id())));
        assert!(info.contains("purpose=independent consumer\n"));
        assert!(info.contains("cmd=native control\n"));
        assert!(!info.contains("release_parent_"));
        assert!(!info.contains("release_token="));
        assert!(BuildLease::acquire_independent(&root, "another consumer", "native peer").is_err());
        drop(lease);
        assert!(!root.join(".trust-build-lock").exists(), "independent Drop owns release");
        println!("shared independent build-lease control executed: {mode}");
        return;
    }
    let parent = std::process::id().to_string();
    let start = super::ps("lstart=", &parent).unwrap();
    let start_utc = zoned_start(&parent, "UTC0", Some("C"));
    for mode in ["valid", "wrong-parent", "wrong-start-utc", "empty-token", "partial"] {
        let root = tempfile::tempdir().unwrap();
        let mut command = actor_command(NAME, root.path(), mode);
        command
            .env("TRUST_NATIVE_REPO_PARENT_PID", &parent)
            .env("TRUST_NATIVE_REPO_PARENT_START", &start)
            .env("TRUST_NATIVE_REPO_PARENT_START_UTC", &start_utc)
            .env("TRUST_NATIVE_REPO_PARENT_TOKEN", "trust-native-repo-owner-control");
        match mode {
            "wrong-parent" => {
                command.env("TRUST_NATIVE_REPO_PARENT_PID", "1");
            }
            "wrong-start-utc" => {
                command.env("TRUST_NATIVE_REPO_PARENT_START_UTC", "previous parent");
            }
            "empty-token" => {
                command.env("TRUST_NATIVE_REPO_PARENT_TOKEN", "");
            }
            "partial" => {
                command.env_remove("TRUST_NATIVE_REPO_PARENT_TOKEN");
            }
            _ => {}
        }
        let output = OwnedActor::spawn(&mut command).finish();
        assert!(output.status.success(), "{mode}: {output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains(&format!("shared independent build-lease control executed: {mode}")),
            "zero executed independent controls cannot pass: {mode}: {output:?}"
        );
    }
}

#[cfg(unix)]
#[test]
fn control_characters_in_either_record_argument_refuse_before_claiming() {
    use std::fs;
    use std::os::unix::fs::MetadataExt;

    for control in ['\n', '\r', '\0', '\u{1b}', '\t', '\u{85}', '\u{2028}', '\u{2029}'] {
        let invalid = format!("before{control}after");
        for invalid_purpose in [true, false] {
            let root = tempfile::tempdir().unwrap();
            let (purpose, invocation) = if invalid_purpose {
                (invalid.as_str(), "native control")
            } else {
                ("independent consumer", invalid.as_str())
            };
            let refused = BuildLease::acquire_independent(root.path(), purpose, invocation);
            assert!(refused.is_err(), "accepted {control:?}, purpose={invalid_purpose}");
            let directory = root.path().join(".trust-build-lock");
            assert!(!directory.exists(), "invalid record must not claim the holder");
            assert!(
                fs::read_dir(root.path()).unwrap().next().is_none(),
                "validate before namespace I/O"
            );

            fs::create_dir(&directory).unwrap();
            let info = directory.join("info");
            let peer = b"persistent peer holder must remain unchanged\n";
            fs::write(&info, peer).unwrap();
            let before_directory = fs::symlink_metadata(&directory).unwrap();
            let before_info = fs::symlink_metadata(&info).unwrap();
            assert!(BuildLease::acquire_independent(root.path(), purpose, invocation).is_err());
            assert_eq!(fs::read(&info).unwrap(), peer);
            let after_directory = fs::symlink_metadata(&directory).unwrap();
            let after_info = fs::symlink_metadata(&info).unwrap();
            assert_eq!(
                (before_directory.dev(), before_directory.ino()),
                (after_directory.dev(), after_directory.ino()),
            );
            assert_eq!(
                (before_info.dev(), before_info.ino()),
                (after_info.dev(), after_info.ino())
            );
            assert!(!root.path().join(crate::trust_build_lock::GUARD_NAME).exists());
        }
    }
    // Ordinary Unicode text remains usable; the rejected set is record controls.
    let root = tempfile::tempdir().unwrap();
    let lease =
        BuildLease::acquire_independent(root.path(), "compilation café", "native Δ").unwrap();
    lease.check_current().unwrap();
    let info = fs::read_to_string(root.path().join(".trust-build-lock/info")).unwrap();
    assert!(info.contains("purpose=compilation café\n"));
    assert!(info.contains("cmd=native Δ\n"));
    drop(lease);
    assert!(!root.path().join(".trust-build-lock").exists());
}

#[cfg(unix)]
#[test]
fn a_simulated_foreign_owner_copy_cannot_validate_or_release_the_original_holder() {
    use std::fs;
    use std::os::unix::fs::MetadataExt;

    let root = tempfile::tempdir().unwrap();
    let mut lease =
        BuildLease::acquire_independent(root.path(), "owner control", "native test").unwrap();
    lease.check_current().unwrap();
    let directory = root.path().join(".trust-build-lock");
    let info = directory.join("info");
    let bytes = fs::read(&info).unwrap();
    let before = fs::symlink_metadata(&info).unwrap();
    // Model only the owner-identity mismatch of a foreign process copy. No
    // actual fork is attempted from this multithreaded Rust test process.
    lease.owner = lease.owner.wrapping_add(1);
    assert_ne!(lease.owner, std::process::id());
    assert!(lease.check_current().is_err());
    assert_eq!(fs::read(&info).unwrap(), bytes);
    drop(lease);
    assert_eq!(fs::read(&info).unwrap(), bytes);
    let after = fs::symlink_metadata(&info).unwrap();
    assert_eq!((before.dev(), before.ino()), (after.dev(), after.ino()));
    assert!(directory.is_dir());
}

// Trust: EW-9 (22). The purpose the stage-1 seed's donor lease records.
#[cfg(unix)]
const SEED_SOURCE: &str = "stage-1 seed source (another worktree clones this build tree)";

/// Trust: EW-9 (22). Every entry under `root`, with its identity and bytes: a judgement
/// must leave all of them as they were.
#[cfg(unix)]
fn snapshot(root: &std::path::Path) -> Vec<(std::path::PathBuf, u64, u64, Option<Vec<u8>>)> {
    use std::os::unix::fs::MetadataExt;
    let mut entries = Vec::new();
    let mut pending = vec![root.to_owned()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            let metadata = std::fs::symlink_metadata(&path).unwrap();
            let bytes = metadata.is_file().then(|| std::fs::read(&path).unwrap());
            if metadata.is_dir() {
                pending.push(path.clone());
            }
            entries.push((path, metadata.dev(), metadata.ino(), bytes));
        }
    }
    entries.sort();
    entries
}

/// Trust: EW-9 (22). A real seed holder, killed while it holds the lease (as a seed
/// killed mid-clone is), leaves its lease; it is judged gone, and the judgement neither
/// reclaims, removes nor changes anything. While it lived it was not gone, and a record
/// with another purpose is never judged.
#[cfg(unix)]
#[test]
fn a_killed_seed_holder_is_judged_gone_and_its_lease_is_left_as_it_was() {
    use std::io::BufRead;
    const NAME: &str = "trust_repo_lock::tests::a_killed_seed_holder_is_judged_gone_and_its_lease_is_left_as_it_was";
    if let Some(root) = std::env::var_os(INDEPENDENT_ROOT) {
        assert_eq!(std::env::var(INDEPENDENT_MODE).unwrap(), "hold");
        let _lease = BuildLease::acquire_independent(
            std::path::Path::new(&root),
            SEED_SOURCE,
            "bootstrap stage-1 seed",
        )
        .unwrap();
        println!("seed holder control holds the lease");
        // Held until the parent kills this process, so no destructor releases it.
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("tree");
    std::fs::create_dir(&root).unwrap();
    let mut actor = OwnedActor::spawn(&mut actor_command(NAME, &root, "hold"));
    let child = actor.0.as_mut().unwrap();
    let pid = child.id();
    let mut lines = std::io::BufReader::new(child.stdout.take().unwrap()).lines();
    assert!(
        lines.any(|line| line.unwrap().contains("seed holder control holds the lease")),
        "zero executed seed holder controls cannot pass"
    );
    let info = std::fs::read_to_string(root.join(".trust-build-lock/info")).unwrap();
    assert!(info.contains(&format!("\npid={pid}\n")), "{info}");
    let before = snapshot(&root);
    assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), None, "a live holder");
    child.kill().unwrap();
    child.wait().unwrap();
    assert!(root.join(".trust-build-lock/info").is_file(), "a killed holder leaves its lease");
    assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), Some(pid));
    assert_eq!(super::gone_independent_holder(&root, "native compiler check"), None);
    assert_eq!(snapshot(&root), before, "a judgement changes nothing");
    assert!(BuildLease::acquire_independent(&root, SEED_SOURCE, "peer").is_err());
    assert_eq!(snapshot(&root), before, "and nothing here takes the lease over");
}

/// Trust: EW-9 (22). A process that has exited and been reaped: its pid, and its start
/// time read as the holder writer reads it (zoned and zone-free).
#[cfg(unix)]
fn reaped_process() -> (u32, String, String) {
    let mut child = std::process::Command::new("/bin/cat")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let pid = child.id().to_string();
    let starts = (super::ps("lstart=", &pid), super::ps_utc("lstart=", &pid));
    drop(child.stdin.take());
    assert!(child.wait().unwrap().success());
    (child.id(), starts.0.unwrap(), starts.1.unwrap())
}

/// Trust: EW-9 (22). The writer's own record for a seed holder, with `pid`, `pstart` and
/// `pstart_utc` replaced. The writer took and released the lease; nothing holds `root`.
#[cfg(unix)]
fn seed_record(root: &std::path::Path, pid: u32, start: &str, start_utc: &str) -> String {
    let lease =
        BuildLease::acquire_independent(root, SEED_SOURCE, "bootstrap stage-1 seed").unwrap();
    let info = std::fs::read_to_string(root.join(".trust-build-lock/info")).unwrap();
    drop(lease);
    assert!(!root.join(".trust-build-lock").exists());
    let replaced =
        [("pid", pid.to_string()), ("pstart", start.into()), ("pstart_utc", start_utc.into())];
    let mut record = String::new();
    for line in info.lines() {
        let key = line.split_once('=').unwrap().0;
        match replaced.iter().find(|(name, _)| *name == key) {
            Some((name, value)) => record.push_str(&format!("{name}={value}\n")),
            None => record.push_str(&format!("{line}\n")),
        }
    }
    assert_eq!(record.lines().count(), info.lines().count());
    record
}

/// Trust: EW-9 (22). Only a well-formed independent seed record whose holder is provably
/// gone is judged gone. Every doubt (a live holder or zombie, another purpose or kind, a
/// parent-managed, malformed, oversized or non-UTF-8 record, a link or a non-regular
/// file) is no verdict, and no judgement changes, creates or blocks on anything.
#[cfg(unix)]
#[test]
fn only_a_well_formed_seed_record_whose_holder_is_provably_gone_is_judged_gone() {
    use std::fs;
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let (dead, dead_start, dead_utc) = reaped_process();
    let own = std::process::id();
    let own_start = super::ps("lstart=", &own.to_string()).unwrap();
    let own_utc = super::ps_utc("lstart=", &own.to_string()).unwrap();
    let gone = seed_record(&root, dead, &dead_start, &dead_utc);
    let live = seed_record(&root, own, &own_start, &own_utc);
    // A recycled pid: our live pid, recorded with a start that is not ours. (`lstart` has
    // whole seconds, so the reaped child, started in this test's second, would not do.)
    let epoch = "Thu Jan  1 00:00:00 1970";
    assert_ne!(own_utc, epoch);
    let recycled = seed_record(&root, own, epoch, epoch);
    let edit = |record: &str, key: &str, value: Option<&str>| -> String {
        record
            .lines()
            .filter_map(|line| match line.split_once('=').unwrap() {
                (name, _) if name == key => value.map(|value| format!("{name}={value}\n")),
                _ => Some(format!("{line}\n")),
            })
            .collect()
    };
    let lock = root.join(".trust-build-lock");
    let info = lock.join("info");
    let judge = |bytes: &[u8]| {
        fs::create_dir(&lock).unwrap();
        fs::write(&info, bytes).unwrap();
        let before = snapshot(&root);
        let verdict = super::gone_independent_holder(&root, SEED_SOURCE);
        assert_eq!(snapshot(&root), before, "a judgement changes nothing");
        fs::remove_file(&info).unwrap();
        fs::remove_dir(&lock).unwrap();
        verdict
    };
    assert_eq!(judge(gone.as_bytes()), Some(dead), "no process has its pid");
    assert_eq!(judge(recycled.as_bytes()), Some(own), "its pid names a later process");
    assert_eq!(judge(live.as_bytes()), None, "a live holder");
    // The writer's record, its `cmd` padded to make it `length` bytes long.
    let padded = |length: usize| {
        let pad = length - edit(&gone, "cmd", Some("")).len();
        edit(&gone, "cmd", Some(&"x".repeat(pad)))
    };
    let limit = super::RECORD_LIMIT as usize;
    assert_eq!(judge(padded(limit).as_bytes()), Some(dead), "a record at the limit");
    assert_eq!(judge(padded(limit + 1).as_bytes()), None, "a record one byte over the limit");
    let doubts = [
        (
            "another purpose",
            edit(&gone, "purpose", Some("native compiler check and selected UI test")),
        ),
        (
            "a purpose that only begins as the seed's",
            edit(&gone, "purpose", Some(&format!("{SEED_SOURCE} x"))),
        ),
        ("another kind", edit(&gone, "kind", Some("measure"))),
        ("no zone-free start", edit(&gone, "pstart_utc", None)),
        ("an empty zone-free start", edit(&gone, "pstart_utc", Some(""))),
        ("no pid", edit(&gone, "pid", None)),
        ("pid zero", edit(&gone, "pid", Some("0"))),
        ("a signed pid", edit(&gone, "pid", Some(&format!("+{dead}")))),
        ("a negative pid", edit(&gone, "pid", Some("-1"))),
        ("a padded pid", edit(&gone, "pid", Some(&format!(" {dead}")))),
        ("a pid beyond pid_t", edit(&gone, "pid", Some("4294967295"))),
        ("no token", edit(&gone, "token", None)),
        ("no contract", edit(&gone, "contract", None)),
        ("a parent-managed holder", format!("{gone}release_token=trust-native-repo-owner-x\n")),
        ("an unknown field", format!("{gone}note=x\n")),
        ("an unknown field in place of a known one", edit(&gone, "contract", None) + "note=x\n"),
        ("a line with no field", format!("{gone}stray\n")),
        ("a repeated field", format!("{gone}pid={dead}\n")),
        ("no final newline", gone.trim_end_matches('\n').to_owned()),
        ("a carriage return", gone.replace('\n', "\r\n")),
        ("an empty record", String::new()),
    ];
    for (why, record) in &doubts {
        assert_eq!(judge(record.as_bytes()), None, "{why}");
    }
    let mut invalid = gone.clone().into_bytes();
    invalid.extend_from_slice(b"cmd=\xff\n");
    assert_eq!(judge(&invalid), None, "not UTF-8");

    // A link at either name, or an info that is not a regular file of one link.
    let elsewhere = root.join("elsewhere");
    fs::create_dir(&elsewhere).unwrap();
    fs::write(elsewhere.join("info"), &gone).unwrap();
    fs::create_dir(&lock).unwrap();
    let observe = |why: &str| {
        let before = snapshot(&root);
        assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), None, "{why}");
        assert_eq!(snapshot(&root), before, "a judgement changes nothing: {why}");
    };
    std::os::unix::fs::symlink(elsewhere.join("info"), &info).unwrap();
    observe("a symlinked info");
    fs::remove_file(&info).unwrap();
    fs::hard_link(elsewhere.join("info"), &info).unwrap();
    observe("a hard-linked info");
    fs::remove_file(&info).unwrap();
    fs::create_dir(&info).unwrap();
    observe("a directory at info");
    fs::remove_dir(&info).unwrap();
    let fifo = std::ffi::CString::new(info.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: a NUL-terminated path; mkfifo only creates the named entry.
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    observe("a FIFO at info (and the judgement does not block on it)");
    fs::remove_file(&info).unwrap();
    observe("no info");
    fs::remove_dir(&lock).unwrap();
    std::os::unix::fs::symlink(&elsewhere, &lock).unwrap();
    observe("a symlinked lease directory");
    fs::remove_file(&lock).unwrap();
    observe("no lease");
    // The control: the same record, a regular file in a real lease directory, is judged.
    fs::create_dir(&lock).unwrap();
    fs::copy(elsewhere.join("info"), &info).unwrap();
    assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), Some(dead));
}

/// Trust: EW-9 (22). A zombie holder is alive to the lock script's stale rule, which is
/// what reclaims the lease, so it is not gone here until it is reaped.
#[cfg(unix)]
#[test]
fn a_zombie_seed_holder_is_not_gone_until_it_is_reaped() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let mut child = std::process::Command::new("/bin/cat")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let pid = child.id();
    let start = super::ps("lstart=", &pid.to_string()).unwrap();
    let start_utc = super::ps_utc("lstart=", &pid.to_string()).unwrap();
    let record = seed_record(&root, pid, &start, &start_utc);
    std::fs::create_dir(root.join(".trust-build-lock")).unwrap();
    std::fs::write(root.join(".trust-build-lock/info"), record).unwrap();
    drop(child.stdin.take());
    // Exited and not yet reaped: a zombie, which `ps` reports with state `Z`.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    while !super::ps("stat=", &pid.to_string()).unwrap().starts_with('Z') {
        assert!(std::time::Instant::now() < deadline, "the child never became a zombie");
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), None, "a zombie");
    assert!(child.wait().unwrap().success());
    assert_eq!(super::gone_independent_holder(&root, SEED_SOURCE), Some(pid), "once reaped");
}

/// Trust: EW-9 (22). A live holder whose start `ps` will not give is doubt, never gone,
/// whatever start its record names.
#[cfg(unix)]
#[test]
fn a_live_holder_whose_start_cannot_be_read_is_not_gone() {
    let pid = std::process::id();
    let start_utc = super::ps_utc("lstart=", &pid.to_string()).unwrap();
    let no_answer = |_| Err::<String, String>("ps did not answer".into());
    assert!(!super::holder_is_gone_by(pid, &start_utc, no_answer));
    assert!(!super::holder_is_gone_by(pid, "Thu Jan  1 00:00:00 1970", no_answer));
    // The control: the same live process with a start that differs is judged gone.
    assert!(super::holder_is_gone_by(pid, "Thu Jan  1 00:00:00 1970", |_| Ok(start_utc.clone())));
    assert!(!super::holder_is_gone_by(pid, &start_utc, |_| Ok(start_utc.clone())));
}

/// Trust: EW-9 (22). A process of another user (`kill(2)` answers `EPERM`) exists, so it is
/// judged by its start like any other live holder: pid 1 with its own start is not gone.
#[cfg(unix)]
#[test]
fn a_holder_of_another_user_is_judged_by_its_start() {
    // SAFETY: `geteuid` cannot fail; signal 0 sends nothing.
    let (euid, probe) = unsafe { (libc::geteuid(), libc::kill(1, 0)) };
    // A hard requirement, never a skip: as root, or where pid 1 is this user's (some
    // containers), the EPERM branch cannot be reached and this test fails saying so.
    assert_ne!(euid, 0, "this test needs a user that cannot signal pid 1 (not root)");
    let errno = std::io::Error::last_os_error().raw_os_error();
    assert_eq!(
        (probe, errno),
        (-1, Some(libc::EPERM)),
        "this test needs pid 1 to be another user's"
    );
    let start_utc = super::ps_utc("lstart=", "1").unwrap();
    assert!(!super::holder_is_gone(1, &start_utc), "pid 1 with its own start");
    assert!(super::holder_is_gone(1, "Thu Jan  1 00:00:00 1970"), "pid 1 with another start");
}
