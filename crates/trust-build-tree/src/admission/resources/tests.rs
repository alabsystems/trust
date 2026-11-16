use std::time::{Duration, Instant};

use super::*;
use crate::admission::Waiting;

fn requirements(
    worktree: Option<PathBuf>,
    count: u32,
    needed: u32,
    exclusive: bool,
) -> Requirements {
    Requirements::new(worktree, count, needed, exclusive, 0).unwrap()
}
fn attempt(coordinator: &mut Coordinator, maximum: u32) -> io::Result<Attempt<Reservation>> {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match coordinator.attempt(Some(0), maximum)? {
            Attempt::Waiting(Waiting::RegistryBusy) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(1));
            }
            result => return Ok(result),
        }
    }
}
fn admitted(coordinator: &mut Coordinator, maximum: u32) -> Reservation {
    match attempt(coordinator, maximum).unwrap() {
        Attempt::Admitted(reservation) => reservation,
        Attempt::Waiting(reason) => panic!("expected actual kernel reservation, got {reason:?}"),
    }
}
fn free(path: &Path) -> bool {
    let file = OpenOptions::new().read(true).write(true).open(path).unwrap();
    try_exclusive(&file).unwrap()
}

pub(super) fn released(path: &Path) -> bool {
    // Another test can fork while this original open description is live.
    // CLOEXEC closes its inherited copy at exec, not at the parent's Drop.
    // Preserve that real exclusion; allow a bounded wait only AFTER release.
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if free(path) {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

#[test]
fn complete_claim_owns_original_worktree_and_slots_then_releases_all() {
    let root = crate::owner_only::tempdir();
    let adopted = root.path().join("adopted");
    let worktree = root.path().join("worktree.lock");
    let mut coordinator =
        Coordinator::open(root.path(), &adopted, requirements(Some(worktree.clone()), 3, 2, false))
            .unwrap();
    let reservation = admitted(&mut coordinator, 2);
    assert_eq!(reservation.held_slot_count(), 2);
    assert!(!reservation.is_exclusive());
    assert!(!free(&worktree));
    assert!(!free(&root.path().join("slot-0")));
    assert!(!free(&root.path().join("slot-1")));
    assert!(coordinator.ticket.original.is_none());
    reservation.check_current().unwrap();
    drop(reservation);
    assert!(released(&worktree));
    assert!(released(&root.path().join("slot-0")));
    assert!(released(&root.path().join("slot-1")));
}

/// Asserts that `error` is the refusal of the owned directory `directory`
/// because it is group or other writable, naming the mode it has now and the
/// recovery, and returns that mode. The mode is read, not assumed: on Linux a
/// directory made in a setgid one inherits S_ISGID, so under umask 002 it is
/// 02775, not 0775.
pub(super) fn refused_by_mode(error: &io::Error, directory: &Path) -> u32 {
    use std::os::unix::fs::MetadataExt as _;
    let mode = fs::symlink_metadata(directory).unwrap().mode() & 0o7777;
    assert_ne!(mode & 0o022, 0, "{} is not group or other writable", directory.display());
    let text = error.to_string();
    assert_eq!(error.kind(), io::ErrorKind::InvalidData, "{text}");
    let named = format!(
        "admission directory {} is group or other writable (mode {mode:04o});",
        directory.display()
    );
    let recovery = format!("run `chmod go-w {}`", crate::shell_word::quoted(directory));
    assert!(text.contains(&named) && text.contains(&recovery), "{text}");
    mode
}

/// The exact recovery a refusal names for `directory`, whose path has a space
/// and a single quote: the whole path single-quoted, each quote in it `'\''`.
pub(super) fn quoted_chmod_go_w(directory: &Path) -> String {
    let text = directory.to_str().unwrap();
    assert!(text.contains(' ') && text.contains('\''), "{text}");
    format!("run `chmod go-w '{}'`", text.replace('\'', r"'\''"))
}

/// Runs the `chmod go-w` that `error` names in a POSIX shell, as its reader
/// would paste it, and asserts that `directory` then has its former mode less
/// the group and other write bits. Only a test that runs alone in its own
/// process may run it (`crate::owner_only::under_umask_002`): another test's
/// lease must never be copied into the shell between its fork and its exec.
pub(super) fn run_named_chmod_go_w(error: &io::Error, directory: &Path) {
    use std::os::unix::fs::MetadataExt as _;
    assert!(crate::trust_output_lock::tests::running_alone(), "a shell runs only in a lone test");
    let text = error.to_string();
    let command = text
        .split_once("run `")
        .and_then(|(_, rest)| rest.split_once('`'))
        .map(|(command, _)| command)
        .unwrap_or_else(|| panic!("no command named: {text}"));
    assert!(command.starts_with("chmod go-w "), "{text}");
    let before = fs::symlink_metadata(directory).unwrap().mode() & 0o7777;
    let status = std::process::Command::new("/bin/sh")
        .args(["-c", command])
        .stdin(std::process::Stdio::null())
        .status()
        .unwrap();
    assert!(status.success(), "{command}");
    let after = fs::symlink_metadata(directory).unwrap().mode() & 0o7777;
    assert_eq!(after, before & !0o022, "{command}");
}

/// `chmod go-w`, the recovery a refusal by mode names.
pub(super) fn chmod_go_w(directory: &Path) {
    use std::os::unix::fs::PermissionsExt as _;
    let mode = fs::symlink_metadata(directory).unwrap().permissions().mode();
    fs::set_permissions(directory, fs::Permissions::from_mode(mode & !0o022)).unwrap();
}

// Under umask 002 the launcher's files are still 0644, and admitted; its
// directories are not checked here (see the two tests after this one).
#[test]
fn launcher_files_in_an_owner_only_namespace_are_admitted_but_a_group_writable_slot_is_not() {
    crate::owner_only::under_umask_002(
        "admission::resources::tests::launcher_files_in_an_owner_only_namespace_are_admitted_but_a_group_writable_slot_is_not",
        || {
            use std::os::unix::fs::PermissionsExt as _;
            let root = crate::owner_only::tempdir();
            let adopted = root.path().join("adopted");
            let worktree = root.path().join("worktree.lock");
            let slot = root.path().join("slot-0");
            // scripts/build-slot made these first, each 0644.
            for path in [&slot, &root.path().join("admission.lock"), &worktree] {
                crate::launcher_file::write(path, b"");
            }
            let mut coordinator = Coordinator::open(
                root.path(),
                &adopted,
                requirements(Some(worktree.clone()), 1, 1, false),
            )
            .unwrap();
            let reservation = admitted(&mut coordinator, 1);
            assert!(!free(&slot));
            assert!(!free(&worktree));
            reservation.check_current().unwrap();
            drop(reservation);
            assert!(released(&slot));
            for path in [&slot, &root.path().join("admission.lock"), &worktree] {
                assert_eq!(fs::metadata(path).unwrap().permissions().mode() & 0o7777, 0o644);
            }
            fs::set_permissions(&slot, fs::Permissions::from_mode(0o664)).unwrap();
            assert!(lease(&slot, false, &adopted).is_err(), "a group-writable slot was leased");
        },
    );
}

// git's `<git-dir>`, which holds the worktree lease, as git makes it under the
// usual umask 022, and a namespace an older scripts/build-slot made there with
// os.makedirs: each 0755. The current build-slot never changes such a
// namespace. Both are admitted; either made group writable is refused by its
// mode.
#[test]
fn launcher_namespace_and_git_dir_at_0755_are_admitted_and_at_0775_are_refused_by_mode() {
    use std::os::unix::fs::PermissionsExt as _;
    let root = crate::owner_only::tempdir();
    let namespace = root.path().join("build-slot");
    let git = root.path().join(".git");
    crate::launcher_file::create_dir(&namespace);
    crate::launcher_file::create_dir(&git);
    let adopted = namespace.join("adopted");
    let worktree = git.join("build-slot.lock");
    let required = || requirements(Some(worktree.clone()), 1, 1, false);
    let mut coordinator = Coordinator::open(&namespace, &adopted, required()).unwrap();
    let reservation = admitted(&mut coordinator, 1);
    assert!(!free(&worktree));
    assert!(!free(&namespace.join("slot-0")));
    reservation.check_current().unwrap();
    drop(reservation);
    assert!(released(&worktree));
    drop(coordinator);

    fs::set_permissions(&namespace, fs::Permissions::from_mode(0o775)).unwrap();
    let error = Coordinator::open(&namespace, &adopted, required()).err().unwrap();
    assert_eq!(refused_by_mode(&error, &namespace), 0o775);
    chmod_go_w(&namespace);
    // On Linux a directory made in a setgid one inherits S_ISGID, so under umask
    // 002 it is 02775: the refusal names that whole mode, and `chmod go-w`, which
    // keeps S_ISGID, admits it.
    fs::set_permissions(&namespace, fs::Permissions::from_mode(0o2775)).unwrap();
    let error = Coordinator::open(&namespace, &adopted, required()).err().unwrap();
    assert_eq!(refused_by_mode(&error, &namespace), 0o2775, "chmod kept S_ISGID for its owner");
    chmod_go_w(&namespace);
    fs::set_permissions(&git, fs::Permissions::from_mode(0o775)).unwrap();
    let mut coordinator = Coordinator::open(&namespace, &adopted, required()).unwrap();
    assert_eq!(refused_by_mode(&attempt(&mut coordinator, 1).err().unwrap(), &git), 0o775);
    assert!(free(&worktree), "a refused worktree lease stayed held");
}

// Under umask 002 git makes `<git-dir>` with plain mkdir, 0775, and an older
// scripts/build-slot made its namespace with os.makedirs, 0775 too; the current
// one makes each missing component 0700 and never changes an existing
// directory, so such a namespace remains (TBT-WORKER-EPOCH-LINUX-1). Admission
// refuses each by name and mode, and the `chmod go-w` it names, pasted into a
// shell, admits it, also when the path has a space and a single quote.
#[test]
fn namespace_and_git_dir_made_under_umask_002_are_refused_by_mode_until_chmod_go_w() {
    crate::owner_only::under_umask_002(
        "admission::resources::tests::namespace_and_git_dir_made_under_umask_002_are_refused_by_mode_until_chmod_go_w",
        || {
            for (cache, repository) in [("cache", "repository"), ("it's a cache", "it's a repo")] {
                let needs_quotes = cache.contains('\'');
                let root = crate::owner_only::tempdir();
                let namespace = root.path().join(cache).join("build-slot");
                fs::create_dir_all(&namespace).unwrap();
                let repository = root.path().join(repository);
                fs::create_dir(&repository).unwrap();
                let git = repository.join(".git");
                fs::create_dir(&git).unwrap();
                let adopted = namespace.join("adopted");
                let worktree = git.join("build-slot.lock");
                let required = || requirements(Some(worktree.clone()), 1, 1, false);
                let error = Coordinator::open(&namespace, &adopted, required()).err().unwrap();
                refused_by_mode(&error, &namespace);
                if needs_quotes {
                    assert!(error.to_string().contains(&quoted_chmod_go_w(&namespace)), "{error}");
                }
                run_named_chmod_go_w(&error, &namespace);
                let mut coordinator = Coordinator::open(&namespace, &adopted, required()).unwrap();
                let error = attempt(&mut coordinator, 1).err().unwrap();
                refused_by_mode(&error, &git);
                if needs_quotes {
                    assert!(error.to_string().contains(&quoted_chmod_go_w(&git)), "{error}");
                }
                run_named_chmod_go_w(&error, &git);
                let reservation = admitted(&mut coordinator, 1);
                assert!(!free(&worktree));
                drop(reservation);
                assert!(released(&worktree));
            }
        },
    );
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            complete_claim_owns_original_worktree_and_slots_then_releases_all();
            original_path_replacement_never_adopts_or_deletes_new_slot();
        },
    );
}

#[test]
fn unknown_memory_never_reserves_exclusive_even_with_zero_byte_threshold() {
    let root = crate::owner_only::tempdir();
    let adopted = root.path().join("adopted");
    let mut coordinator =
        Coordinator::open(root.path(), &adopted, requirements(None, 1, 1, true)).unwrap();
    assert!(matches!(
        coordinator.attempt(None, 1).unwrap(),
        Attempt::Waiting(Waiting::MemoryUnavailable)
    ));
    assert!(coordinator.ticket.original.is_none());
    assert!(!root.path().join("admission.lock").exists());
}

#[test]
fn current_locations_actor() {
    if std::env::var_os("TRUST_ADMISSION_LOCATIONS_ACTOR").is_none() {
        return;
    }
    let locations = Locations::current().unwrap();
    let expected =
        fs::canonicalize(std::env::var_os("TRUST_ADMISSION_EXPECTED_NAMESPACE").unwrap()).unwrap();
    assert_eq!(locations.namespace, expected);
    let fake_home = PathBuf::from(std::env::var_os("HOME").unwrap());
    assert!(!locations.adopted.starts_with(&fake_home));
    assert_eq!(locations.adopted, account_home().unwrap().join(".cache/build-slot/adopted"));
}

#[test]
fn resource_lifetime_actor() {
    let Some(root) = std::env::var_os("TRUST_ADMISSION_RESOURCE_ACTOR") else { return };
    let root = PathBuf::from(root);
    let mut coordinator = Coordinator::open(
        &root,
        &root.join("adopted"),
        requirements(Some(root.join("worktree.lock")), 1, 1, false),
    )
    .unwrap();
    let _reservation = admitted(&mut coordinator, 1);
    println!("ORIGINAL-RESOURCES-HELD");
    io::stdout().flush().unwrap();
    let mut token = [0];
    io::stdin().read_exact(&mut token).unwrap();
    assert_eq!(token, [83]);
    // The actual kernel must close all original claims without Rust Drop.
    std::process::exit(83);
}

#[test]
fn actual_process_exit_without_destructors_releases_original_resource_claim() {
    use std::io::{BufRead, BufReader};
    use std::process::{Child, Command, Stdio};
    struct Owned(Child);
    impl Drop for Owned {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let root = crate::owner_only::tempdir();
    let mut child = Owned(
        Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "admission::resources::tests::resource_lifetime_actor",
                "--nocapture",
            ])
            .env("TRUST_ADMISSION_RESOURCE_ACTOR", root.path())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let stdout = child.0.stdout.take().unwrap();
    let (send, receive) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        let result = BufReader::new(stdout)
            .lines()
            .find_map(|line| match line {
                Ok(line) if line == "ORIGINAL-RESOURCES-HELD" => Some(Ok(())),
                Ok(_) => None,
                Err(error) => Some(Err(error)),
            })
            .unwrap_or_else(|| {
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "original resource actor exited before readiness",
                ))
            });
        let _ = send.send(result);
    });
    receive.recv_timeout(Duration::from_secs(10)).unwrap().unwrap();
    reader.join().unwrap();
    for path in ["worktree.lock", "slot-0", "admission.lock"] {
        assert!(!free(&root.path().join(path)), "original actor must hold {path}");
    }
    child.0.stdin.as_mut().unwrap().write_all(&[83]).unwrap();
    assert_eq!(child.0.wait().unwrap().code(), Some(83));
    for path in ["worktree.lock", "slot-0", "admission.lock"] {
        assert!(released(&root.path().join(path)), "kernel must release {path} after actual exit");
    }
}

#[test]
fn forked_resource_lifetime_actor() {
    if std::env::var_os("TRUST_ADMISSION_FORKED_RESOURCE_ACTOR").is_none() {
        return;
    }
    let root = crate::owner_only::tempdir();
    let worktree = root.path().join("worktree.lock");
    let mut coordinator = Coordinator::open(
        root.path(),
        &root.path().join("adopted"),
        requirements(Some(worktree), 1, 1, false),
    )
    .unwrap();
    let reservation = admitted(&mut coordinator, 1);
    let mut pipe = [-1; 2];
    assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        // Only async-signal-safe calls after fork. Keep the inherited original
        // open descriptions until the parent explicitly releases this actor.
        unsafe {
            libc::close(pipe[1]);
            let mut token = 0_u8;
            let read = libc::read(pipe[0], (&mut token as *mut u8).cast(), 1);
            libc::_exit(if read == 1 && token == 83 { 83 } else { 84 });
        }
    }
    assert!(pid > 0);
    struct Forked(libc::pid_t);
    impl Drop for Forked {
        fn drop(&mut self) {
            if self.0 > 0 {
                unsafe {
                    libc::kill(self.0, libc::SIGKILL);
                    libc::waitpid(self.0, std::ptr::null_mut(), 0);
                }
            }
        }
    }
    let mut child = Forked(pid);
    unsafe { libc::close(pipe[0]) };
    let mut release = unsafe { File::from_raw_fd(pipe[1]) };
    drop(reservation);
    for path in ["worktree.lock", "slot-0", "admission.lock"] {
        assert!(!free(&root.path().join(path)), "fork still owns original {path}");
    }
    release.write_all(&[83]).unwrap();
    drop(release);
    let mut status = 0;
    assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
    child.0 = 0;
    assert!(libc::WIFEXITED(status));
    assert_eq!(libc::WEXITSTATUS(status), 83);
    for path in ["worktree.lock", "slot-0", "admission.lock"] {
        assert!(free(&root.path().join(path)), "actual reap releases original {path}");
    }
}

#[test]
fn actual_fork_retains_original_claim_after_parent_closes_it() {
    // Fork in an isolated executable so this deterministic control cannot
    // inherit other concurrently running tests' original claims.
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "admission::resources::tests::forked_resource_lifetime_actor",
            "--nocapture",
        ])
        .env("TRUST_ADMISSION_FORKED_RESOURCE_ACTOR", "1")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
}

#[test]
fn canonical_adoption_ignores_scratch_home_and_keeps_explicit_namespace_override() {
    let root = crate::owner_only::tempdir();
    let fake_home = root.path().join("scratch-home");
    crate::owner_only::create_dir(&fake_home);
    let selected = root.path().join("selected");
    crate::owner_only::create_dir(&selected);
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "admission::resources::tests::current_locations_actor", "--nocapture"])
        .env("TRUST_ADMISSION_LOCATIONS_ACTOR", "1")
        .env("TRUST_ADMISSION_EXPECTED_NAMESPACE", &selected)
        .env("BUILD_SLOT_DIR", &selected)
        .env("HOME", &fake_home)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(!selected.join("admission").exists());
    assert_eq!(fs::read_dir(&fake_home).unwrap().count(), 0);
}

#[test]
fn failed_full_claim_releases_every_partial_slot_worktree_and_admission_lock() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::tests::failed_full_claim_releases_every_partial_slot_worktree_and_admission_lock",
        || {
            let root = crate::owner_only::tempdir();
            let adopted = root.path().join("adopted");
            let worktree = root.path().join("worktree.lock");
            let busy = lease(&root.path().join("slot-1"), false, &adopted).unwrap().unwrap();
            let mut coordinator = Coordinator::open(
                root.path(),
                &adopted,
                requirements(Some(worktree.clone()), 2, 2, false),
            )
            .unwrap();
            assert!(matches!(
                attempt(&mut coordinator, 2).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(released(&worktree));
            assert!(released(&root.path().join("slot-0")));
            assert!(released(&root.path().join("admission.lock")));
            drop(busy);
            assert!(released(&root.path().join("slot-1")));
            assert_eq!(admitted(&mut coordinator, 2).held_slot_count(), 2);
        },
    );
}

#[test]
fn idle_borrowing_is_bounded_by_original_pool_and_actual_busy_slots() {
    let root = crate::owner_only::tempdir();
    let adopted = root.path().join("adopted");
    let _busy = lease(&root.path().join("slot-1"), false, &adopted).unwrap().unwrap();
    let mut coordinator =
        Coordinator::open(root.path(), &adopted, requirements(None, 3, 1, false)).unwrap();
    assert!(coordinator.attempt(Some(0), 4).is_err());
    assert!(coordinator.attempt(Some(0), 0).is_err());
    let mut reservation = admitted(&mut coordinator, 3);
    assert_eq!(reservation.held_slot_count(), 2);
    assert!(!root.path().join("slot-3").exists());
    assert!(reservation.try_drain_exclusive().is_err());
}

#[test]
fn exclusive_winner_retains_admission_and_worktree_while_old_slots_drain() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::tests::exclusive_winner_retains_admission_and_worktree_while_old_slots_drain",
        || {
            let root = crate::owner_only::tempdir();
            let adopted = root.path().join("adopted");
            let worktree = root.path().join("worktree.lock");
            let old = lease(&root.path().join("slot-0"), false, &adopted).unwrap().unwrap();
            // Cover an actual historic larger pool, including a noncanonical numeric
            // spelling; bounded enumeration fences the original file itself.
            crate::launcher_file::write(&root.path().join("slot-9"), &[]);
            crate::launcher_file::write(&root.path().join("slot-00"), &[]);
            let mut coordinator = Coordinator::open(
                root.path(),
                &adopted,
                requirements(Some(worktree.clone()), 2, 1, true),
            )
            .unwrap();
            let mut reservation = admitted(&mut coordinator, 1);
            assert!(!free(&worktree));
            assert!(!free(&root.path().join("admission.lock")));
            assert!(!reservation.try_drain_exclusive().unwrap());
            assert_eq!(reservation.held_slot_count(), 0);
            drop(old);
            assert!(released(&root.path().join("slot-0")));
            assert!(reservation.try_drain_exclusive().unwrap());
            assert_eq!(reservation.held_slot_count(), 4);
            for slot in ["slot-0", "slot-1", "slot-9", "slot-00"] {
                assert!(!free(&root.path().join(slot)));
            }
            drop(reservation);
            assert!(released(&worktree));
            assert!(released(&root.path().join("admission.lock")));
        },
    );
}

#[test]
fn adopted_debt_is_reobserved_under_each_actual_slot_lock() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::tests::adopted_debt_is_reobserved_under_each_actual_slot_lock",
        || {
            let root = crate::owner_only::tempdir();
            let adopted = root.path().join("adopted");
            crate::owner_only::create_dir(&adopted);
            let slot = root.path().join("slot-0");
            crate::launcher_file::write(&slot, &[]);
            let slot = fs::canonicalize(slot).unwrap();
            let pid = std::process::id();
            let birth = crate::trust_repo_lock::management::process::live_adoption_birth(pid)
                .unwrap()
                .unwrap();
            let record = serde_json::json!({"schema":1,"adopted":true,"pid":pid,"identity":{"pid":pid,"uid":unsafe{libc::geteuid()},"birth":birth,"executable":"/old/program"},"pool":root.path(),"worktree":null,"leases":[slot]});
            let path = adopted.join("live.json");
            crate::owner_only::write(&path, &serde_json::to_vec(&record).unwrap());
            let mut coordinator =
                Coordinator::open(root.path(), &adopted, requirements(None, 1, 1, false)).unwrap();
            assert!(matches!(
                attempt(&mut coordinator, 1).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(path.exists());
            assert!(released(&root.path().join("admission.lock")));
            // A later process birth is genuinely distinct, not the same PID's exec.
            let mut stale = record;
            stale["identity"]["birth"] = serde_json::json!(if cfg!(target_os = "macos") {
                "darwin:1:1"
            } else {
                "linux:00000000-0000-0000-0000-000000000000:1"
            });
            fs::write(&path, serde_json::to_vec(&stale).unwrap()).unwrap();
            assert_eq!(admitted(&mut coordinator, 1).held_slot_count(), 1);
            assert!(!path.exists());
        },
    );
}

#[test]
fn original_path_replacement_never_adopts_or_deletes_new_slot() {
    let root = crate::owner_only::tempdir();
    let adopted = root.path().join("adopted");
    let mut coordinator =
        Coordinator::open(root.path(), &adopted, requirements(None, 1, 1, false)).unwrap();
    let reservation = admitted(&mut coordinator, 1);
    let slot = root.path().join("slot-0");
    fs::rename(&slot, root.path().join("original-slot")).unwrap();
    crate::owner_only::write(&slot, b"replacement");
    assert!(reservation.check_current().is_err());
    drop(reservation);
    assert_eq!(fs::read(&slot).unwrap(), b"replacement");
    assert!(released(&root.path().join("original-slot")));
}
