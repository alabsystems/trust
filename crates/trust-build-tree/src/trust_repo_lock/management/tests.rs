use std::io::BufRead;
use std::process::{Child, Command, Stdio};

use super::*;

fn request() -> Acquire {
    Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native ownership regression".into(),
        contract: "one original build tree".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    }
}

fn acquired(manager: &Manager, request: &Acquire) -> String {
    match manager.acquire(request).unwrap() {
        Acquisition::Acquired(token) => token,
        result => panic!("expected new original holder, got {result:?}"),
    }
}

#[test]
fn actual_native_holder_reentry_and_exact_release() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    assert!(manager.status().unwrap().is_free());
    let token = acquired(&manager, &request());
    let status = manager.status().unwrap();
    assert_eq!(status.holder.as_ref().unwrap().liveness, Liveness::Live);
    assert_eq!(status.holder.as_ref().unwrap().pid, std::process::id());
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    let mut nested = request();
    nested.inherited_token = Some(token.clone());
    assert_eq!(manager.acquire(&nested).unwrap(), Acquisition::Borrowed(token.clone()));
    assert_eq!(manager.release("foreign-token").unwrap(), Release::ForeignHolder);
    assert_eq!(manager.release(&token).unwrap(), Release::Released);
    assert_eq!(manager.release(&token).unwrap(), Release::AlreadyFree);
    assert!(manager.status().unwrap().is_free());
}

#[test]
fn native_holder_is_never_group_writable_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "trust_repo_lock::management::tests::native_holder_is_never_group_writable_under_a_group_writable_umask",
        || {
            use std::os::unix::fs::PermissionsExt as _;
            let root = tempfile::tempdir().unwrap();
            let manager = Manager::open(root.path()).unwrap();
            let token = acquired(&manager, &request());
            let holder = fs::symlink_metadata(root.path().join(HOLDER)).unwrap();
            assert_eq!(holder.permissions().mode() & 0o777, 0o755);
            assert_eq!(manager.status().unwrap().holder.unwrap().pid, std::process::id());
            assert_eq!(manager.release(&token).unwrap(), Release::Released);
            assert!(manager.status().unwrap().is_free());
        },
    );
}

// Sets a directory's mode and proves every bit of it took, the special bits
// included. Asked for on a directory whose group is not one of ours (a TMPDIR
// owned by group wheel, say), a setgid bit is dropped without an error, so
// such a directory first gets our effective group.
fn set_directory_mode(path: &Path, mode: u32) {
    use std::os::unix::fs::PermissionsExt as _;
    if mode & 0o2000 != 0 {
        std::os::unix::fs::chown(path, None, Some(unsafe { libc::getegid() })).unwrap();
    }
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
    let actual = fs::symlink_metadata(path).unwrap().permissions().mode() & 0o7777;
    assert_eq!(actual, mode, "{}: mode {actual:04o}, not {mode:04o}", path.display());
}

// The holder this crate made under umask 002 before `create_holder_directory`:
// owned, but group writable. Every verb, `break` included, refuses it and says
// why and how to recover, its path quoted for a shell when the checkout's path
// has a space and a single quote; once it is made owner-only, `break` retires it.
// The refusal names the whole mode, a setgid bit included (2775), and the
// recovery it names (`chmod go-w`, here 2755) keeps that bit and is admitted.
#[test]
fn group_or_other_writable_holder_is_refused_by_mode_until_made_owner_only() {
    use std::os::unix::fs::symlink;
    for (checkout, mode) in [
        (None, 0o775),
        (None, 0o757),
        (None, 0o2775),
        (Some("it's a checkout"), 0o775),
        (Some("it's a checkout"), 0o757),
        (Some("it's a checkout"), 0o2775),
    ] {
        let temporary = tempfile::tempdir().unwrap();
        let root = match checkout {
            Some(name) => {
                let root = temporary.path().join(name);
                fs::create_dir(&root).unwrap();
                root
            }
            None => temporary.path().to_owned(),
        };
        let manager = Manager::open(&root).unwrap();
        let token = acquired(&manager, &request());
        let holder = fs::canonicalize(&root).unwrap().join(HOLDER);
        let info = fs::read(holder.join("info")).unwrap();
        set_directory_mode(&holder, mode);
        let named = format!(
            "holder directory {} is group or other writable (mode {mode:04o});",
            holder.display()
        );
        let recovery = format!(
            "run `chmod go-w {}` and `targo trust repo lock break --reason TEXT`",
            crate::shell_word::quoted(&holder)
        );
        // In a checkout whose path has a space and a single quote, the exact
        // command: the whole path single-quoted, each quote in it `'\''`.
        let exact = checkout.map(|_| {
            let text = holder.to_str().unwrap();
            assert!(text.contains(' ') && text.contains('\''), "{text}");
            format!("run `chmod go-w '{}'` and", text.replace('\'', r"'\''"))
        });
        let mut breaking = request();
        breaking.break_reason = Some("owned fixture group-writable holder control".into());
        let errors = [
            manager.status().map(|_| ()).unwrap_err(),
            manager
                .break_holder("owned fixture group-writable holder control")
                .map(|_| ())
                .unwrap_err(),
            manager.acquire(&breaking).map(|_| ()).unwrap_err(),
            manager.acquire(&request()).map(|_| ()).unwrap_err(),
            manager.release(&token).map(|_| ()).unwrap_err(),
        ];
        for error in errors {
            let error = error.to_string();
            assert!(error.contains(&named) && error.contains(&recovery), "{mode:o}: {error}");
            if let Some(exact) = &exact {
                assert!(error.contains(exact), "{mode:o}: {error}");
            }
        }
        assert_eq!(fs::read(holder.join("info")).unwrap(), info, "a refusal changed the holder");
        // The recovery the refusal names: `chmod go-w`, then `break`.
        set_directory_mode(&holder, mode & !0o022);
        assert_eq!(manager.status().unwrap().holder.unwrap().pid, std::process::id());
        assert!(manager.break_holder("owned fixture group-writable holder recovery").unwrap());
        assert!(manager.status().unwrap().is_free());
        assert!(!holder.exists());
        // A symlink to a group-writable directory is still refused as no owned
        // holder directory at all, not by its target's mode.
        let target = root.join("target");
        fs::create_dir(&target).unwrap();
        set_directory_mode(&target, mode);
        symlink(&target, &holder).unwrap();
        let error = manager.status().map(|_| ()).unwrap_err().to_string();
        assert!(
            error.contains("holder directory must be an owned non-symlink directory"),
            "{error}"
        );
        fs::remove_file(&holder).unwrap();
    }
}

#[test]
fn actual_recycled_birth_is_recovered_but_unknown_start_and_parent_handoff_are_retained() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let path = root.path().join(HOLDER).join("info");
    let original = fs::read_to_string(&path).unwrap();
    let birth = process::read(std::process::id()).unwrap().birth;
    fs::write(&path, original.replace(&format!("native_birth={birth}\n"), "native_birth=1\n"))
        .unwrap();
    assert_eq!(manager.status().unwrap().holder.unwrap().liveness, Liveness::Gone);
    let replacement = acquired(&manager, &request());
    assert_ne!(token, replacement);
    assert!(
        fs::read_to_string(root.path().join(".trust-build-lock.breaks"))
            .unwrap()
            .contains("STALE-TAKEOVER")
    );
    let current = fs::read_to_string(&path).unwrap();
    let unknown = current
        .lines()
        .filter(|line| !line.starts_with("native_birth=") && !line.starts_with("pstart_utc="))
        .collect::<Vec<_>>()
        .join("\n")
        + "\npstart_utc=\n";
    fs::write(&path, &unknown).unwrap();
    assert_eq!(manager.status().unwrap().holder.unwrap().liveness, Liveness::Unknown);
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    fs::write(&path, current + "release_token=\n").unwrap();
    assert_eq!(manager.release(&replacement).unwrap(), Release::ParentManaged);
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    assert!(manager.break_holder("owned fixture cleanup after retained parent control").unwrap());
}

#[test]
fn duplicate_record_fields_and_symlinked_metadata_never_reclaim_or_release() {
    use std::os::unix::fs::symlink;
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let path = root.path().join(HOLDER).join("info");
    let original = fs::read_to_string(&path).unwrap();
    fs::write(&path, original.clone() + "pid=2\n").unwrap();
    assert!(manager.acquire(&request()).is_err());
    assert!(manager.release(&token).is_err());
    let outside = root.path().join("outside");
    fs::rename(&path, &outside).unwrap();
    symlink(&outside, &path).unwrap();
    assert!(manager.status().is_err());
    assert!(manager.release(&token).is_err());
    assert!(manager.break_holder("owned fixture unsafe metadata control").is_err());
    assert_eq!(fs::read_to_string(outside).unwrap(), original + "pid=2\n");
}

#[test]
fn foreign_future_record_and_matching_token_outside_original_family_never_grant_work() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let mut foreign = request();
    foreign.owner_pid = unsafe { libc::getppid() } as u32;
    foreign.inherited_token = Some(token.clone());
    assert!(matches!(manager.acquire(&foreign).unwrap(), Acquisition::Busy(_)));
    let path = root.path().join(HOLDER).join("info");
    let original = fs::read_to_string(&path).unwrap();
    let future = original.clone() + "future_release_owner=unknown\n";
    fs::write(&path, &future).unwrap();
    assert!(manager.acquire(&request()).is_err());
    assert!(manager.release(&token).is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), future);
    fs::write(&path, original).unwrap();
    assert_eq!(manager.release(&token).unwrap(), Release::Released);
}

#[test]
fn namespace_wait_never_covers_a_process_owner_wait() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let path = root.path().to_owned();
    let thread = std::thread::spawn(move || {
        let manager = Manager::open(&path).unwrap();
        let mut waiting = request();
        waiting.wait = Duration::from_secs(5);
        acquired(&manager, &waiting)
    });
    std::thread::sleep(Duration::from_millis(100));
    assert_eq!(manager.release(&token).unwrap(), Release::Released);
    let replacement = thread.join().unwrap();
    assert_eq!(manager.release(&replacement).unwrap(), Release::Released);
}

#[test]
fn native_parent_managed_dead_record_is_never_automatically_recovered() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let path = root.path().join(HOLDER).join("info");
    let original = fs::read_to_string(&path).unwrap();
    let birth = process::read(std::process::id()).unwrap().birth;
    let retained = original.replace(&format!("native_birth={birth}\n"), "native_birth=1\n")
        + "release_parent_pid=\n";
    fs::write(&path, &retained).unwrap();
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    assert_eq!(manager.release(&token).unwrap(), Release::ParentManaged);
    assert_eq!(fs::read_to_string(path).unwrap(), retained);
}

struct Actor(Child, io::BufReader<std::process::ChildStdout>, tempfile::TempDir);
impl Actor {
    fn new(root: &Path) -> Self {
        Self::named(root, "bootstrap")
    }

    fn named(root: &Path, name: &str) -> Self {
        // Execute the exact current native test bytes under the actual kernel
        // bootstrap process name. This is an owned fixture, never a sealed SDK
        // candidate or a claim that a real compiler build took place.
        let image = tempfile::tempdir().unwrap();
        let executable = image.path().join(name);
        fs::copy(std::env::current_exe().unwrap(), &executable).unwrap();
        let mut child = Command::new(executable)
            .args([
                "--exact",
                "trust_repo_lock::management::tests::native_writer_actor",
                "--nocapture",
            ])
            .current_dir(root)
            .env("TRUST_TREE_NATIVE_ACTOR", "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let stdout = child.stdout.take().unwrap();
        let mut reader = io::BufReader::new(stdout);
        loop {
            let mut line = String::new();
            assert_ne!(
                reader.read_line(&mut line).unwrap(),
                0,
                "native actor exited before readiness"
            );
            if line.contains("NATIVE-WRITER-READY") {
                break;
            }
        }
        Self(child, reader, image)
    }
}
impl Drop for Actor {
    fn drop(&mut self) {
        let _retained_native_image = self.2.path();
        drop(self.0.stdin.take());
        let deadline = Instant::now() + Duration::from_secs(3);
        while self.0.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                let _ = self.0.kill();
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        let status = self.0.wait().unwrap();
        let mut remaining = Vec::new();
        let _ = self.1.read_to_end(&mut remaining);
        if !std::thread::panicking() {
            assert!(
                status.success(),
                "native actor failed: {status}: {}",
                String::from_utf8_lossy(&remaining)
            );
        }
    }
}

#[test]
fn native_writer_actor() {
    if std::env::var_os("TRUST_TREE_NATIVE_ACTOR").as_deref() != Some(OsStr::new("1")) {
        return;
    }
    println!("NATIVE-WRITER-READY");
    io::stdout().flush().unwrap();
    let mut byte = [0];
    let _ = io::stdin().read(&mut byte).unwrap();
}

#[test]
fn live_writer_surviving_release_is_adopted_until_actual_reap() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let actor = Actor::new(root.path());
    let status = manager.status().unwrap();
    assert!(status.writers.iter().any(|writer| writer.pid == Some(actor.0.id()) && writer.covered));
    assert!(
        matches!(manager.release(&token).unwrap(), Release::HandedOver(writer) if writer.pid == Some(actor.0.id()))
    );
    let held = manager.status().unwrap().holder.unwrap();
    assert_eq!(held.pid, actor.0.id());
    assert_eq!(held.liveness, Liveness::Live);
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    assert!(
        fs::read_to_string(root.path().join(".trust-build-lock.breaks"))
            .unwrap()
            .contains("ORPHAN-HANDOVER")
    );
    drop(actor);
    let replacement = acquired(&manager, &request());
    assert_eq!(manager.release(&replacement).unwrap(), Release::Released);
}

#[test]
fn native_guard_drop_retains_actual_writer_instead_of_unlocking_tree() {
    let root = tempfile::tempdir().unwrap();
    let lease = super::super::BuildLease::acquire_independent(
        root.path(),
        "native guard surviving-writer control",
        "native current test image",
    )
    .unwrap();
    let actor = Actor::new(root.path());
    drop(lease);
    assert!(
        root.path().join(HOLDER).join("info").is_file(),
        "dropping a native holder must not leave a free tree over its live writer"
    );
    let status = Manager::open(root.path()).unwrap().status().unwrap();
    assert_eq!(status.holder.unwrap().pid, actor.0.id());
}

#[test]
fn native_command_lease_retains_surviving_toolchain_writers_until_actual_reap() {
    for name in ["targo", "trustc", "rust-lld", "compiletest"] {
        let root = tempfile::tempdir().unwrap();
        let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request()).unwrap() {
            LeaseAcquisition::Granted(lease) => lease,
            LeaseAcquisition::Busy(_) => panic!("new isolated test root is busy"),
        };
        // Actual kernel image/name, lifetime and physical cwd. This actor is
        // exclusion evidence only; it is never a compiler/SDK or proof input.
        let actor = Actor::named(root.path(), name);
        drop(lease);
        let manager = Manager::open(root.path()).unwrap();
        let held = manager.status().unwrap().holder.expect("retain original exclusion over writer");
        assert_eq!(held.pid, actor.0.id(), "writer {name}");
        assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
        drop(actor);
        let replacement = acquired(&manager, &request());
        assert_eq!(manager.release(&replacement).unwrap(), Release::Released);
    }
}

#[test]
fn writer_scope_respects_sibling_path_boundaries_and_physical_cwd() {
    let parent = tempfile::tempdir().unwrap();
    let root = parent.path().join("trust");
    let sibling = parent.path().join("trust-sibling");
    fs::create_dir(&root).unwrap();
    fs::create_dir(&sibling).unwrap();
    let actor = Actor::new(&sibling);
    let manager = Manager::open(&root).unwrap();
    assert!(manager.status().unwrap().is_free());
    let other = Manager::open(&sibling).unwrap().status().unwrap();
    assert!(other.writers.iter().any(|writer| writer.pid == Some(actor.0.id())));
    assert!(!names_root(OsStr::new(&format!("--root={}", sibling.display())), &root));
    assert!(names_root(OsStr::new(&format!("--root={}/build", root.display())), &root));
}

#[test]
fn unwrapped_writer_is_adopted_on_refusal_and_foreign_token_cannot_release_it() {
    let root = tempfile::tempdir().unwrap();
    let actor = Actor::new(root.path());
    let manager = Manager::open(root.path()).unwrap();
    // An actual sibling process cannot cover this process tree's live writer.
    let other_root = tempfile::tempdir().unwrap();
    let sibling_owner = Actor::new(other_root.path());
    let mut input = request();
    input.owner_pid = sibling_owner.0.id();
    assert!(matches!(manager.acquire(&input).unwrap(), Acquisition::Busy(_)));
    assert_eq!(manager.release("foreign-token").unwrap(), Release::ForeignHolder);
    assert_eq!(manager.status().unwrap().holder.unwrap().pid, actor.0.id());
}

#[test]
fn sentinel_identity_and_original_root_replacement_refuse_without_deletion() {
    let parent = tempfile::tempdir().unwrap();
    let root = parent.path().join("root");
    fs::create_dir(&root).unwrap();
    let manager = Manager::open(&root).unwrap();
    fs::write(root.join(SENTINEL), format!("pid={}\n", std::process::id())).unwrap();
    assert!(!manager.status().unwrap().is_free());
    assert!(matches!(manager.acquire(&request()).unwrap(), Acquisition::Busy(_)));
    assert!(root.join(SENTINEL).exists());
    fs::rename(&root, parent.path().join("original")).unwrap();
    fs::create_dir(&root).unwrap();
    assert!(manager.acquire(&request()).is_err());
    assert!(manager.status().is_err());
    assert!(!root.join(HOLDER).exists());
}

#[test]
fn recovery_audit_failure_keeps_original_holder_and_unknown_contents() {
    use std::os::unix::fs::symlink;
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let token = acquired(&manager, &request());
    let path = root.path().join(HOLDER).join("info");
    let original = fs::read_to_string(&path).unwrap();
    let outside = root.path().join("unrelated");
    fs::write(&outside, b"keep").unwrap();
    symlink(&outside, root.path().join(".trust-build-lock.breaks")).unwrap();
    assert!(manager.break_holder("owned fixture bad audit control").is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), original);
    assert_eq!(fs::read(&outside).unwrap(), b"keep");
    fs::write(root.path().join(HOLDER).join("unknown"), b"preserve").unwrap();
    assert!(manager.release(&token).is_err());
    assert_eq!(fs::read(root.path().join(HOLDER).join("unknown")).unwrap(), b"preserve");
}

/// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): the census's argv and cwd
/// observations of an actual writer fail while Darwin reports it exiting, then
/// a zombie. Each call site waits and omits it, where `writer_gone` alone
/// refused the whole census (`native writer argv <pid>: ...`).
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
#[test]
fn writer_census_argv_and_cwd_refusals_wait_out_an_exit_and_omit_only_its_zombie() {
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let actor = Actor::new(root.path());
    let pid = actor.0.id();
    let counted = |status: &Status| status.writers.iter().any(|writer| writer.pid == Some(pid));
    assert!(counted(&manager.status().unwrap()), "the live actor is a writer");
    {
        let _argv = process::args_fault(pid, 3, libc::EIO);
        let _exiting = process::exiting_fault(pid, Some(3));
        let status = manager.status().unwrap();
        assert!(!counted(&status), "omitted once a zombie, after its argv refusal");
    }
    {
        let _cwd = process::CwdFault::install(pid, 3, libc::EIO);
        let _exiting = process::exiting_fault(pid, Some(3));
        let status = manager.status().unwrap();
        assert!(!counted(&status), "omitted once a zombie, after its cwd refusal");
    }
    {
        // A refusal that is not an exit stays unknown: the census refuses.
        let _argv = process::args_fault(pid, 3, libc::EIO);
        let error = manager.status().unwrap_err().to_string();
        let refused = io::Error::from_raw_os_error(libc::EIO);
        assert_eq!(error, format!("native writer argv {pid}: KERN_PROCARGS2: {refused}"));
    }
    {
        // The same for cwd, and the refusal names the PID, as argv's does.
        let _cwd = process::CwdFault::install(pid, 3, libc::EIO);
        let error = manager.status().unwrap_err().to_string();
        let refused = io::Error::from_raw_os_error(libc::EIO);
        assert_eq!(error, format!("native writer cwd {pid}: PROC_PIDVNODEPATHINFO: {refused}"));
    }
    assert!(counted(&manager.status().unwrap()), "the actual actor is still a writer");
}

/// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): one census spends one exit wait
/// across all its PIDs. Two actual writers' identity reads fail while Darwin
/// reports each exiting for 1.2 s, then a zombie. The census's budget
/// (CENSUS_EXIT_SETTLE) covers the first exit but not the second, which stays
/// unknown and refuses the census; a budget per PID or per call omits both.
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
#[test]
fn writer_census_spends_one_exit_wait_across_all_its_pids() {
    const SPAN: std::time::Duration = std::time::Duration::from_millis(1200);
    const {
        assert!(SPAN.as_nanos() < process::CENSUS_EXIT_SETTLE.as_nanos());
        assert!(2 * SPAN.as_nanos() > process::CENSUS_EXIT_SETTLE.as_nanos());
    }
    let root = tempfile::tempdir().unwrap();
    let manager = Manager::open(root.path()).unwrap();
    let actors = [Actor::new(root.path()), Actor::new(root.path())];
    let pids = actors.each_ref().map(|actor| actor.0.id());
    let counted = |status: &Status| {
        pids.iter().all(|pid| status.writers.iter().any(|writer| writer.pid == Some(*pid)))
    };
    assert!(counted(&manager.status().unwrap()), "both live actors are writers");
    // The faults hold on the census's own thread only, and a census that hangs
    // fails here. A budget per PID would wait out both exits and succeed, so the
    // error alone refutes it; the wall clock bounds only a hang. The census
    // covers every process of this user, so another one's exit can spend the
    // budget and be the PID named. Only an identity, argv or cwd refusal naming a
    // PID outside the test is retried, in at most five attempts; any other error,
    // including one that names no PID, ends the retries at once.
    let named = |error: &str| {
        pids.iter().any(|pid| error.contains(&format!("native process identity {pid}: ")))
    };
    let foreign = |error: &str| {
        ["native process identity ", "native writer argv ", "native writer cwd "].iter().any(
            |shape| {
                error.split(shape).skip(1).any(|rest| {
                    rest.split_once(": ")
                        .and_then(|(pid, _)| pid.parse::<u32>().ok())
                        .is_some_and(|pid| !pids.contains(&pid))
                })
            },
        )
    };
    let mut attempts = 0;
    let (error, elapsed) = loop {
        attempts += 1;
        let (sender, receiver) = std::sync::mpsc::channel();
        let path = root.path().to_owned();
        std::thread::spawn(move || {
            let _faults = pids.map(|pid| {
                (process::read_errno_fault(pid, 6, libc::ESRCH), process::exiting_for(pid, SPAN))
            });
            let started = std::time::Instant::now();
            let result = Manager::open(&path).unwrap().status().map(|_| ());
            let _ = sender.send((result.map_err(|error| error.to_string()), started.elapsed()));
        });
        let (result, elapsed) =
            receiver.recv_timeout(std::time::Duration::from_secs(60)).expect("the census hung");
        let error = result.expect_err("the second exit outlasts the census's budget");
        if !foreign(&error) || attempts == 5 {
            break (error, elapsed);
        }
    };
    assert!(named(&error), "{error}");
    assert!(elapsed >= process::CENSUS_EXIT_SETTLE, "it spent its budget: {elapsed:?}");
    assert!(counted(&manager.status().unwrap()), "the actual actors are still writers");
}
