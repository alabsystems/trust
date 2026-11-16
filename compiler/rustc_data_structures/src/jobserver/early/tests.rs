//! Actual-source standalone FIRST-entry fixtures; run through the engineering
//! harness, not inside libtest startup while claiming an early FD precondition.
//! Run: `targo --unverified test --locked --manifest-path`
//! `compiler/rustc_data_structures/src/jobserver/early/Cargo.toml --test early-entry`.
#![feature(trust_process_inherit_fds)]
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};

// Compile the actual codegen ownership implementation as well. These controls
// prove original worker joining/credit retention, not whole-compiler behavior.
#[path = "../../../../rustc_codegen_ssa/src/back/worker_ownership.rs"]
mod worker_ownership;

const ISOLATED_LOCK_FIXTURE: &str = "TRUST_EARLY_CUSTODY_LOCK_FIXTURE";

/// Keep the lock owner in a fresh one-case process. An unrelated libtest
/// sibling can fork a copy of an open description until its exec even when
/// CLOEXEC works correctly; waiting for our selected child does not join it.
/// Other outer tests remain parallel, but never possess this fixture's lease.
fn isolated_lock_fixture(body: impl FnOnce()) {
    let current = std::thread::current();
    let test = current.name().expect("named test thread");
    if std::env::var_os(ISOLATED_LOCK_FIXTURE).as_deref() == Some(std::ffi::OsStr::new(test)) {
        return body();
    }
    let output = Command::new(std::env::current_exe().expect("current test executable"))
        .args(["--exact", test, "--test-threads=1"])
        .env(ISOLATED_LOCK_FIXTURE, test)
        .stdin(Stdio::null())
        .output()
        .expect("run the lock owner alone");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success(), "{test}, run alone, failed:\n{report}");
    assert!(stdout.contains("test result: ok. 1 passed;"), "{test} did not run alone:\n{report}");
}

fn command(entry: &str) -> Command {
    let mut command = Command::new(entry);
    command.env_clear();
    command
}

#[test]
fn original_sdk_and_gnu_capture_survive_source_slot_replacement() {
    isolated_lock_fixture(|| {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("sdk-lease");
        let lease = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        lease.try_lock().unwrap();
        let server = jobserver_utils::Jobserver::new(2).unwrap();
        let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        server.configure(&mut cmd);
        cmd.inherit_fd(lease.as_raw_fd());
        cmd.env("ATERM_SDK_LEASE_V3", lease.as_raw_fd().to_string()).env("CUSTODY_JOINT", "1");
        let mut child = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let mut output = BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        assert_eq!(line, "ready\n");
        drop(lease);
        let observer = File::open(&path).unwrap();
        assert!(
            matches!(observer.try_lock(), Err(std::fs::TryLockError::WouldBlock)),
            "original SDK keeper lost its shared-description lock"
        );
        child.stdin.take().unwrap().write_all(b"done\n").unwrap();
        assert!(child.wait().unwrap().success());
        observer.try_lock().unwrap();
    });
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): a bare protocol-1 admission (no
/// GNU pool, nothing else advertised) that asks for the embedded test-harness
/// loan runs its compiler on an owned pool holding no token. The same process
/// that does not ask still refuses, and any advertisement, even dangling, is
/// still judged and refused rather than replaced by a loan.
#[test]
fn a_bare_protocol_one_embedding_borrows_only_its_own_execution() {
    let run = |own: bool, extra: &[(&str, &str)]| {
        let mut command = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        command.env("BUILD_SLOT_CPU_PROTOCOL", "1").env("BUILD_SLOT_HELD", "1");
        if own {
            command.env("CUSTODY_OWN_EXECUTION", "1");
        }
        for (name, value) in extra {
            command.env(name, value);
        }
        command.output().unwrap()
    };
    let lent = run(true, &[]);
    assert!(
        lent.status.success()
            && String::from_utf8_lossy(&lent.stdout).contains("own execution lent"),
        "{lent:?}"
    );
    assert_eq!(run(false, &[]).status.code(), Some(75), "without the loan the compiler refuses");
    for extra in [
        &[("CARGO_MAKEFLAGS", "-j --jobserver-fds=60,61 --jobserver-auth=60,61")][..],
        &[("MAKEFLAGS", "-s")],
        &[("CARGO_JOBSERVER_HANDOFF", "/nonexistent")],
        &[("BUILD_SLOT_CPU_PROTOCOL", "2")],
    ] {
        assert_eq!(
            run(true, extra).status.code(),
            Some(75),
            "{extra:?} is judged, never lent over"
        );
    }
    // A real SDK lease passes its own capture, so only the owed check stands
    // between it and a loan: an SDK-bearing process is not lent over either.
    let temp = tempfile::tempdir().unwrap();
    let lease = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(temp.path().join("sdk-lease"))
        .unwrap();
    lease.try_lock().unwrap();
    for own in [false, true] {
        let mut command = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        command.env("BUILD_SLOT_CPU_PROTOCOL", "1").env("BUILD_SLOT_HELD", "1");
        if own {
            command.env("CUSTODY_OWN_EXECUTION", "1");
        }
        command.inherit_fd(lease.as_raw_fd());
        command.env("ATERM_SDK_LEASE_V3", lease.as_raw_fd().to_string());
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(75), "an SDK lease is not lent over: {output:?}");
    }
}

#[test]
fn invalid_scoped_fifo_never_becomes_an_ambient_or_private_pool() {
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("fifo");
    let native = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: private fixture pathname with a valid NUL terminator, owner-only FIFO.
    assert_eq!(unsafe { libc::mkfifo(native.as_ptr(), 0o600) }, 0);
    let status = command(env!("CARGO_BIN_EXE_early-custody-entry"))
        .env("CARGO_MAKEFLAGS", format!("--jobserver-auth=fifo:{}", path.display()))
        .env("CARGO_JOBSERVER_HANDOFF", "malformed")
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(75));
}

#[test]
fn no_context_keeps_private_cli_limit_and_late_embedding_refuses_inheritance() {
    assert!(
        command(env!("CARGO_BIN_EXE_early-custody-entry"))
            .env("MAKEFLAGS", "w")
            .status()
            .unwrap()
            .success()
    );
    assert!(command(env!("CARGO_BIN_EXE_early-custody-embedded")).status().unwrap().success());
    let status = command(env!("CARGO_BIN_EXE_early-custody-embedded"))
        .env("CARGO_MAKEFLAGS", "--jobserver-auth=3,4")
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(75));
}

#[test]
fn cpu_sdk_only_metadata_retains_sdk_but_never_produces_private_tokens() {
    assert_metadata_custody("-vV", MetadataRoute::Direct);
}

#[test]
fn compiler_protocol_discovery_retains_sdk_but_never_produces_private_tokens() {
    assert_metadata_custody("--resource-capabilities", MetadataRoute::Direct);
}

#[test]
fn cleared_sdk_forwarding_retains_the_original_keeper_and_no_private_tokens() {
    assert_metadata_custody("--resource-capabilities", MetadataRoute::ClearedForward);
}

enum MetadataRoute {
    Direct,
    ClearedForward,
}

fn assert_metadata_custody(query: &str, route: MetadataRoute) {
    isolated_lock_fixture(|| {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("sdk-lease");
        let lease = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        lease.try_lock().unwrap();
        let base = || {
            let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
            cmd.inherit_fd(lease.as_raw_fd());
            cmd.env("ATERM_SDK_LEASE_V3", lease.as_raw_fd().to_string())
                .env("BUILD_SLOT_CPU_PROTOCOL", "3");
            cmd
        };
        assert_eq!(
            base().status().unwrap().code(),
            Some(75),
            "producing entry without GNU must refuse"
        );
        assert_eq!(base().args([query, "--extra"]).status().unwrap().code(), Some(75));
        let mut cmd = base();
        cmd.arg(query).env(
            match route {
                MetadataRoute::Direct => "CUSTODY_METADATA",
                MetadataRoute::ClearedForward => "CUSTODY_FORWARD_METADATA",
            },
            "1",
        );
        let mut child = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let mut output = BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        assert_eq!(line, "ready\n");
        drop(lease);
        let observer = File::open(&path).unwrap();
        assert!(matches!(observer.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
        child.stdin.take().unwrap().write_all(b"done\n").unwrap();
        assert!(child.wait().unwrap().success());
        observer.try_lock().unwrap();
    });
}

#[test]
fn workload_original_is_captured_once_and_never_reimported_from_a_late_locator() {
    isolated_lock_fixture(|| {
        use std::os::fd::{FromRawFd, OwnedFd};
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("workload-cpu");
        let lease = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        lease.try_lock().unwrap();
        // SAFETY: duplicate this actual held fixture description into a source
        // disjoint from stdio and the fixed GNU importer's targets.
        let raw = unsafe { libc::fcntl(lease.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 64) };
        assert!(raw >= 64);
        let inherited = unsafe { OwnedFd::from_raw_fd(raw) };
        let server = jobserver_utils::Jobserver::new(2).unwrap();
        let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        server.configure(&mut cmd);
        cmd.inherit_fd(inherited.as_raw_fd());
        cmd.env("ATERM_WORKLOAD_CPU_FDS_V1", raw.to_string())
            .env("CUSTODY_WORKLOAD_FD", raw.to_string())
            .env("CUSTODY_WORKLOAD", "1");
        let mut child = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let mut output = BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        assert_eq!(line, "ready\n");
        drop(inherited);
        drop(lease);
        let observer = File::open(&path).unwrap();
        assert!(matches!(observer.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
        child.stdin.take().unwrap().write_all(b"done\n").unwrap();
        assert!(child.wait().unwrap().success());
        observer.try_lock().unwrap();
    });
}

#[test]
fn invalid_workload_locator_refuses_even_with_a_valid_inherited_scheduler() {
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    for locator in ["", "3", "malformed", "99999999"] {
        let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        server.configure(&mut cmd);
        assert_eq!(
            cmd.env("ATERM_WORKLOAD_CPU_FDS_V1", locator).status().unwrap().code(),
            Some(75),
            "an invalid selected workload route cannot become ordinary admission"
        );
    }
}

#[test]
fn original_host_directory_is_owned_once_before_config_without_late_import() {
    use std::os::fd::{FromRawFd, OwnedFd};
    use std::os::unix::fs::PermissionsExt;
    let root = tempfile::tempdir().unwrap();
    std::fs::set_permissions(root.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
    assert_eq!(root.path().metadata().unwrap().permissions().mode() & 0o777, 0o700);
    let directory = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW)
        .open(root.path())
        .unwrap();
    let raw = unsafe { libc::fcntl(directory.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 128) };
    assert!(raw >= 128);
    let inherited = unsafe { OwnedFd::from_raw_fd(raw) };
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
    server.configure(&mut cmd);
    cmd.inherit_fd(inherited.as_raw_fd());
    assert!(
        cmd.env("ATERM_WORKLOAD_HOST_STORE_FD_V1", raw.to_string())
            .env("CUSTODY_HOST_STORE_FD", raw.to_string())
            .env("CUSTODY_HOST_STORE", "1")
            .status()
            .unwrap()
            .success()
    );
}

#[test]
fn admitted_compiler_requires_original_host_control_even_after_cpu_is_taken() {
    use std::os::fd::{FromRawFd, OwnedFd};
    use std::os::unix::fs::PermissionsExt;
    let root = tempfile::tempdir().unwrap();
    std::fs::set_permissions(root.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
    let directory = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW)
        .open(root.path())
        .unwrap();
    let lease = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(root.path().join("workload-cpu"))
        .unwrap();
    lease.try_lock().unwrap();
    // SAFETY: both duplications hold actual fixture descriptions in disjoint
    // source slots outside stdio and the fixed GNU importer's targets.
    let cpu_raw = unsafe { libc::fcntl(lease.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 64) };
    assert!(cpu_raw >= 64);
    let cpu = unsafe { OwnedFd::from_raw_fd(cpu_raw) };
    let store_raw = unsafe { libc::fcntl(directory.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 128) };
    assert!(store_raw >= 128);
    let store = unsafe { OwnedFd::from_raw_fd(store_raw) };
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
    server.configure(&mut cmd);
    cmd.inherit_fd(cpu.as_raw_fd());
    cmd.inherit_fd(store.as_raw_fd());
    assert!(
        cmd.env("ATERM_WORKLOAD_CPU_FDS_V1", cpu_raw.to_string())
            .env("ATERM_WORKLOAD_HOST_STORE_FD_V1", store_raw.to_string())
            .env("CUSTODY_WORKLOAD_FD", cpu_raw.to_string())
            .env("CUSTODY_HOST_STORE_FD", store_raw.to_string())
            .env("CUSTODY_MISSING_HOST_CONTROL", "1")
            .status()
            .unwrap()
            .success()
    );
}

#[test]
fn malformed_host_directory_locator_cannot_become_canonical_discovery() {
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    for locator in ["", "5", "malformed", "99999999"] {
        let mut cmd = command(env!("CARGO_BIN_EXE_early-custody-entry"));
        server.configure(&mut cmd);
        assert_eq!(
            cmd.env("ATERM_WORKLOAD_HOST_STORE_FD_V1", locator).status().unwrap().code(),
            Some(75)
        );
    }
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): a fixed-width build-slot
/// (protocol 1) carries no GNU pool. `rustc -V` (Cargo's `#[cargo_test]`) and
/// `rustc --print sysroot` (toolchain discovery) are the same bounded queries
/// as `--version` and `--print=sysroot`, while every producing or widened
/// invocation still refuses and no query mints a scheduler.
#[test]
fn protocol_one_query_spellings_are_the_same_bounded_queries() {
    for query in
        [&["-V"][..], &["--version"], &["-vV"], &["--print", "sysroot"], &["--print=sysroot"]]
    {
        let output = command(env!("CARGO_BIN_EXE_early-custody-entry"))
            .args(query)
            .env("BUILD_SLOT_CPU_PROTOCOL", "1")
            .env("CUSTODY_BOUNDED_QUERY", "1")
            .output()
            .unwrap();
        assert!(
            output.status.success()
                && String::from_utf8_lossy(&output.stdout).contains("bounded query admitted"),
            "{query:?}: {output:?}"
        );
    }
    for args in [
        &[][..],
        &["-V", "-"],
        &["-V", "--crate-type=lib"],
        &["-v"],
        &["-Vv"],
        &["-V="],
        &["--print", "cfg"],
        &["--print", "sysroot", "-"],
    ] {
        let status = command(env!("CARGO_BIN_EXE_early-custody-entry"))
            .args(args)
            .env("BUILD_SLOT_CPU_PROTOCOL", "1")
            .env("CUSTODY_BOUNDED_QUERY", "1")
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(75), "{args:?} is not a bounded query");
    }
    // A grant the driver drops untaken (its session ended before scheduler
    // setup) is spent with it.
    let dropped = command(env!("CARGO_BIN_EXE_early-custody-entry"))
        .arg("--print=sysroot")
        .env("BUILD_SLOT_CPU_PROTOCOL", "1")
        .env("CUSTODY_BOUNDED_QUERY", "1")
        .env("CUSTODY_DROP_GRANT", "1")
        .output()
        .unwrap();
    assert!(
        dropped.status.success()
            && String::from_utf8_lossy(&dropped.stdout).contains("bounded query admitted"),
        "{dropped:?}"
    );
    // A bounded argv is no admission in a process that has a scheduler: an
    // inherited pool, or the embedded loan of its own execution. Neither may
    // grant a session that is answered on no scheduler.
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    let mut scheduled = command(env!("CARGO_BIN_EXE_early-custody-entry"));
    server.configure(&mut scheduled);
    let scheduled =
        scheduled.arg("--print=sysroot").env("BUILD_SLOT_CPU_PROTOCOL", "1").output().unwrap();
    assert!(scheduled.status.success(), "{scheduled:?}");
    let lent = command(env!("CARGO_BIN_EXE_early-custody-entry"))
        .arg("--print=sysroot")
        .env("BUILD_SLOT_CPU_PROTOCOL", "1")
        .env("BUILD_SLOT_HELD", "1")
        .env("CUSTODY_OWN_EXECUTION", "1")
        .output()
        .unwrap();
    assert!(
        lent.status.success()
            && String::from_utf8_lossy(&lent.stdout).contains("own execution lent"),
        "{lent:?}"
    );
}
