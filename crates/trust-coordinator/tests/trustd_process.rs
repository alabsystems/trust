// Process-level contract tests for trustd's CLI and singleton socket ownership.
// These exercise behavior that an in-process unit test cannot prove: information
// flags must terminate before daemon startup, exit codes are stable, and two OS
// processes cannot both become the authority for one socket path.

#![cfg(unix)]

use std::ffi::OsString;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
#[cfg(not(target_vendor = "apple"))]
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_coordinator::coordinator::{
    DISABLE_ENV, IDENTITY_VERSION, SOCK_ENV, STATUS_VERSION, daemon_matches_executable,
    daemon_matches_executable_from_pid, ensure_daemon, exercise_daemon_at,
    exercise_daemon_at_from_pid, identity_at, ping_at, recover_dirty_epoch_after_quiescence,
    status_at,
};

/// The built `trustd`, already executed once in this process (see
/// [`run_once_before_any_deadline`]): a push lane links it fresh, and the first
/// test to start it would otherwise pay its first-run assessment inside a
/// three-second readiness wait. Every caller resolves the path before it starts
/// a clock, and concurrent callers wait here for the one warm-up.
fn trustd() -> &'static str {
    static FIRST_RUN: std::sync::Once = std::sync::Once::new();
    let executable = env!("CARGO_BIN_EXE_trustd");
    FIRST_RUN.call_once(|| run_once_before_any_deadline(Path::new(executable), "--help"));
    executable
}

/// Execute a freshly created executable once, before any test times something
/// it starts. `arg` must make it exit without serving (`--help` for `trustd`,
/// `--list` for a test binary).
///
/// macOS assesses a file the first time it is executed (the build outputs and
/// their copies carry `com.apple.provenance`; `std::fs::copy` makes an APFS
/// clone, which is a new file to that check), and it assesses first executions
/// ONE AT A TIME, machine-wide. The wait is outside the process: `spawn`
/// returns at once and the child runs only when the check finishes. Measured
/// 2026-10-01 on 14 cores: a freshly linked `trustd` took 271 ms to its first
/// `--version` and 7 ms after; a copy of the 490 MB `trust-router` lib test
/// binary takes 3-6 s to its first exec, and copies started together are
/// checked serially. A push lane starts freshly linked test binaries side by
/// side, so that queue is real there. With only two such copies queued first,
/// `runtime_identity_is_the_exact_executable_and_wrong_binary_is_rejected` and
/// `exact_daemon_completes_the_live_reserve_release_smoke` failed their 3 s
/// `wait_for_status`; with nine, the launcher never reported readiness inside
/// `ensure_daemon_survives_its_launchers_process_group_being_killed`'s 30 s
/// (and the launcher's own `ensure_daemon` allows its fresh `trustd` 5 s).
/// Paying the check here keeps it out of those waits; the incremental-session
/// fixtures in `trust-router`'s `incremental_ay` tests warm their stand-in
/// solver for the same reason.
fn run_once_before_any_deadline(executable: &Path, arg: &str) {
    let status = Command::new(executable)
        .arg(arg)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .unwrap_or_else(|error| panic!("run {} {arg} once: {error}", executable.display()));
    assert!(status.success(), "{} {arg} failed: {status:?}", executable.display());
}

struct SocketFixture {
    root: PathBuf,
    path: PathBuf,
}

impl SocketFixture {
    fn new() -> Self {
        Self::with_file_name(OsString::from("daemon.sock"))
    }

    fn with_file_name(file_name: OsString) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        // trustd stages a private socket beneath the target parent before
        // publication. Darwin's AF_UNIX namespace is only 104 bytes, so use the
        // same short canonical /tmp namespace as production instead of the much
        // longer per-session $TMPDIR path.
        let temp_root = std::fs::canonicalize("/tmp").expect("canonical system temporary root");
        for _ in 0..128 {
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = temp_root.join(format!("td-{}-{sequence}", std::process::id()));
            let mut builder = std::fs::DirBuilder::new();
            builder.mode(0o700);
            match builder.create(&root) {
                Ok(()) => {
                    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))
                        .expect("make socket fixture directory private");
                    let path = root.join(file_name);
                    return Self { root, path };
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create socket fixture directory: {error}"),
            }
        }
        panic!("could not allocate a unique socket fixture directory")
    }

    fn lock_path(&self) -> PathBuf {
        let mut path = self.path.as_os_str().to_owned();
        path.push(".lock");
        PathBuf::from(path)
    }

    fn cleanup(&self) {
        // The stable sentinel lives outside this target-like fixture. Remove it
        // only after validating its private identity, taking its nonblocking
        // kernel lock, and confirming the pathname still names the opened inode.
        // If a daemon survived a panicking test, leave every artifact intact so
        // cleanup cannot split its authority domain.
        let runtime_socket = match trust_coordinator::coordinator::host_socket_path() {
            Ok(path) => path,
            Err(_) => return,
        };
        let Some(runtime_root) = runtime_socket.parent() else {
            return;
        };
        let digest = Sha256::digest(self.path.as_os_str().as_bytes());
        let sentinel = runtime_root.join(format!("{digest:x}.lock"));
        let mut sentinel_guard = None;
        let mut options = OpenOptions::new();
        options.read(true).write(true).custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
        match options.open(&sentinel) {
            Ok(file) => {
                let metadata = match file.metadata() {
                    Ok(metadata)
                        if metadata.file_type().is_file()
                            && metadata.uid() == unsafe { libc::geteuid() }
                            && metadata.permissions().mode() & 0o077 == 0
                            && metadata.nlink() == 1 =>
                    {
                        metadata
                    }
                    _ => return,
                };
                if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
                    return;
                }
                let still_same = std::fs::symlink_metadata(&sentinel).is_ok_and(|current| {
                    current.file_type().is_file()
                        && current.dev() == metadata.dev()
                        && current.ino() == metadata.ino()
                });
                if !still_same || std::fs::remove_file(&sentinel).is_err() {
                    return;
                }
                sentinel_guard = Some(file);
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return,
        }
        let _ = std::fs::remove_file(&self.path);
        let _ = std::fs::remove_file(self.lock_path());
        let _ = std::fs::remove_dir(&self.root);
        drop(sentinel_guard);
    }
}

impl Drop for SocketFixture {
    fn drop(&mut self) {
        self.cleanup();
    }
}

struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn wait_for_exit(child: &mut Child, timeout: Duration) -> Option<ExitStatus> {
    let start = Instant::now();
    while start.elapsed() < timeout {
        if let Some(status) = child.try_wait().expect("poll child") {
            return Some(status);
        }
        thread::sleep(Duration::from_millis(10));
    }
    None
}

fn wait_for_status(path: &Path, timeout: Duration) -> bool {
    let start = Instant::now();
    while start.elapsed() < timeout {
        if status_at(path).is_some() {
            return true;
        }
        thread::sleep(Duration::from_millis(10));
    }
    false
}

fn spawn_trustd(path: &Path) -> Child {
    spawn_trustd_executable(path, Path::new(trustd()))
}

fn spawn_trustd_executable(path: &Path, executable: &Path) -> Child {
    Command::new(executable)
        .arg("--socket")
        .arg(path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("start trustd")
}

// Build directories may be group-writable, and fs::copy preserves the source
// executable's mode. Authority tests need a private package without changing
// the build tree or relaxing the production executable-path checks.
fn copy_private_executable(source: &Path, destination: &Path) {
    std::fs::copy(source, destination).expect("copy packaged executable");
    std::fs::set_permissions(destination, std::fs::Permissions::from_mode(0o700))
        .expect("make packaged executable private");
}

fn recover_after_confirmed_quiescence(path: &Path) {
    let output = Command::new(trustd())
        .args(["--recover-after-crash", "--confirm-no-solvers", "--socket"])
        .arg(path)
        .output()
        .expect("run explicit trustd crash recovery");
    assert!(
        output.status.success(),
        "explicit crash recovery failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn executable_sha256(path: &Path) -> String {
    let bytes = std::fs::read(path).expect("read executable for identity hash");
    format!("{:x}", Sha256::digest(bytes))
}

/// Whether this host can derive a nonzero effective-memory budget.
///
/// On a bare-metal initial-namespace Linux host the cgroup-v2 mount root has no
/// `memory.max`, and `linux_visible_cgroup_limit_with`
/// (src/memory_jobserver.rs:1715-1723) DELIBERATELY fails closed: a cgroup
/// namespace can present a constrained descendant as `/`, so a missing visible
/// control file is never accepted as proof of an unbounded hierarchy root, and
/// a future exception needs an authenticated initial-namespace proof.
/// `machine_budget_bytes()` is then 0 and every nonzero RESERVE answers
/// DEGRADED. This probe is a platform-availability observation ONLY — never
/// authority: where it reports 0 the tests below pin the documented fail-closed
/// contract instead of the grant protocol, and where the budget derives
/// (macOS sysctl, limit-visible containers) the full protocol asserts run
/// unchanged. The gate is budget availability, not target_os.
fn host_budget_available() -> bool {
    trust_coordinator::memory_jobserver::machine_budget_bytes() != 0
}

/// Raw single-line RESERVE exchange against a live daemon; returns the trimmed
/// reply line. Bounded by a read timeout so a wedged daemon fails the test
/// instead of hanging it.
fn reserve_reply_at(path: &Path, bytes: u64, label: &str) -> String {
    let mut client = UnixStream::connect(path).expect("connect RESERVE probe");
    client
        .set_read_timeout(Some(Duration::from_secs(2)))
        .expect("bound RESERVE probe read timeout");
    writeln!(client, "RESERVE {bytes} {} {label}", std::process::id()).expect("send RESERVE probe");
    client.flush().expect("flush RESERVE probe");
    let mut reply = String::new();
    BufReader::new(client).read_line(&mut reply).expect("read RESERVE probe reply");
    reply.trim().to_string()
}

/// Pin the documented fail-closed contract on a host whose effective-memory
/// budget cannot be derived (see `host_budget_available`): the daemon still
/// binds and answers a closed IDENTITY naming the exact packaged bytes, STATUS
/// truthfully reports the underivable budget as 0 rather than guessing, and a
/// nonzero RESERVE is refused promptly with DEGRADED — never GRANTED, never a
/// hang. Before this pin, that contract was untested on exactly the class of
/// host where it is load-bearing.
fn assert_zero_budget_fail_closed_contract(path: &Path) {
    let identity = identity_at(path).expect("zero-budget daemon still serves closed IDENTITY");
    assert_eq!(identity.version, IDENTITY_VERSION);
    assert_eq!(identity.protocol, STATUS_VERSION);
    assert_eq!(identity.executable_sha256, executable_sha256(Path::new(trustd())));
    let status = status_at(path).expect("zero-budget daemon still serves valid STATUS");
    assert_eq!(
        status.budget_bytes, 0,
        "an underivable effective-memory budget must surface as 0, never a guess"
    );
    assert_eq!(
        reserve_reply_at(path, 1, "zero-budget-probe"),
        "DEGRADED",
        "a nonzero RESERVE against a zero budget must be refused, not granted or parked"
    );
}

#[test]
fn informational_flags_exit_without_creating_a_socket() {
    let fixture = SocketFixture::new();

    for flag in ["--version", "-V"] {
        let output = Command::new(trustd())
            .arg(flag)
            .env(SOCK_ENV, &fixture.path)
            .output()
            .expect("run trustd version command");
        assert!(output.status.success(), "{flag} failed: {output:?}");
        let stdout = String::from_utf8(output.stdout).expect("version output is UTF-8");
        let release = option_env!("CFG_RELEASE").unwrap_or(env!("CARGO_PKG_VERSION"));
        let expected_first_line = format!("trustd {release}");
        assert_eq!(stdout.lines().next(), Some(expected_first_line.as_str()));
        assert!(stdout.contains("trust.identity=trustd\n"));
        assert!(stdout.contains(&format!("trust.protocol={STATUS_VERSION}\n")));
        let commit =
            option_env!("CFG_VER_HASH").filter(|value| !value.is_empty()).unwrap_or("unbound");
        assert!(stdout.contains(&format!("commit-hash: {commit}\n")));
        assert!(!fixture.path.exists(), "{flag} must not start a daemon");
    }

    let help = Command::new(trustd())
        .arg("--help")
        .env(SOCK_ENV, &fixture.path)
        .output()
        .expect("run trustd help command");
    assert!(help.status.success(), "--help failed: {help:?}");
    assert!(String::from_utf8(help.stdout).expect("help is UTF-8").contains("Usage: trustd"));
    assert!(!fixture.path.exists(), "--help must not start a daemon");
}

#[test]
fn malformed_arguments_exit_two_without_creating_a_socket() {
    let fixture = SocketFixture::new();
    for args in [
        vec!["--unknown"],
        vec!["--socket"],
        vec!["--socket="],
        vec!["--socket", "--version"],
        vec!["--version", "--help"],
    ] {
        let output = Command::new(trustd())
            .args(&args)
            .env(SOCK_ENV, &fixture.path)
            .output()
            .expect("run malformed trustd command");
        assert_eq!(output.status.code(), Some(2), "wrong exit for {args:?}: {output:?}");
        assert!(!fixture.path.exists(), "malformed args must not start a daemon");
    }
}

#[test]
#[cfg(not(target_vendor = "apple"))]
fn non_utf8_socket_path_starts_and_serves() {
    let fixture = SocketFixture::with_file_name(OsString::from_vec(b"daemon-\xff.sock".to_vec()));
    let daemon = spawn_trustd(&fixture.path);
    let daemon = ChildGuard(daemon);
    assert!(
        wait_for_status(&fixture.path, Duration::from_secs(3)),
        "trustd must preserve non-UTF-8 Unix path bytes"
    );
    drop(daemon);
}

// Darwin's VFS rejects an invalid-UTF-8 AF_UNIX pathname with EILSEQ before
// trustd can bind it. The parser unit test still proves byte preservation; this
// process test covers the strongest pathname Darwin itself supports.
#[test]
#[cfg(target_vendor = "apple")]
fn multibyte_utf8_socket_path_starts_and_serves() {
    let fixture = SocketFixture::with_file_name(OsString::from("daemon-💌.sock"));
    let daemon = spawn_trustd(&fixture.path);
    let daemon = ChildGuard(daemon);
    assert!(
        wait_for_status(&fixture.path, Duration::from_secs(3)),
        "trustd must preserve multibyte Unix path bytes"
    );
    drop(daemon);
}

#[test]
fn concurrent_process_start_keeps_one_status_authority_and_socket_inode() {
    let fixture = SocketFixture::new();
    let first = spawn_trustd(&fixture.path);
    let mut first = ChildGuard(first);
    assert!(
        wait_for_status(&fixture.path, Duration::from_secs(3)),
        "first trustd never published a valid STATUS"
    );

    let before = std::fs::symlink_metadata(&fixture.path).expect("first socket metadata");
    assert_eq!(before.permissions().mode() & 0o777, 0o600);
    let identity = (before.dev(), before.ino());

    let mut second = spawn_trustd(&fixture.path);
    let second_status = wait_for_exit(&mut second, Duration::from_secs(3));
    if second_status.is_none() {
        let _ = second.kill();
        let _ = second.wait();
    }
    assert_eq!(
        second_status.and_then(|status| status.code()),
        Some(1),
        "competing trustd must fail promptly"
    );

    let status = status_at(&fixture.path).expect("original STATUS authority remains reachable");
    assert_eq!(status.version, STATUS_VERSION);
    let after = std::fs::symlink_metadata(&fixture.path).expect("surviving socket metadata");
    assert_eq!((after.dev(), after.ino()), identity, "competitor replaced the live socket");
    assert!(first.0.try_wait().expect("poll first trustd").is_none());
}

#[test]
fn runtime_identity_is_the_exact_executable_and_wrong_binary_is_rejected() {
    let fixture = SocketFixture::new();
    let package = PackagedLauncher::new(&fixture.path);
    let executable = package.trustd();
    let daemon = spawn_trustd_executable(&fixture.path, &executable);
    let mut daemon = ChildGuard(daemon);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    let identity = identity_at(&fixture.path).expect("closed IDENTITY response");
    assert_eq!(identity.version, IDENTITY_VERSION);
    assert_eq!(identity.protocol, STATUS_VERSION);
    assert_eq!(identity.executable_sha256, executable_sha256(Path::new(trustd())));
    if host_budget_available() {
        assert!(
            daemon_matches_executable(&fixture.path, &executable),
            "exact packaged executable is accepted"
        );
    } else {
        // Documented fail-closed trade, not a skipped check: the visible cgroup
        // walk (`linux_visible_cgroup_limit_with`, memory_jobserver.rs:1715-1723)
        // refuses to treat a missing root `memory.max` as an unbounded-root
        // proof, because a cgroup namespace can masquerade a constrained
        // descendant as `/`. The IDENTITY asserts above already proved the
        // byte-identity half passes exactly on this daemon; adoption must still
        // be refused, because a daemon whose admission ceiling is 0 can never
        // become a memory-budget authority (`daemon_budget_is_acceptable`
        // requires a nonzero ceiling on both sides).
        assert_zero_budget_fail_closed_contract(&fixture.path);
        assert!(
            !daemon_matches_executable(&fixture.path, &executable),
            "a zero-budget daemon must not be adopted even with exact byte identity"
        );
    }
    assert!(
        !daemon_matches_executable(&fixture.path, &package.launcher()),
        "a different executable cannot reuse a STATUS-compatible daemon"
    );
    assert!(daemon.0.try_wait().expect("poll daemon").is_none());
}

#[test]
fn exact_daemon_completes_the_live_reserve_release_smoke() {
    let fixture = SocketFixture::new();
    let package = PackagedLauncher::new(&fixture.path);
    let executable = package.trustd();
    let daemon = spawn_trustd_executable(&fixture.path, &executable);
    let daemon = ChildGuard(daemon);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    if !host_budget_available() {
        // Documented fail-closed trade, not a skipped test: on a host where the
        // visible cgroup walk (`linux_visible_cgroup_limit_with`,
        // memory_jobserver.rs:1715-1723) cannot authenticate the hierarchy root
        // — a cgroup namespace can masquerade a constrained descendant as `/` —
        // the budget is deliberately 0 and the grant protocol cannot complete.
        // Pin the contract that replaces it: exact IDENTITY still served,
        // STATUS budget 0, nonzero RESERVE promptly DEGRADED, and the public
        // smoke entry point refuses rather than fabricating a grant.
        assert_zero_budget_fail_closed_contract(&fixture.path);
        assert!(
            exercise_daemon_at(&fixture.path, &executable, "product-proof-live-smoke").is_err(),
            "the live smoke must refuse, never fabricate a grant, under a zero budget"
        );
        return;
    }

    let smoke = exercise_daemon_at(&fixture.path, &executable, "product-proof-live-smoke")
        .expect("exact trustd must complete its public live protocol exercise");
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        assert!(
            !daemon_matches_executable_from_pid(&fixture.path, &executable, std::process::id(),),
            "the test client's PID must not impersonate the spawned daemon"
        );
        assert!(
            daemon_matches_executable_from_pid(&fixture.path, &executable, daemon.0.id()),
            "readiness must bind the actual spawned daemon PID"
        );
        let peer_smoke = exercise_daemon_at_from_pid(
            &fixture.path,
            &executable,
            "product-proof-live-smoke",
            daemon.0.id(),
        )
        .expect("spawned trustd must complete the peer-bound live protocol exercise");
        assert_eq!(peer_smoke.reservation_bytes, 1);
        assert!(peer_smoke.status_released.active.is_empty());
    }
    assert_eq!(smoke.identity.version, IDENTITY_VERSION);
    assert_eq!(smoke.identity.protocol, STATUS_VERSION);
    assert_eq!(smoke.reservation_bytes, 1);
    assert_eq!(smoke.reservation_label, "product-proof-live-smoke");
    assert_eq!(smoke.status_reserved.active.len(), 1);
    assert_eq!(smoke.status_reserved.active[0].token, smoke.reservation_token);
    assert_eq!(smoke.status_reserved.active[0].pid, smoke.reservation_pid);
    assert!(smoke.status_released.active.is_empty());
    assert_eq!(smoke.status_released.reserved_bytes, 0);
}

#[test]
fn cargo_clean_style_unlink_cannot_create_a_second_authority() {
    let fixture = SocketFixture::new();
    let first = spawn_trustd(&fixture.path);
    let mut first = ChildGuard(first);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    std::fs::write(fixture.lock_path(), b"obsolete lock").expect("create obsolete target lock");
    std::fs::remove_file(&fixture.path).expect("remove published socket pathname");
    std::fs::remove_file(fixture.lock_path()).expect("remove obsolete target lock");

    let mut second = spawn_trustd(&fixture.path);
    let second_status = wait_for_exit(&mut second, Duration::from_secs(3));
    if second_status.is_none() {
        let _ = second.kill();
        let _ = second.wait();
    }
    assert_eq!(
        second_status.and_then(|status| status.code()),
        Some(1),
        "external lifetime lock must survive target cleanup"
    );
    assert!(first.0.try_wait().expect("poll first authority").is_none());

    first.0.kill().expect("stop first authority");
    first.0.wait().expect("reap first authority");
    recover_after_confirmed_quiescence(&fixture.path);
    let replacement = spawn_trustd(&fixture.path);
    let replacement = ChildGuard(replacement);
    assert!(
        wait_for_status(&fixture.path, Duration::from_secs(3)),
        "a new owner starts after the old kernel lock is released"
    );
    drop(replacement);
}

#[test]
fn killed_daemon_with_live_grant_refuses_restart_until_explicit_recovery() {
    let fixture = SocketFixture::new();
    let mut first = spawn_trustd(&fixture.path);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    let mut client = UnixStream::connect(&fixture.path).expect("connect reservation owner");
    client.set_read_timeout(Some(Duration::from_secs(2))).expect("bound reservation read timeout");
    writeln!(client, "RESERVE 1 {} crash-fixture", std::process::id()).expect("request live grant");
    client.flush().expect("flush live grant request");
    let mut reply = String::new();
    BufReader::new(client.try_clone().expect("clone reservation stream"))
        .read_line(&mut reply)
        .expect("read live grant reply");
    let mut solver = None;
    if host_budget_available() {
        assert!(reply.starts_with("GRANTED "), "unexpected grant reply: {reply:?}");

        // Model an admitted solver and any descendants retaining the owning
        // stream. F_DUPFD intentionally creates a descriptor without FD_CLOEXEC.
        let owner_fd = client.as_raw_fd();
        let mut solver_command = Command::new("/bin/sleep");
        solver_command.arg("30").stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
        unsafe {
            solver_command.pre_exec(move || {
                if libc::fcntl(owner_fd, libc::F_DUPFD, 3) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        solver = Some(ChildGuard(solver_command.spawn().expect("spawn admitted solver fixture")));
    } else {
        // Documented fail-closed trade, not a skipped test: the visible cgroup
        // walk (`linux_visible_cgroup_limit_with`, memory_jobserver.rs:1715-1723)
        // refuses to treat a missing root `memory.max` as an unbounded-root
        // proof, so the budget is 0 and no live grant can exist to survive the
        // crash. Pin the grant half's fail-closed contract instead. The restart
        // refusal below stays asserted UNCONDITIONALLY: the DIRTY crash epoch is
        // held for the daemon's complete lifetime (`serve`'s durable-epoch
        // protocol), so refusing automatic restart after SIGKILL — and requiring
        // the explicit operator recovery — does not depend on a grant.
        assert_eq!(
            reply.trim(),
            "DEGRADED",
            "a zero-budget daemon must refuse the live grant, not park or grant it"
        );
    }
    drop(client);

    first.kill().expect("kill first daemon");
    first.wait().expect("reap first daemon");
    assert!(fixture.path.exists(), "process exit leaves the socket entry stale");

    let mut second = Command::new(trustd())
        .arg("--socket")
        .arg(&fixture.path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("attempt automatic restart");
    let second_status = wait_for_exit(&mut second, Duration::from_secs(3));
    if second_status.is_none() {
        let _ = second.kill();
        let _ = second.wait();
    }
    let mut stderr = String::new();
    if let Some(mut pipe) = second.stderr.take() {
        pipe.read_to_string(&mut stderr).expect("read restart refusal");
    }
    assert_eq!(second_status.and_then(|status| status.code()), Some(1));
    assert!(
        stderr.contains("automatic restart is refused"),
        "restart diagnostic must explain the fail-closed epoch: {stderr}"
    );

    if let Some(solver) = solver.as_mut() {
        solver.0.kill().expect("quiesce prior solver fixture");
        solver.0.wait().expect("reap prior solver fixture");
    }
    recover_after_confirmed_quiescence(&fixture.path);

    let third = spawn_trustd(&fixture.path);
    let _third = ChildGuard(third);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));
    assert!(identity_at(&fixture.path).is_some(), "recovered restart serves IDENTITY");
}

/// A private directory under the short `/tmp` namespace holding a copy of the
/// built `trustd` beside a copy of THIS test executable, i.e. the toolchain
/// packaging `resolve_trustd` requires (`trustd` is the sibling of the running
/// executable). The copy of the test binary is the launcher: re-executed with
/// `--exact packaged_launcher_helper --ignored`, it calls the real
/// `ensure_daemon` exactly as `targo` does.
struct PackagedLauncher {
    root: PathBuf,
}

/// Presence of this file beside the executable is what turns the ignored
/// helper test into a launcher; it holds the socket path to ensure. A file
/// rather than an environment variable keeps the helper inert in every normal
/// test run, including `--ignored` runs from the build directory.
const LAUNCHER_SOCKET_FILE: &str = "launcher-socket";
const LAUNCHER_READY: &str = "trustd-launcher: ensure_daemon returned ready";

impl PackagedLauncher {
    fn new(socket: &Path) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let temp_root = std::fs::canonicalize("/tmp").expect("canonical system temporary root");
        for _ in 0..128 {
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = temp_root.join(format!("tp-{}-{sequence}", std::process::id()));
            let mut builder = std::fs::DirBuilder::new();
            builder.mode(0o700);
            match builder.create(&root) {
                Ok(()) => {
                    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))
                        .expect("make package fixture directory private");
                    let package = Self { root };
                    copy_private_executable(Path::new(trustd()), &package.trustd());
                    copy_private_executable(
                        &std::env::current_exe().expect("test executable path"),
                        &package.launcher(),
                    );
                    // Each copy is a new file to the first-run check: pay it
                    // now, before the socket file below can make the launcher
                    // act, and before any test starts a clock on either copy.
                    run_once_before_any_deadline(&package.trustd(), "--help");
                    run_once_before_any_deadline(&package.launcher(), "--list");
                    std::fs::write(
                        package.root.join(LAUNCHER_SOCKET_FILE),
                        socket.as_os_str().as_bytes(),
                    )
                    .expect("record launcher socket path");
                    return package;
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create package fixture directory: {error}"),
            }
        }
        panic!("could not allocate a unique package fixture directory")
    }

    fn trustd(&self) -> PathBuf {
        self.root.join("trustd")
    }

    fn launcher(&self) -> PathBuf {
        self.root.join("trustd-launcher")
    }
}

impl Drop for PackagedLauncher {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(self.trustd());
        let _ = std::fs::remove_file(self.launcher());
        let _ = std::fs::remove_file(self.root.join(LAUNCHER_SOCKET_FILE));
        let _ = std::fs::remove_dir(&self.root);
    }
}

/// Unlinks the endpoint on unwind so a daemon that outlived a failed assertion
/// takes its endpoint-lost CLEAN exit within one refresh tick instead of
/// lingering until its idle timeout.
struct UnlinkEndpointOnDrop<'a>(&'a Path);

impl Drop for UnlinkEndpointOnDrop<'_> {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(self.0);
    }
}

/// Launcher half of `ensure_daemon_survives_its_launchers_process_group_being_killed`.
/// Inert unless it runs from a `PackagedLauncher` directory.
#[test]
#[ignore = "process helper: acts only when re-executed from a PackagedLauncher directory"]
fn packaged_launcher_helper() {
    let executable = std::env::current_exe().expect("launcher executable path");
    let Some(package) = executable.parent() else {
        return;
    };
    let Ok(socket) = std::fs::read(package.join(LAUNCHER_SOCKET_FILE)) else {
        return;
    };
    let socket = PathBuf::from(std::ffi::OsStr::from_bytes(&socket));
    // Held, as targo holds it, until the group kill ends this process.
    let _lease = ensure_daemon(&socket)
        .unwrap_or_else(|error| panic!("packaged launcher could not ensure trustd: {error}"));
    let mut stdout = std::io::stdout();
    writeln!(stdout, "{LAUNCHER_READY}").expect("announce launcher readiness");
    stdout.flush().expect("flush launcher readiness");
    // Stay alive like a real launcher (a targo build) until the test kills this
    // launcher's whole process group. Bounded so a broken test cannot leak it.
    thread::sleep(Duration::from_secs(120));
}

/// Regression for the 2026-09-22 production incident: a `timeout 150 ... targo
/// trust check` probe expired, GNU timeout signalled its WHOLE process group,
/// and the trustd that probe's `ensure_daemon` had spawned died with it, never
/// recording CLEAN, so every later verified gate on the host refused to start.
///
/// Reproduce it end to end with the real client and real packaging: a launcher
/// in its own process group calls `ensure_daemon`, the test kills that group
/// (as timeout, Ctrl-C, or a CI teardown does), and the daemon must survive,
/// keep serving, and — with its launcher's stderr pipe now reader-less — still
/// take a clean shutdown path that records CLEAN.
#[test]
fn ensure_daemon_survives_its_launchers_process_group_being_killed() {
    let fixture = SocketFixture::new();
    let package = PackagedLauncher::new(&fixture.path);

    let mut launcher_command = Command::new(package.launcher());
    launcher_command
        .args(["--exact", "packaged_launcher_helper", "--ignored", "--nocapture"])
        .args(["--test-threads=1", "-q"])
        .env_remove(DISABLE_ENV)
        .env_remove(SOCK_ENV)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        // The launcher leads a process group this test owns, exactly as GNU
        // timeout makes its child one. Only this group is ever signalled.
        .process_group(0);
    let mut launcher = ChildGuard(launcher_command.spawn().expect("start packaged launcher"));
    let launcher_group = libc::pid_t::try_from(launcher.0.id()).expect("launcher pid fits pid_t");
    let _unlink_endpoint = UnlinkEndpointOnDrop(&fixture.path);

    let stdout = launcher.0.stdout.take().expect("piped launcher stdout");
    let (ready_tx, ready_rx) = mpsc::channel();
    thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            let Ok(line) = line else { return };
            if line.trim() == LAUNCHER_READY {
                let _ = ready_tx.send(());
            }
        }
    });
    if ready_rx.recv_timeout(Duration::from_secs(30)).is_err() {
        let status = launcher.0.try_wait().expect("poll launcher");
        panic!("launcher never reported ensure_daemon readiness (launcher status: {status:?})");
    }
    let identity = identity_at(&fixture.path).expect("ensure_daemon left a serving daemon");
    assert_eq!(identity.executable_sha256, executable_sha256(&package.trustd()));

    // Kill the launcher's whole process group, as `timeout` did on expiry.
    assert_eq!(
        unsafe { libc::killpg(launcher_group, libc::SIGTERM) },
        0,
        "signal the launcher's own process group: {}",
        std::io::Error::last_os_error()
    );
    let launcher_status = wait_for_exit(&mut launcher.0, Duration::from_secs(10))
        .expect("launcher group terminated by SIGTERM");
    assert_eq!(launcher_status.signal(), Some(libc::SIGTERM), "{launcher_status:?}");
    thread::sleep(Duration::from_millis(250));

    assert!(
        ping_at(&fixture.path),
        "trustd died with its launcher's process group: the machine-wide daemon must not \
         share the group of whichever build happened to start it"
    );
    let survivor = identity_at(&fixture.path).expect("surviving daemon still serves IDENTITY");
    assert_eq!(survivor, identity, "the survivor is the daemon the launcher started");
    status_at(&fixture.path).expect("surviving daemon still serves a valid STATUS");

    // The launcher owned the read end of trustd's stderr pipe, so every later
    // stderr write now fails with EPIPE. Unlinking the endpoint forces the
    // daemon's post-readiness diagnostic (the endpoint-lost line) and then its
    // quiescent shutdown, which must still record CLEAN rather than panic.
    std::fs::remove_file(&fixture.path).expect("unlink the endpoint to force a clean shutdown");
    let shutdown_started = Instant::now();
    let epoch_was_dirty = loop {
        match recover_dirty_epoch_after_quiescence(&fixture.path) {
            // The stable lock is free only once the daemon has exited.
            Ok(was_dirty) => break was_dirty,
            Err(error) => {
                assert!(
                    shutdown_started.elapsed() < Duration::from_secs(30),
                    "detached trustd never released its ownership lock after losing its \
                     endpoint: {error}"
                );
                thread::sleep(Duration::from_millis(50));
            }
        }
    };
    assert!(
        !epoch_was_dirty,
        "detached trustd exited without recording CLEAN once its launcher's stderr reader \
         was gone; a failed diagnostic write must never cost the host its crash epoch"
    );
}
