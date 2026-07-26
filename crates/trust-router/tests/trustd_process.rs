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
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_router::coordinator::{
    IDENTITY_VERSION, SOCK_ENV, STATUS_VERSION, daemon_matches_executable, exercise_daemon_at,
    identity_at, status_at,
};

fn trustd() -> &'static str {
    env!("CARGO_BIN_EXE_trustd")
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
        let runtime_socket = match trust_router::coordinator::host_socket_path() {
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
    Command::new(trustd())
        .arg("--socket")
        .arg(path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("start trustd")
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
    let daemon = spawn_trustd(&fixture.path);
    let mut daemon = ChildGuard(daemon);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    let identity = identity_at(&fixture.path).expect("closed IDENTITY response");
    assert_eq!(identity.version, IDENTITY_VERSION);
    assert_eq!(identity.protocol, STATUS_VERSION);
    assert_eq!(identity.executable_sha256, executable_sha256(Path::new(trustd())));
    assert!(
        daemon_matches_executable(&fixture.path, Path::new(trustd())),
        "exact packaged executable is accepted"
    );
    assert!(
        !daemon_matches_executable(
            &fixture.path,
            &std::env::current_exe().expect("test executable path")
        ),
        "a different executable cannot reuse a STATUS-compatible daemon"
    );
    assert!(daemon.0.try_wait().expect("poll daemon").is_none());
}

#[test]
fn exact_daemon_completes_the_live_reserve_release_smoke() {
    let fixture = SocketFixture::new();
    let daemon = spawn_trustd(&fixture.path);
    let _daemon = ChildGuard(daemon);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));

    let smoke = exercise_daemon_at(&fixture.path, Path::new(trustd()), "product-proof-live-smoke")
        .expect("exact trustd must complete its public live protocol exercise");
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
    assert!(reply.starts_with("GRANTED "), "unexpected grant reply: {reply:?}");

    // Model an admitted solver and any descendants retaining the owning stream.
    // F_DUPFD intentionally creates a descriptor without FD_CLOEXEC.
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
    let mut solver = ChildGuard(solver_command.spawn().expect("spawn admitted solver fixture"));
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

    solver.0.kill().expect("quiesce prior solver fixture");
    solver.0.wait().expect("reap prior solver fixture");
    recover_after_confirmed_quiescence(&fixture.path);

    let third = spawn_trustd(&fixture.path);
    let _third = ChildGuard(third);
    assert!(wait_for_status(&fixture.path, Duration::from_secs(3)));
    assert!(identity_at(&fixture.path).is_some(), "recovered restart serves IDENTITY");
}
