// Trust: actual frontend/child controls, with no compiler or Cargo substitute
// claiming evidence. The selected sibling is an owned process-test fixture.

use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt as _;
use std::path::PathBuf;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use jobserver_utils::{DESCENDANT_HANDOFF_ENV, Jobserver};

use super::{CARGO_TIPPY_BIN, lock_fixture_parent, unique_temp_dir, write_executable};

const ROLE: &str = "TIPPY_JOBSERVER_TEST_ROLE";
const SOCKET: &str = "TIPPY_JOBSERVER_TEST_SOCKET";
const TIMEOUT: Duration = Duration::from_secs(15);

struct Fixture {
    root: PathBuf,
    frontend: PathBuf,
    cargo: PathBuf,
}

impl Fixture {
    fn new(label: &str, branded: bool) -> Self {
        let root = unique_temp_dir(label);
        let bin = root.join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        let cargo = bin.join("targo");
        // Follow the maintained shim process-test pattern: shell exec retains
        // exactly what the production frontend explicitly handed its child.
        // The test executable probes raw descriptors rather than doing a late,
        // unsafe ambient jobserver import after libtest has opened files.
        write_executable(
            &cargo,
            concat!(
                "#!/bin/sh\nexec \"$TIPPY_JOBSERVER_TEST_EXE\" ",
                "--ignored --exact jobserver_boundary::child --nocapture --test-threads=1\n",
            )
            .as_bytes(),
        );
        let frontend = if branded {
            let frontend = bin.join("tippy");
            std::fs::hard_link(CARGO_TIPPY_BIN, &frontend).unwrap();
            write_executable(&bin.join("tippy-driver"), b"#!/bin/sh\nexit 70\n");
            write_executable(&bin.join("trustc"), b"#!/bin/sh\nexit 71\n");
            frontend
        } else {
            PathBuf::from(CARGO_TIPPY_BIN)
        };
        Self { root, frontend, cargo }
    }

    fn command(&self, role: &str) -> Command {
        let mut command = Command::new(&self.frontend);
        command
            .arg("--workspace")
            .env("CARGO", &self.cargo)
            .env(ROLE, role)
            .env("TIPPY_JOBSERVER_TEST_EXE", std::env::current_exe().unwrap())
            .env_remove("CARGO_MAKEFLAGS")
            .env_remove("MAKEFLAGS")
            .env_remove("MFLAGS")
            .env_remove(DESCENDANT_HANDOFF_ENV)
            .env_remove("TRUST_TIPPY_RUSTC_PRIVATE_HOST_DIR")
            .env_remove("TRUST_TIPPY_RUSTC_PRIVATE_TARGET_DIR")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .process_group(0);
        command
    }

    fn launch(&self, command: &mut Command) -> (Running, BufReader<UnixStream>) {
        // Keep socket paths short on Darwin and outside the authenticated bin
        // directory; creating a control channel is not a toolchain mutation.
        let socket_directory = tempfile::tempdir().unwrap();
        let socket = socket_directory.path().join("s");
        let listener = UnixListener::bind(&socket).unwrap();
        listener.set_nonblocking(true).unwrap();
        command.env(SOCKET, socket);
        let mut child = Running {
            child: command.spawn().unwrap(),
            _socket_directory: socket_directory,
        };
        let deadline = Instant::now() + TIMEOUT;
        let stream = loop {
            match listener.accept() {
                Ok((stream, _)) => break stream,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    assert!(
                        child.child.try_wait().unwrap().is_none(),
                        "frontend exited before the child connected"
                    );
                    assert!(Instant::now() < deadline, "frontend child did not connect");
                    std::thread::sleep(Duration::from_millis(10));
                },
                Err(error) => panic!("cannot accept frontend child: {error}"),
            }
        };
        stream.set_read_timeout(Some(TIMEOUT)).unwrap();
        stream.set_write_timeout(Some(TIMEOUT)).unwrap();
        (child, BufReader::new(stream))
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

struct Running {
    child: Child,
    _socket_directory: tempfile::TempDir,
}

impl Running {
    fn wait(&mut self) -> ExitStatus {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < deadline, "frontend did not finish its child wait");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            // SAFETY: only this fixture's spawn creates this process group.
            // Reap our own children on failure without touching other builds.
            unsafe { libc::kill(-(self.child.id() as i32), libc::SIGKILL) };
            let _ = self.child.wait();
        }
    }
}

fn line(stream: &mut BufReader<UnixStream>, expected: &str) {
    let mut actual = String::new();
    stream.read_line(&mut actual).unwrap();
    assert_eq!(actual.trim_end(), expected);
}

fn send(stream: &mut BufReader<UnixStream>, message: &str) {
    writeln!(stream.get_mut(), "{message}").unwrap();
}

fn duplicate(fd: i32) -> Option<File> {
    // SAFETY: dup inspects this number without assuming it is open or owned.
    let copy = unsafe { libc::dup(fd) };
    (copy >= 0).then(|| {
        // SAFETY: successful dup returned a fresh, exclusively owned handle.
        unsafe { File::from_raw_fd(copy) }
    })
}

#[test]
#[ignore = "subprocess role, invoked only by the frontend process controls"]
fn child() {
    let role = std::env::var(ROLE).expect("child role is set by a frontend process control");
    let stream = UnixStream::connect(std::env::var_os(SOCKET).unwrap()).unwrap();
    stream.set_read_timeout(Some(TIMEOUT)).unwrap();
    stream.set_write_timeout(Some(TIMEOUT)).unwrap();
    let mut control = BufReader::new(stream);
    if role == "none" {
        assert!(
            std::env::var_os("CARGO_MAKEFLAGS").is_none(),
            "frontend invented a scheduler"
        );
        send(&mut control, "NO_SERVER");
        line(&mut control, "FINISH");
        return;
    }
    assert!(matches!(role.as_str(), "shared" | "exit42"));

    let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
    let auth = flags
        .split_whitespace()
        .find_map(|flag| flag.strip_prefix("--jobserver-auth="))
        .unwrap();
    let (read, write) = auth.split_once(',').unwrap();
    let mut read = duplicate(read.parse().unwrap()).expect("advertised read fd was stripped");
    let mut write = duplicate(write.parse().unwrap()).expect("advertised write fd was stripped");
    let canary = std::env::var("TIPPY_JOBSERVER_TEST_CANARY").unwrap();
    let canary = canary.split(',').collect::<Vec<_>>();
    if let Some(file) = duplicate(canary[0].parse().unwrap()) {
        let actual = file.metadata().unwrap();
        assert_ne!(
            (actual.dev(), actual.ino()),
            (canary[1].parse().unwrap(), canary[2].parse().unwrap()),
            "frontend passed an unrelated descriptor"
        );
    }
    assert!(
        std::env::var_os(DESCENDANT_HANDOFF_ENV).is_none(),
        "renumbered child retained a stale endpoint binding"
    );
    send(&mut control, "READY");
    let mut token = [0];
    read.read_exact(&mut token).unwrap();
    send(&mut control, "ACQUIRED");
    line(&mut control, "RELEASE");
    write.write_all(&token).unwrap();
    send(&mut control, "RELEASED");
    line(&mut control, "FINISH");
    if role == "exit42" {
        std::process::exit(42);
    }
}

fn shared_tokens(branded: bool, child_exit: i32) {
    let _fixture_parent_guard = lock_fixture_parent();
    let fixture = Fixture::new("jobserver-shared", branded);
    let server = Jobserver::new(1).unwrap();
    let held = server.client().acquire().unwrap();
    let canary_path = fixture.root.join("unrelated-input");
    std::fs::write(&canary_path, b"not a scheduler or executable").unwrap();
    let canary = File::open(&canary_path).unwrap();
    let canary_metadata = canary.metadata().unwrap();
    let canary_fd = canary.as_raw_fd();
    let mut command = fixture.command(if child_exit == 42 { "exit42" } else { "shared" });
    command
        .env("MAKEFLAGS", "--jobserver-auth=999998,999998")
        .env("MFLAGS", "--jobserver-auth=999997,999997")
        .env(
            "TIPPY_JOBSERVER_TEST_CANARY",
            format!("{canary_fd},{},{}", canary_metadata.dev(), canary_metadata.ino()),
        );
    server.configure(&mut command);
    // A checked numeric pool never borrows authority from an ambient endpoint;
    // renumbering at the frontend must not re-advertise that unrelated binding.
    command.env(DESCENDANT_HANDOFF_ENV, "untrusted-do-not-forward");
    // SAFETY: pass the owned canary to the frontend only. Its final Cargo
    // spawn must explicitly preserve the scheduler while stripping this file.
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(canary_fd, libc::F_SETFD, 0) < 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let (mut child, mut control) = fixture.launch(&mut command);
    drop(command);
    line(&mut control, "READY");
    control
        .get_mut()
        .set_read_timeout(Some(Duration::from_millis(150)))
        .unwrap();
    let mut premature = String::new();
    let error = control
        .read_line(&mut premature)
        .expect_err("child acquired a private pool's token");
    assert!(matches!(
        error.kind(),
        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
    ));
    assert!(premature.is_empty());
    assert_eq!(server.client().available().unwrap(), 0);
    control.get_mut().set_read_timeout(Some(TIMEOUT)).unwrap();
    drop(held);
    line(&mut control, "ACQUIRED");
    assert_eq!(
        server.client().available().unwrap(),
        0,
        "child did not acquire the original pool's token"
    );
    assert!(
        child.child.try_wait().unwrap().is_none(),
        "frontend failed to retain the child wait"
    );
    send(&mut control, "RELEASE");
    line(&mut control, "RELEASED");
    assert_eq!(
        server.client().available().unwrap(),
        1,
        "original token was lost or duplicated"
    );
    send(&mut control, "FINISH");
    assert_eq!(child.wait().code(), Some(child_exit));
    assert_eq!(server.client().available().unwrap(), 1);
}

#[test]
fn branded_frontend_preserves_shared_tokens_and_strips_unrelated_fds() {
    shared_tokens(true, 0);
}

#[test]
fn development_frontend_preserves_shared_tokens_and_child_failure() {
    shared_tokens(false, 42);
}

#[test]
fn absent_advertisement_never_creates_a_pool() {
    let _fixture_parent_guard = lock_fixture_parent();
    for branded in [false, true] {
        let fixture = Fixture::new("jobserver-absent", branded);
        let (mut child, mut control) = fixture.launch(&mut fixture.command("none"));
        line(&mut control, "NO_SERVER");
        send(&mut control, "FINISH");
        assert!(child.wait().success());
    }
}

#[test]
fn invalid_advertisements_refuse_before_launching_the_authenticated_sibling() {
    let _fixture_parent_guard = lock_fixture_parent();
    for auth in ["bad", "999999,999999", "regular-file"] {
        let fixture = Fixture::new("jobserver-invalid", true);
        let marker = fixture.root.join("must-not-launch");
        write_executable(
            &fixture.cargo,
            b"#!/bin/sh\nprintf launched > \"$TIPPY_JOBSERVER_TEST_MARKER\"\nexit 42\n",
        );
        let file = File::open(&fixture.cargo).unwrap();
        let fd = file.as_raw_fd();
        let auth = if auth == "regular-file" {
            format!("{fd},{fd}")
        } else {
            auth.to_owned()
        };
        let mut command = fixture.command("must-not-run");
        command
            .env("CARGO_MAKEFLAGS", format!("--jobserver-auth={auth}"))
            .env("TIPPY_JOBSERVER_TEST_MARKER", &marker)
            .stderr(Stdio::piped());
        // SAFETY: keep the real regular file open at this number so a pipe
        // type check, rather than merely EBADF, must refuse the third case.
        unsafe {
            command.pre_exec(move || {
                if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let output = command.output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success());
        assert!(stderr.contains("cannot inherit Tippy jobserver"), "{stderr}");
        assert!(!marker.exists(), "invalid scheduling authority launched Cargo");
    }
}

#[test]
fn help_and_version_keep_their_metadata_only_behavior_with_invalid_advertisements() {
    for query in ["--help", "--version"] {
        let output = Command::new(CARGO_TIPPY_BIN)
            .arg(query)
            .env("CARGO_MAKEFLAGS", "--jobserver-auth=999999,999999")
            .env_remove(DESCENDANT_HANDOFF_ENV)
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        assert!(!output.stdout.is_empty());
    }
}

#[test]
fn failed_spawn_returns_setup_failure_without_consuming_shared_tokens() {
    let _fixture_parent_guard = lock_fixture_parent();
    let fixture = Fixture::new("jobserver-spawn-failure", false);
    let server = Jobserver::new(1).unwrap();
    let mut command = fixture.command("must-not-run");
    command
        .env("CARGO", fixture.root.join("missing-cargo"))
        .stderr(Stdio::piped());
    server.configure(&mut command);
    let output = command.output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(stderr.contains("failed to launch"), "{stderr}");
    assert_eq!(server.client().available().unwrap(), 1);
}
