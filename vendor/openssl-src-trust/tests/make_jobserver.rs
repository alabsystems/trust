// Trust: actual stripping std and real GNU make, without a launcher or shim.
#![cfg(unix)]
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use jobserver_utils::Jobserver;

const CHILD: &str = env!("CARGO_BIN_EXE_openssl-jobserver-test-child");
const TIMEOUT: Duration = Duration::from_secs(15);

struct Running(Child);
impl Running {
    fn wait(&mut self) -> ExitStatus {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            if let Some(status) = self.0.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < deadline, "owned native fixture timed out");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            // SAFETY: only this test-created private process group is killed.
            unsafe { libc::kill(-(self.0.id() as i32), libc::SIGKILL) };
            let _ = self.0.wait();
        }
    }
}

fn child(mode: &str) -> Command {
    let mut command = Command::new(CHILD);
    command
        .env_clear()
        .env("OPENSSL_TEST_MODE", mode)
        .process_group(0);
    command
}

#[test]
fn owned_make_pair_survives_stripping_spawn_and_drops_unrelated_canary() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("canary");
    fs::write(&path, b"unrelated regular file").unwrap();
    let canary = File::open(path).unwrap();
    let fd = canary.as_raw_fd();
    let metadata = canary.metadata().unwrap();
    let server = Jobserver::new(2).unwrap();
    let mut command = child("relay");
    command.env(
        "OPENSSL_TEST_CANARY",
        format!("{fd},{},{}", metadata.dev(), metadata.ino()),
    );
    server.configure_make(&mut command);
    // SAFETY: deliberately pass one canary into the first hop; the ordinary
    // second spawn must strip it while preserving only explicitly owned FDs.
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut running = Running(command.spawn().unwrap());
    assert!(running.wait().success());
    assert_eq!(
        server.client().available().unwrap(),
        2,
        "probe leaked a token"
    );
}

#[test]
fn malformed_closed_and_regular_file_authority_refuse_without_private_budget() {
    for flags in ["--jobserver-auth=bad", "--jobserver-auth=900000,900001"] {
        let mut command = child("invalid");
        command.env("CARGO_MAKEFLAGS", flags);
        assert!(
            Running(command.spawn().unwrap()).wait().success(),
            "{flags}"
        );
    }
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("regular");
    fs::write(&path, b"not a pipe").unwrap();
    let file = File::open(path).unwrap();
    let fd = file.as_raw_fd();
    let mut command = child("invalid");
    command.env("CARGO_MAKEFLAGS", format!("--jobserver-auth={fd},{fd}"));
    // SAFETY: pass a known regular file to exercise the checked import guard.
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    assert!(Running(command.spawn().unwrap()).wait().success());
    for flags in [None, Some("--jobserver-auth=-2,-2"), Some("--silent")] {
        let mut command = child("absent");
        if let Some(flags) = flags {
            command.env("CARGO_MAKEFLAGS", flags);
        }
        assert!(Running(command.spawn().unwrap()).wait().success());
    }
}

// The GNU make on PATH, as (major, minor).
fn gnu_make_version() -> (u32, u32) {
    let version = Command::new("make").arg("--version").output().unwrap();
    let version = String::from_utf8_lossy(&version.stdout).into_owned();
    let number = version
        .lines()
        .next()
        .and_then(|line| line.strip_prefix("GNU Make "))
        .unwrap_or_else(|| panic!("not GNU make: {version}"));
    let mut parts = number.split('.').map(|part| part.parse().unwrap());
    (parts.next().unwrap(), parts.next().unwrap_or(0))
}

// Trust (BOOTSTRAP-JOBSERVER-PROBE-1): a named pool with two tokens, in a
// private directory the caller keeps alive.
fn named_server(directory: &std::path::Path) -> Jobserver {
    let path = directory.join("jobserver.fifo");
    let name = std::ffi::CString::new(path.to_str().unwrap()).unwrap();
    // SAFETY: a new FIFO in this test's private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let server = Jobserver::from_fifo(&path).unwrap();
    server.client().release_raw().unwrap();
    server.client().release_raw().unwrap();
    server
}

fn recursive_make(fail: bool) {
    recursive_make_with(fail, false);
}

// GNU make before 4.2 reads its jobserver pipe in blocking mode and stops on
// EAGAIN ("read jobs pipe"). This fixture's named pool comes from
// `Jobserver::from_fifo`, whose descriptions stay nonblocking; a build
// script's comes from `Jobserver::from_env`, which makes them blocking. Before
// 4.2 the named-pool runs would measure this fixture, not the product.
const NAMED_POOL_MAKE: (u32, u32) = (4, 2);

fn recursive_make_with(fail: bool, named: bool) {
    let version = gnu_make_version();
    if named && version < NAMED_POOL_MAKE {
        eprintln!("not run: GNU make {version:?} is older than {NAMED_POOL_MAKE:?}");
        return;
    }
    let directory = tempfile::tempdir().unwrap();
    let makefile = directory.path().join("Makefile");
    fs::write(
        &makefile,
        concat!(
            ".PHONY: all a b inner one two three\n",
            "all: a b\n",
            "a b:\n\t+$(MAKE) --no-print-directory -f $(firstword $(MAKEFILE_LIST)) inner\n",
            "inner: one two three\n",
            "one two three:\n\t+\"$(PROBE)\"\n",
        ),
    )
    .unwrap();
    let socket = directory.path().join("control.sock");
    let listener = UnixListener::bind(&socket).unwrap();
    listener.set_nonblocking(true).unwrap();
    let server = if named {
        named_server(directory.path())
    } else {
        Jobserver::new(2).unwrap()
    };
    // One token stays with the parent. Make may run only two leaves: its
    // implicit slot and the single remaining shared token.
    let held = server.client().acquire().unwrap();
    let stderr = File::create(directory.path().join("stderr")).unwrap();
    let mut command = Command::new("make");
    command
        .args(["--no-print-directory", "-f"])
        .arg(&makefile)
        .arg("all")
        .env("PROBE", CHILD)
        .env("OPENSSL_TEST_MODE", "leaf")
        .env("OPENSSL_TEST_SOCKET", &socket)
        .env_remove("OPENSSL_TEST_FAIL")
        .stdout(Stdio::null())
        .stderr(stderr)
        .process_group(0);
    if fail {
        command.env("OPENSSL_TEST_FAIL", "1");
    }
    if named {
        server.configure_gnu_make(&mut command).unwrap();
    } else {
        server.configure_make(&mut command);
    }
    let mut running = Running(command.spawn().unwrap());
    let deadline = Instant::now() + TIMEOUT;
    let mut active: Vec<BufReader<UnixStream>> = Vec::new();
    let mut count = 0;
    let mut first_wave = None;
    let status = loop {
        while let Ok((stream, _)) = listener.accept() {
            stream.set_nonblocking(false).unwrap();
            stream.set_read_timeout(Some(TIMEOUT)).unwrap();
            let mut stream = BufReader::new(stream);
            let mut ready = String::new();
            stream.read_line(&mut ready).unwrap();
            assert_eq!(ready, "ready\n");
            active.push(stream);
            count += 1;
            assert!(
                active.len() <= 2,
                "recursive make exceeded the shared budget"
            );
            if active.len() == 2 && first_wave.is_none() {
                first_wave = Some(Instant::now());
            }
        }
        if let Some(started) = first_wave {
            if started.elapsed() >= Duration::from_millis(200) {
                for mut stream in active.drain(..) {
                    writeln!(stream.get_mut(), "finish").unwrap();
                }
            }
        }
        if let Some(status) = running.0.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "recursive make stalled with {count} leaves"
        );
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(
        first_wave.is_some(),
        "make serialized despite an available shared token"
    );
    assert_eq!(status.success(), !fail);
    if !fail {
        assert_eq!(count, 6);
    }
    let errors = fs::read_to_string(directory.path().join("stderr")).unwrap();
    assert!(!errors.contains("jobserver unavailable"), "{errors}");
    assert_eq!(
        server.client().available().unwrap(),
        1,
        "make leaked/minted a token"
    );
    drop(held);
    assert_eq!(server.client().available().unwrap(), 2);
}

#[test]
fn real_recursive_make_shares_tokens_and_restores_them_after_success() {
    recursive_make(false);
}

#[test]
fn real_recursive_make_restores_tokens_after_a_failed_recipe() {
    recursive_make(true);
}

// Trust (BOOTSTRAP-JOBSERVER-PROBE-1): a named FIFO pool, as Bootstrap gives
// the seed Cargo, reaches real GNU make through `configure_gnu_make` and is
// shared and restored exactly as a numeric pipe is.
#[test]
fn real_recursive_make_shares_a_named_fifo_pool_and_restores_it() {
    recursive_make_with(false, true);
}

#[test]
fn real_recursive_make_restores_a_named_fifo_pool_after_a_failed_recipe() {
    recursive_make_with(true, true);
}

// Why make gets the numeric pair: the `fifo:` spelling that every other child
// gets stops GNU make before 4.4 before it runs anything. Make before 4.2
// reads it as `--jobserver-fds`, 4.2 and 4.3 as `--jobserver-auth`.
#[test]
fn the_fifo_spelling_stops_gnu_make_before_4_4() {
    let directory = tempfile::tempdir().unwrap();
    let makefile = directory.path().join("Makefile");
    fs::write(&makefile, "all:\n\t@true\n").unwrap();
    let server = named_server(directory.path());
    let run = |gnu: bool| {
        let mut command = Command::new("make");
        command
            .args(["--no-print-directory", "-f"])
            .arg(&makefile)
            .process_group(0);
        if gnu {
            server.configure_gnu_make(&mut command).unwrap();
        } else {
            server.configure_make(&mut command);
        }
        command.output().unwrap()
    };
    let spelled = run(false);
    let stderr = String::from_utf8_lossy(&spelled.stderr);
    let version = gnu_make_version();
    if version < (4, 4) {
        let option = if version < (4, 2) {
            "--jobserver-fds"
        } else {
            "--jobserver-auth"
        };
        assert_eq!(spelled.status.code(), Some(2), "{stderr}");
        assert!(
            stderr.contains(&format!("invalid {option} string")),
            "{version:?}: {stderr}"
        );
    } else {
        assert!(spelled.status.success(), "{stderr}");
    }
    let paired = run(true);
    assert!(
        paired.status.success(),
        "{}",
        String::from_utf8_lossy(&paired.stderr)
    );
    assert_eq!(server.client().available().unwrap(), 2);
}
