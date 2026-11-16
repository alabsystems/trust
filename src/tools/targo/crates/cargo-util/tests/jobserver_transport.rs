// Trust: imported scheduling authority must survive ProcessBuilder nesting.
#![cfg(unix)]

use std::env;
use std::ffi::CString;
use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use cargo_util::{Jobserver, ProcessBuilder};

const ROLE: &str = "TARGO_JOBSERVER_TRANSPORT_ROLE";
const SOCKET: &str = "TARGO_JOBSERVER_TRANSPORT_SOCKET";
const TIMEOUT: Duration = Duration::from_secs(15);

struct Running(Child);
impl Running {
    fn wait(&mut self) -> std::process::ExitStatus {
        self.wait_with_timeout(TIMEOUT)
    }

    fn wait_with_timeout(&mut self, timeout: Duration) -> std::process::ExitStatus {
        let deadline = Instant::now() + timeout;
        loop {
            if let Some(status) = self.0.try_wait().unwrap() {
                return status;
            }
            assert!(
                Instant::now() < deadline,
                "owned transport subprocess timed out"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            // SAFETY: this test created the child's private process group.
            unsafe { libc::kill(-(self.0.id() as i32), libc::SIGKILL) };
            let _ = self.0.wait();
        }
    }
}

fn receive(stream: &mut BufReader<UnixStream>) -> String {
    let mut line = String::new();
    stream.read_line(&mut line).unwrap();
    line.trim_end().to_owned()
}
fn send(stream: &mut BufReader<UnixStream>, message: &str) {
    writeln!(stream.get_mut(), "{message}").unwrap();
}
fn expect(stream: &mut BufReader<UnixStream>, message: &str) {
    assert_eq!(receive(stream), message);
}

fn exercise(mode: &str, absent: Option<&str>) {
    exercise_with_directory(mode, absent, tempfile::tempdir().unwrap());
}

fn exercise_with_directory(mode: &str, absent: Option<&str>, directory: tempfile::TempDir) {
    let socket = directory.path().join("control.sock");
    let listener = UnixListener::bind(&socket).unwrap();
    let canary_path = directory.path().join("canary");
    fs::write(&canary_path, "unrelated descriptor").unwrap();
    let canary = File::open(canary_path).unwrap();
    let canary_fd = canary.as_raw_fd();
    let identity = canary.metadata().unwrap();
    let fifo = if absent == Some("fifo") {
        let path = directory.path().join("scheduler.fifo");
        let name = CString::new(path.as_os_str().as_bytes()).unwrap();
        // SAFETY: a fresh path in this test's private temporary directory.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        // SAFETY: nonblocking reads only affect this test-owned FIFO handle.
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        assert!(flags >= 0);
        assert_eq!(
            unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) },
            0
        );
        Some((path, file))
    } else {
        None
    };
    let absent = absent.filter(|flags| *flags != "fifo");
    let mut server = fifo.is_none().then(|| Jobserver::new(1).unwrap());
    if mode == "unaware" {
        server
            .as_mut()
            .unwrap()
            .enable_descendant_handoff()
            .unwrap();
    }
    let held = server
        .as_ref()
        .map(|server| server.client().acquire().unwrap());
    let available = || {
        if let Some(server) = &server {
            server.client().available().unwrap()
        } else {
            // Darwin's FIONREAD reports zero for a readable named FIFO.
            // Inspect at most two tokens nonblockingly and put their exact
            // bytes back; every call occurs while the child awaits control.
            let mut file = &fifo.as_ref().unwrap().1;
            let mut bytes = [0; 2];
            match file.read(&mut bytes) {
                Ok(count) => {
                    file.write_all(&bytes[..count]).unwrap();
                    count
                }
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => 0,
                Err(error) => panic!("parent FIFO tokens: {error}"),
            }
        }
    };
    let mut command = Command::new(env::current_exe().unwrap());
    command
        .args(["--exact", "subprocess", "--nocapture", "--test-threads=1"])
        .env_clear()
        .env(ROLE, mode)
        .env(SOCKET, socket)
        .env(
            "TARGO_JOBSERVER_CANARY",
            format!("{canary_fd},{},{}", identity.dev(), identity.ino()),
        )
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .process_group(0);
    if let Some(flags) = absent {
        command.env("TARGO_JOBSERVER_ABSENT", "1");
        if !flags.is_empty() {
            command.env("CARGO_MAKEFLAGS", flags);
        }
    } else if let Some((path, _)) = &fifo {
        command.env(
            "CARGO_MAKEFLAGS",
            format!("--jobserver-auth=fifo:{}", path.display()),
        );
    } else {
        server.as_ref().unwrap().configure(&mut command);
    }
    // SAFETY: deliberately pass this one known canary into the relay. Spawn
    // must close it; ordinary exec replacement must retain its prior semantics.
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(canary_fd, libc::F_SETFD, 0) < 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut child = Running(command.spawn().unwrap());
    let relay_pid = child.0.id();
    listener.set_nonblocking(true).unwrap();
    let deadline = Instant::now() + TIMEOUT;
    let (stream, _) = loop {
        match listener.accept() {
            Ok(connection) => break connection,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(
                    child.0.try_wait().unwrap().is_none(),
                    "transport child exited before driver"
                );
                assert!(Instant::now() < deadline, "driver did not connect");
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(error) => panic!("driver accept: {error}"),
        }
    };
    // Darwin accepts inherit the listener's nonblocking flag.
    stream.set_nonblocking(false).unwrap();
    stream.set_read_timeout(Some(TIMEOUT)).unwrap();
    stream.set_write_timeout(Some(TIMEOUT)).unwrap();
    let mut control = BufReader::new(stream);
    let driver_pid = receive(&mut control).parse::<u32>().unwrap();
    if mode == "exec" {
        assert_eq!(driver_pid, relay_pid, "exec replacement added a supervisor");
    } else {
        assert_ne!(driver_pid, relay_pid);
    }
    if absent.is_some() {
        expect(&mut control, "ABSENT");
        send(&mut control, "FINISH");
        drop(held);
    } else {
        expect(&mut control, "EXHAUSTED");
        assert_eq!(available(), 0);
        drop(held);
        if let Some((_, file)) = &fifo {
            (&*file).write_all(b"+").unwrap();
        }
        send(&mut control, "GO");
        expect(&mut control, "ACQUIRED");
        assert_eq!(available(), 0, "driver used another server");
        send(&mut control, "DROP");
        expect(&mut control, "RELEASED");
        assert_eq!(available(), 1, "released token is not visible to parent");
    }
    assert_eq!(
        child.wait().code(),
        Some(if mode == "exec" { 23 } else { 0 })
    );
    assert_eq!(available(), 1, "token lost or duplicated");
    // SAFETY: reading the parent's still-owned descriptor flags.
    assert_ne!(
        unsafe { libc::fcntl(canary_fd, libc::F_GETFD) } & libc::FD_CLOEXEC,
        0
    );
}

#[test]
fn imported_server_survives_spawn_and_authenticated_environment_inspection() {
    exercise("spawn", None);
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn unaware_descendant_recovers_the_same_native_pool_without_changing_environment() {
    exercise("unaware", None);
}

// Trust: isolate TMPDIR changes in a child, retaining the real unaware relay,
// native recovery, canary-FD checks and same-pool exhaustion/release assertions.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn oversized_tmpdir_keeps_authenticated_descendant_handoff() {
    let directory = tempfile::tempdir_in("/tmp").unwrap();
    let long = directory.path().join("x".repeat(128));
    fs::create_dir(&long).unwrap();
    assert!(long.as_os_str().len() > 108);
    let mut command = Command::new(env::current_exe().unwrap());
    command
        .args(["--exact", "subprocess", "--nocapture", "--test-threads=1"])
        .env_clear()
        .env(ROLE, "long-tmpdir-parent")
        .env("TMPDIR", &long)
        .stdin(Stdio::null())
        .process_group(0);
    let mut child = Running(command.spawn().unwrap());
    // Leave the nested harness time to enforce its own deadline and reap its
    // separate child group before this outer guard could kill the harness.
    assert!(child.wait_with_timeout(TIMEOUT * 3).success());
    assert_eq!(fs::read_dir(&long).unwrap().count(), 0);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn reject_unaware_handoff(mode: &str) {
    let mut server = Jobserver::new(1).unwrap();
    server.enable_descendant_handoff().unwrap();
    let mut command = Command::new(env::current_exe().unwrap());
    command
        .args(["--exact", "subprocess", "--nocapture", "--test-threads=1"])
        .env_clear()
        .env(ROLE, mode)
        .stdin(Stdio::null())
        .process_group(0);
    server.configure(&mut command);
    let mut child = Running(command.spawn().unwrap());
    assert!(child.wait().success());
    assert_eq!(
        server.client().available().unwrap(),
        1,
        "refusal changed token count"
    );
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn unaware_descendant_refuses_a_forged_native_handoff() {
    reject_unaware_handoff("forged");
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn unaware_descendant_refuses_a_dead_native_handoff() {
    reject_unaware_handoff("dead");
}
#[test]
fn imported_server_survives_status_used_by_protected_children() {
    exercise("status", None);
}
#[test]
fn imported_server_survives_explicit_descriptor_stripping() {
    exercise("strip", None);
}
#[test]
fn imported_server_preserves_exec_pid_exit_status_and_descriptor_semantics() {
    exercise("exec", None);
}
#[test]
fn named_fifo_keeps_shared_tokens_through_nested_spawn() {
    exercise("spawn", Some("fifo"));
}
#[test]
fn absent_disabled_and_unrelated_makeflags_do_not_create_authority() {
    for mode in ["spawn", "status", "exec"] {
        for flags in ["", "--jobserver-auth=-2,-2", "unrelated-make-flags"] {
            exercise(mode, Some(flags));
        }
    }
}

#[test]
fn subprocess() {
    let Ok(role) = env::var(ROLE) else { return };
    if role == "long-tmpdir-parent" {
        // The control channel itself is deliberately short: only the production
        // endpoint must adapt to this child's actual oversized TMPDIR.
        assert!(env::temp_dir().as_os_str().len() > 108);
        exercise_with_directory("unaware", None, tempfile::tempdir_in("/tmp").unwrap());
        reject_unaware_handoff("forged");
        reject_unaware_handoff("dead");
        return;
    }
    if ["unaware", "forged", "dead"].contains(&role.as_str()) {
        // Deliberately unaware: use a plain Command without opting any pipe
        // descriptors into inheritance or creating a replacement pool.
        let mut command = Command::new(env::current_exe().unwrap());
        command
            .args(["--exact", "subprocess", "--nocapture", "--test-threads=1"])
            .env(
                ROLE,
                if role == "unaware" {
                    "driver"
                } else {
                    "reject-driver"
                },
            )
            .env("TARGO_JOBSERVER_MODE", &role)
            .env(
                "TARGO_JOBSERVER_EXPECTED_AUTH",
                env::var_os("CARGO_MAKEFLAGS").unwrap(),
            );
        if role != "unaware" {
            let advertisement = env::var(jobserver_utils::DESCENDANT_HANDOFF_ENV).unwrap();
            let mut fields: Vec<_> = advertisement.splitn(6, ':').map(str::to_owned).collect();
            assert_eq!(fields.len(), 6);
            if role == "forged" {
                let replacement = if fields[4].starts_with('0') { "1" } else { "0" };
                fields[4].replace_range(..1, replacement);
            } else {
                fields[5].push_str("-absent");
            }
            command.env(jobserver_utils::DESCENDANT_HANDOFF_ENV, fields.join(":"));
        }
        assert!(command.status().unwrap().success());
        return;
    }
    if role == "reject-driver" {
        let before = env::var_os("CARGO_MAKEFLAGS");
        // SAFETY: capture is this descendant's first descriptor operation.
        let error = unsafe { Jobserver::from_env_with_handoff() }.unwrap_err();
        assert!(
            error
                .to_string()
                .contains("cannot recover inherited jobserver"),
            "{error}"
        );
        assert_eq!(before, env::var_os("CARGO_MAKEFLAGS"));
        return;
    }
    if role != "driver" {
        // SAFETY: this relay has not closed/reassigned any inherited numbers;
        // capture before argument/file processing, as native Targo does.
        let inherited = unsafe { Jobserver::from_env() }.unwrap();
        let mut builder = ProcessBuilder::new(env::current_exe().unwrap());
        builder
            .args(&["--exact", "subprocess", "--nocapture", "--test-threads=1"])
            .env(ROLE, "driver")
            .env("TARGO_JOBSERVER_MODE", &role);
        if let Some(server) = &inherited {
            builder.inherit_jobserver(server);
        }
        let effective = builder
            .get_effective_envs()
            .unwrap()
            .get(std::ffi::OsStr::new("CARGO_MAKEFLAGS"))
            .cloned();
        let owned_pair = if env::var_os("TARGO_JOBSERVER_ABSENT").is_none() {
            let flags = effective.as_ref().unwrap().to_str().unwrap();
            flags
                .split_whitespace()
                .find_map(|arg| arg.strip_prefix("--jobserver-auth="))
                .filter(|auth| !auth.starts_with("fifo:"))
                .map(|auth| {
                    auth.split(',')
                        .map(|fd| fd.parse::<i32>().unwrap())
                        .collect::<Vec<_>>()
                })
        } else {
            None
        };
        let mut cloned = builder.clone();
        drop(builder);
        drop(inherited);
        let metadata_command = cloned.build_command();
        let configured = metadata_command
            .get_envs()
            .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten());
        if env::var_os("TARGO_JOBSERVER_ABSENT").is_none() {
            assert_eq!(
                configured,
                effective.as_deref(),
                "claim env differs from spawn env"
            );
            cloned.env("TARGO_JOBSERVER_EXPECTED_AUTH", effective.as_ref().unwrap());
        }
        drop(metadata_command);
        match role.as_str() {
            "exec" => {
                cloned.exec_replace().unwrap();
                unreachable!();
            }
            "status" => {
                assert!(cloned.status().unwrap().success());
                drop(cloned);
            }
            _ => {
                let mut command = cloned.build_command();
                if role == "strip" {
                    let auth = env::var("CARGO_MAKEFLAGS").unwrap();
                    let pair = auth
                        .split_whitespace()
                        .find_map(|arg| arg.strip_prefix("--jobserver-auth="))
                        .unwrap();
                    let mut originals = pair
                        .split(',')
                        .map(|n| n.parse::<i32>().unwrap())
                        .collect::<Vec<_>>();
                    originals.push(
                        env::var("TARGO_JOBSERVER_CANARY")
                            .unwrap()
                            .split(',')
                            .next()
                            .unwrap()
                            .parse()
                            .unwrap(),
                    );
                    // SAFETY: emulate SP-1 for known incoming originals only.
                    // The retained child pair must be distinct and stay live.
                    unsafe {
                        command.pre_exec(move || {
                            for fd in &originals {
                                let flags = libc::fcntl(*fd, libc::F_GETFD);
                                if flags < 0
                                    || libc::fcntl(*fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) < 0
                                {
                                    return Err(std::io::Error::last_os_error());
                                }
                            }
                            Ok(())
                        });
                    }
                }
                // Only the Command hook now owns the child transport.
                drop(cloned);
                assert!(command.status().unwrap().success());
            }
        }
        if let Some(pair) = owned_pair {
            for fd in pair {
                // SAFETY: query a known former transport slot without re-opening anything.
                assert_eq!(
                    unsafe { libc::fcntl(fd, libc::F_GETFD) },
                    -1,
                    "child transport leaked"
                );
            }
        }
        return;
    }
    // SAFETY: capture before opening the control socket or inspecting files.
    let before = [
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        jobserver_utils::DESCENDANT_HANDOFF_ENV,
    ]
    .map(env::var_os);
    let inherited = unsafe { Jobserver::from_env_with_handoff() }.unwrap();
    assert_eq!(
        before,
        [
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            jobserver_utils::DESCENDANT_HANDOFF_ENV
        ]
        .map(env::var_os),
        "native import changed authenticated environment bytes"
    );
    let mut control = BufReader::new(UnixStream::connect(env::var_os(SOCKET).unwrap()).unwrap());
    control.get_mut().set_read_timeout(Some(TIMEOUT)).unwrap();
    send(&mut control, &std::process::id().to_string());
    let canary = env::var("TARGO_JOBSERVER_CANARY")
        .unwrap()
        .split(',')
        .map(|n| n.parse::<u64>().unwrap())
        .collect::<Vec<_>>();
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fstat writes only this stat object, if the old slot is still open.
    let survives = if unsafe { libc::fstat(canary[0] as i32, stat.as_mut_ptr()) } == 0 {
        // SAFETY: successful fstat initialized stat.
        let stat = unsafe { stat.assume_init() };
        stat.st_dev as u64 == canary[1] && stat.st_ino as u64 == canary[2]
    } else {
        false
    };
    let exec = env::var("TARGO_JOBSERVER_MODE").unwrap() == "exec";
    assert_eq!(survives, exec, "unrelated descriptor inheritance changed");
    if env::var_os("TARGO_JOBSERVER_ABSENT").is_some() {
        assert!(inherited.is_none());
        send(&mut control, "ABSENT");
        expect(&mut control, "FINISH");
    } else {
        assert_eq!(
            env::var_os("CARGO_MAKEFLAGS"),
            env::var_os("TARGO_JOBSERVER_EXPECTED_AUTH")
        );
        let server = inherited.unwrap();
        if env::var("CARGO_MAKEFLAGS")
            .unwrap()
            .contains("--jobserver-auth=fifo:")
        {
            assert!(server.client().try_acquire().unwrap().is_none());
        } else {
            assert_eq!(server.client().available().unwrap(), 0);
        }
        send(&mut control, "EXHAUSTED");
        expect(&mut control, "GO");
        let held = server.client().acquire().unwrap();
        send(&mut control, "ACQUIRED");
        expect(&mut control, "DROP");
        drop(held);
        send(&mut control, "RELEASED");
    }
    if exec {
        std::process::exit(23);
    }
}
