// Trust: real nested frontend + compiler-probe scheduling, using local inputs.
#![cfg(unix)]

use std::env;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use cargo_util::Jobserver;

const TIMEOUT: Duration = Duration::from_secs(30);
struct Running(Child);
impl Running {
    fn wait(&mut self) -> std::process::ExitStatus {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            if let Some(status) = self.0.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < deadline, "owned native Targo timed out");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            // SAFETY: every member of this private group was started by us.
            unsafe { libc::kill(-(self.0.id() as i32), libc::SIGKILL) };
            let _ = self.0.wait();
        }
    }
}
fn read(stream: &mut BufReader<UnixStream>, expected: &str) {
    let mut message = String::new();
    stream.read_line(&mut message).unwrap();
    assert_eq!(message.trim_end(), expected);
}
fn write(stream: &mut BufReader<UnixStream>, message: &str) {
    writeln!(stream.get_mut(), "{message}").unwrap();
}
fn executable(path: &std::path::Path, bytes: &str) {
    fs::write(path, bytes).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
}

#[test]
fn nested_native_targo_and_compiler_probes_keep_the_parent_server() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let bin = root.join("bin");
    fs::create_dir(&bin).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='jobserver_fixture'\nversion='0.0.0'\nedition='2024'\n[lib]\npath='lib.rs'\n").unwrap();
    fs::write(root.join("lib.rs"), "pub fn value() -> u32 { 42 }\n").unwrap();
    let test_shim_dir = env::var_os("TEST_TRUST_SHIM_DIR").map(std::path::PathBuf::from);
    let real_rustc = test_shim_dir
        .as_ref()
        .map(|dir| dir.join("rustc").into_os_string())
        .or_else(|| env::var_os("RUSTC"))
        .expect("test requires an explicit compiler or bootstrap fixture shim");
    let real_rustdoc = test_shim_dir
        .as_ref()
        .map(|dir| dir.join("rustdoc").into_os_string())
        .or_else(|| env::var_os("RUSTDOC"))
        .expect("test requires a matching rustdoc or bootstrap fixture shim");
    // An ordinary extension is deliberately exec-replaced. Its nested real
    // frontend then spawns compiler probes: that second boundary must strip
    // unrelated descriptors while preserving only the scheduler it imported.
    executable(
        &bin.join("cargo-run-inner"),
        "#!/bin/sh\nexec \"$TARGO_TRANSPORT_NATIVE\" --unverified check --offline --manifest-path \"$TARGO_TRANSPORT_MANIFEST\"\n",
    );
    let rustc_proxy = bin.join("trustc");
    executable(
        &rustc_proxy,
        r#"#!/usr/bin/python3
import array, fcntl, os, socket, stat, sys, termios
flags = os.environ['CARGO_MAKEFLAGS']
auth = next(x.split('=', 1)[1] for x in flags.split() if x.startswith('--jobserver-auth='))
r, w = [int(x) for x in auth.split(',')]
assert stat.S_ISFIFO(os.fstat(r).st_mode) and stat.S_ISFIFO(os.fstat(w).st_mode)
old, dev, ino = [int(x) for x in os.environ['TARGO_TRANSPORT_CANARY'].split(',')]
try:
    item = os.fstat(old)
    assert (item.st_dev, item.st_ino) != (dev, ino), 'unrelated descriptor reached compiler probe'
except OSError:
    pass
try:
    marker = os.open(os.environ['TARGO_TRANSPORT_ONCE'], os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
except FileExistsError:
    marker = None
if marker is not None:
    os.close(marker)
    control = socket.socket(socket.AF_UNIX)
    control.settimeout(30)
    control.connect(os.environ['TARGO_TRANSPORT_SOCKET'])
    messages = control.makefile('rwb', buffering=0)
    available = array.array('i', [0])
    fcntl.ioctl(r, termios.FIONREAD, available, True)
    assert available[0] == 0, 'compiler probe received an independent budget'
    messages.write(b'EXHAUSTED\n')
    assert messages.readline() == b'GO\n'
    token = os.read(r, 1)
    assert len(token) == 1
    messages.write(b'ACQUIRED\n')
    assert messages.readline() == b'DROP\n'
    assert os.write(w, token) == 1
    messages.write(b'RELEASED\n')
    assert messages.readline() == b'CONTINUE\n'
    messages.close()
    control.close()
os.execv(os.environ['TARGO_TRANSPORT_RUSTC'], [os.environ['TARGO_TRANSPORT_RUSTC'], *sys.argv[1:]])
"#,
    );
    let canary_path = root.join("canary");
    fs::write(&canary_path, "unrelated input").unwrap();
    let canary = File::open(&canary_path).unwrap();
    let fd = canary.as_raw_fd();
    let identity = canary.metadata().unwrap();
    let server = Jobserver::new(1).unwrap();
    let held = server.client().acquire().unwrap();
    let socket = root.join("probe.sock");
    let listener = UnixListener::bind(&socket).unwrap();
    let native = env!("CARGO_BIN_EXE_targo");
    let mut command = Command::new(native);
    command
        .arg("run-inner")
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("cargo-home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env(
            "PATH",
            format!("{}:/usr/bin:/bin:/usr/sbin:/sbin", bin.display()),
        )
        .env("RUSTC", &rustc_proxy)
        .env("RUSTDOC", real_rustdoc)
        .env("TARGO_TRANSPORT_NATIVE", native)
        .env("TARGO_TRANSPORT_RUSTC", real_rustc)
        .env("TARGO_TRANSPORT_MANIFEST", root.join("Cargo.toml"))
        .env(
            "TARGO_TRANSPORT_CANARY",
            format!("{fd},{},{}", identity.dev(), identity.ino()),
        )
        .env("TARGO_TRANSPORT_SOCKET", socket)
        .env("TARGO_TRANSPORT_ONCE", root.join("probe-ran"))
        .current_dir(root)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .process_group(0);
    server.configure(&mut command);
    // SAFETY: explicitly pass only this test-owned canary into outer Targo.
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut child = Running(command.spawn().unwrap());
    listener.set_nonblocking(true).unwrap();
    let deadline = Instant::now() + TIMEOUT;
    let (stream, _) = loop {
        match listener.accept() {
            Ok(connection) => break connection,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(
                    child.0.try_wait().unwrap().is_none(),
                    "native Targo exited before its probe"
                );
                assert!(Instant::now() < deadline, "compiler probe did not connect");
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(error) => panic!("compiler probe accept: {error}"),
        }
    };
    // Darwin accepts inherit the listener's nonblocking flag.
    stream.set_nonblocking(false).unwrap();
    stream.set_read_timeout(Some(TIMEOUT)).unwrap();
    stream.set_write_timeout(Some(TIMEOUT)).unwrap();
    let mut control = BufReader::new(stream);
    read(&mut control, "EXHAUSTED");
    drop(held);
    write(&mut control, "GO");
    read(&mut control, "ACQUIRED");
    assert_eq!(
        server.client().available().unwrap(),
        0,
        "probe acquired another server's token"
    );
    write(&mut control, "DROP");
    read(&mut control, "RELEASED");
    // Resume the caller's implicit token reservation before compilation starts.
    let implicit = server.client().acquire().unwrap();
    write(&mut control, "CONTINUE");
    assert!(child.wait().success());
    drop(implicit);
    assert_eq!(server.client().available().unwrap(), 1);
    assert!(root.join("probe-ran").is_file());
    // SAFETY: inspect only the parent's still-owned canary descriptor.
    assert_ne!(
        unsafe { libc::fcntl(fd, libc::F_GETFD) } & libc::FD_CLOEXEC,
        0
    );
}

#[test]
fn invalid_advertised_servers_fail_before_logger_or_config() {
    for auth in [
        "not-a-server",
        "200001,200002",
        "regular-file",
        "non-fifo-path",
    ] {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let canary_path = root.join("regular-file");
        fs::write(&canary_path, "not a scheduling pipe").unwrap();
        let canary = File::open(&canary_path).unwrap();
        let fd = canary.as_raw_fd();
        fs::create_dir(root.join(".cargo")).unwrap();
        fs::write(root.join(".cargo/config.toml"), "invalid toml [").unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        command
            .args(["--unverified", "check"])
            .env_clear()
            .env("HOME", root)
            .env("CARGO_LOG_PROFILE", "true")
            .env(
                "CARGO_MAKEFLAGS",
                if auth == "regular-file" {
                    format!("--jobserver-auth={fd},{fd}")
                } else if auth == "non-fifo-path" {
                    format!("--jobserver-auth=fifo:{}", canary_path.display())
                } else {
                    format!("--jobserver-auth={auth}")
                },
            )
            .current_dir(root);
        // SAFETY: make the checked non-pipe case genuinely open in the child.
        unsafe {
            command.pre_exec(move || {
                if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(error.contains("cannot inherit Targo jobserver"), "{error}");
        assert!(
            !error.contains("could not parse"),
            "read config before scheduler refusal: {error}"
        );
        assert!(!root.join("target").exists());
        assert!(
            !fs::read_dir(root).unwrap().any(|entry| entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with("trace-")),
            "logger ran before checked capture"
        );
    }
}
