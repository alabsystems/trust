// Trust: real subprocess checks for scheduling authority across both shims.
#![cfg(unix)]

use std::env;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use jobserver::Client;
use jobserver_utils::{DESCENDANT_HANDOFF_ENV, Jobserver};
use shim_utils::InheritedJobserver;

const ROLE: &str = "BOOTSTRAP_JOBSERVER_TEST_ROLE";
const SOCKET: &str = "BOOTSTRAP_JOBSERVER_TEST_SOCKET";
const TIMEOUT: Duration = Duration::from_secs(15);

// Kill/reap only this test's own process group if an assertion or deadline
// fails, so a broken token handoff cannot strand a waiting descendant.
struct Running(Child);

impl Running {
    fn wait(&mut self) -> std::process::ExitStatus {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            if let Some(status) = self.0.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < deadline, "owned shim subprocess timed out");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            // SAFETY: spawn below creates a new group with this child's PID;
            // every process in it belongs to this test, not another build.
            unsafe { libc::kill(-(self.0.id() as i32), libc::SIGKILL) };
            let _ = self.0.wait();
        }
    }
}

struct Fixture {
    directory: tempfile::TempDir,
    driver: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let driver = directory.path().join("driver");
        // The fake driver runs this owned test executable, ignores the shim's
        // compiler options, and never executes a compiler or canonical tool.
        fs::write(&driver, "#!/bin/sh\nexec \"$BOOTSTRAP_JOBSERVER_TEST_EXE\" --exact child_process --nocapture --test-threads=1\n").unwrap();
        fs::set_permissions(&driver, fs::Permissions::from_mode(0o700)).unwrap();
        Self { directory, driver }
    }

    fn command(&self, kind: &str) -> Command {
        let mut command = match kind {
            "rustc" | "version" | "literal_version" | "wrapped_version" => {
                Command::new(env!("CARGO_BIN_EXE_rustc"))
            }
            "rustdoc" => Command::new(env!("CARGO_BIN_EXE_rustdoc")),
            _ => {
                let mut command = Command::new(env::current_exe().unwrap());
                command.args(["--exact", "child_process", "--nocapture", "--test-threads=1"]);
                command
            }
        };
        command
            .env_clear()
            .env(
                ROLE,
                if matches!(
                    kind,
                    "rustc" | "version" | "rustdoc" | "literal_version" | "wrapped_version"
                ) {
                    "probe"
                } else {
                    kind
                },
            )
            .env("BOOTSTRAP_JOBSERVER_TEST_EXE", env::current_exe().unwrap())
            .env("RUSTC_STAGE", "0")
            .env("RUSTC_REAL", &self.driver)
            .env("RUSTC_SNAPSHOT", &self.driver)
            .env("RUSTC_LIBDIR", self.directory.path())
            .env("RUSTC_SNAPSHOT_LIBDIR", self.directory.path())
            .env("RUSTDOC_REAL", &self.driver)
            .env("RUSTDOC_LIBDIR", self.directory.path())
            .env("RUSTC_SYSROOT", self.directory.path())
            .env("CFG_COMPILER_BUILD_TRIPLE", env!("BUILD_TRIPLE"))
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .process_group(0);
        if kind == "literal_version" {
            command.arg("--version");
        } else if kind == "wrapped_version" {
            command.env("RUSTC", &self.driver).arg(&self.driver).arg("--version");
        } else if matches!(kind, "rustc" | "rustdoc" | "version") {
            let args = self.directory.path().join("args");
            fs::write(
                &args,
                if kind == "version" { "-vV\n" } else { "input.rs\n--crate-name\nfixture\n" },
            )
            .unwrap();
            command.arg(format!("@{}", args.display()));
        }
        command
    }

    fn launch(&self, command: &mut Command) -> (Running, BufReader<UnixStream>) {
        let socket = self.directory.path().join("control.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        command.env(SOCKET, socket);
        let child = Running(command.spawn().unwrap());
        let (send, receive) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = send.send(listener.accept());
        });
        let (stream, _) = receive.recv_timeout(TIMEOUT).expect("driver did not connect").unwrap();
        stream.set_read_timeout(Some(TIMEOUT)).unwrap();
        stream.set_write_timeout(Some(TIMEOUT)).unwrap();
        (child, BufReader::new(stream))
    }
}

fn line(stream: &mut BufReader<UnixStream>, expected: &str) {
    let mut line = String::new();
    stream.read_line(&mut line).unwrap();
    assert_eq!(line.trim_end(), expected);
}

fn send(stream: &mut BufReader<UnixStream>, message: &str) {
    writeln!(stream.get_mut(), "{message}").unwrap();
}

fn shared_tokens(kind: &str) {
    let fixture = Fixture::new();
    let mut server = Jobserver::new(1).unwrap();
    if kind == "plain_recovery" {
        server.enable_descendant_handoff().unwrap();
    }
    let held = server.client().acquire().unwrap();
    let mut command = fixture.command(kind);
    server.configure(&mut command);
    let canary_file = File::open(&fixture.driver).unwrap();
    {
        let fd = canary_file.as_raw_fd();
        let metadata = canary_file.metadata().unwrap();
        command.env(
            "BOOTSTRAP_JOBSERVER_TEST_CANARY",
            format!("{fd},{},{}", metadata.dev(), metadata.ino()),
        );
        // SAFETY: hand this known canary to the first shim/relay only. The
        // real or simulated Trust-std strip must remove it at the next spawn.
        unsafe {
            command.pre_exec(move || {
                if libc::fcntl(fd, libc::F_SETFD, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
    }
    let (mut child, mut control) = fixture.launch(&mut command);
    line(&mut control, "EXHAUSTED");
    assert_eq!(server.client().available().unwrap(), 0);
    drop(held);
    send(&mut control, "GO");
    line(&mut control, "ACQUIRED");
    assert_eq!(server.client().available().unwrap(), 0, "driver acquired a private server's token");
    send(&mut control, "DROP");
    line(&mut control, "RELEASED");
    assert!(child.wait().success());
    assert_eq!(server.client().available().unwrap(), 1, "shared token was lost or duplicated");
}

#[test]
fn imported_pipe_survives_stripping_and_unrelated_descriptor_does_not() {
    shared_tokens("relay");
}

#[test]
fn rustc_compile_preserves_the_shared_server_through_argument_files() {
    // These real-shim compositions require the pinned Trust std's SP-1
    // default strip. The relay above also emulates it on older/stock std.
    shared_tokens("rustc");
}

#[test]
fn rustdoc_preserves_the_shared_server_through_argument_files() {
    shared_tokens("rustdoc");
}

#[test]
fn rustc_version_query_preserves_the_shared_server() {
    shared_tokens("version");
}

#[test]
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn plain_build_script_hop_recovers_exactly_the_exhausted_pool() {
    shared_tokens("plain_recovery");
}

// Trust: rustix-style build-script probes use a plain Command rather than a
// jobserver-aware launcher. Exercise that extra spawn with the actual compiler
// and the actual Trust std used to build this test, not the fake driver above.
#[test]
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn three_hop_plain_command_stdin_metadata_compiles() {
    let fixture = Fixture::new();
    let compiler = env!("BOOTSTRAP_TEST_BUILD_RUSTC");
    // Trust (CUSTODY-PROTOCOL1-LAUNCH-1): Cargo hands this test binary no
    // scheduler, and under `build-slot` protocol 1 a strict compiler refuses a
    // query that is handed none (a compiler that predates
    // CUSTODY-BOUNDED-QUERY-SPELLINGS-1 refuses even `--print sysroot`). The
    // test waits on the query, so it lends the compiler its own execution, in
    // every context: an owned pool holding no token, with the descendant
    // handoff. The loan replaces any GNU advertisement this process
    // inherited. The query is only setup, and the advertisement refusals have
    // their own tests below. The query runs in its own process group under
    // this file's deadline, so a compiler that waited for a token it can
    // never get fails the test rather than hanging it.
    let mut query = Command::new(compiler);
    query
        .args(["--print", "sysroot"])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0);
    let mut lent = Jobserver::new(0).unwrap();
    lent.enable_descendant_handoff().unwrap();
    lent.configure_make(&mut query);
    let mut running = Running(query.spawn().unwrap());
    let status = running.wait();
    let (mut stdout, mut stderr) = (String::new(), String::new());
    running.0.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    running.0.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
    // The spawn hooks share the loan's pipe and handoff endpoint, so the loan
    // is released only with the command, now that the query has been reaped.
    drop((running, query, lent));
    assert!(status.success(), "{status:?}: {stderr}");
    let sysroot = PathBuf::from(stdout.trim());
    let mut server = Jobserver::new(1).unwrap();
    server.enable_descendant_handoff().unwrap();
    let mut command = fixture.command("stdin_build_script");
    command
        .env("RUSTC_REAL", compiler)
        .env("RUSTC_SNAPSHOT", compiler)
        .env("RUSTC_SYSROOT", &sysroot)
        .env("RUSTC_LIBDIR", sysroot.join("lib"))
        .env("RUSTC_SNAPSHOT_LIBDIR", sysroot.join("lib"))
        .env("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "1")
        .env("RUSTC_BOOTSTRAP", "1")
        .env("BOOTSTRAP_JOBSERVER_TEST_OUT", fixture.directory.path().join("probe.rmeta"));
    server.configure(&mut command);
    let mut child = Running(command.spawn().unwrap());
    assert!(child.wait().success(), "three-hop stdin metadata probe failed");
    assert!(fixture.directory.path().join("probe.rmeta").metadata().unwrap().len() > 0);
    assert_eq!(server.client().available().unwrap(), 1, "probe changed the original token pool");
}

#[test]
fn absent_jobserver_stays_absent_in_relay_and_both_shims() {
    for kind in ["relay", "rustc", "rustdoc", "version"] {
        for disabled in [false, true] {
            let fixture = Fixture::new();
            let mut command = fixture.command(kind);
            command.env("BOOTSTRAP_JOBSERVER_TEST_NO_SERVER", "1");
            if disabled {
                command.env("CARGO_MAKEFLAGS", "--jobserver-auth=-2,-2");
                command.env("BOOTSTRAP_JOBSERVER_TEST_DISABLED_SERVER", "1");
            }
            let (mut child, mut control) = fixture.launch(&mut command);
            line(&mut control, "NO_SERVER");
            send(&mut control, "FINISH");
            assert!(child.wait().success(), "{kind}");
        }
    }
}

#[test]
fn stripping_without_forwarding_destroys_the_advertised_server() {
    let fixture = Fixture::new();
    let server = Client::new(1).unwrap();
    let mut command = fixture.command("relay_without_forwarding");
    server.configure(&mut command);
    command.env("BOOTSTRAP_JOBSERVER_TEST_INVALID_SERVER", "1");
    let (mut child, mut control) = fixture.launch(&mut command);
    line(&mut control, "INVALID_SERVER");
    send(&mut control, "FINISH");
    assert!(child.wait().success());
}

#[test]
fn malformed_servers_refuse_before_either_shim_opens_argument_files() {
    for kind in ["rustc", "rustdoc"] {
        for auth in ["bad", "999999,999999"] {
            let fixture = Fixture::new();
            let mut command = fixture.command(kind);
            command
                .args(["@/no/such/bootstrap-jobserver-argument-file"])
                .env("CARGO_MAKEFLAGS", format!("--jobserver-auth={auth}"))
                .stderr(Stdio::piped());
            let output = command.output().unwrap();
            assert!(!output.status.success());
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert!(stderr.contains("cannot inherit bootstrap jobserver"), "{kind}: {stderr}");
            assert!(!stderr.contains("failed to load"), "{kind}: {stderr}");
        }
    }
}

#[test]
fn literal_version_queries_do_not_require_stripped_build_script_jobservers() {
    for kind in ["literal_version", "wrapped_version"] {
        for auth in ["bad", "999999,999999"] {
            let fixture = Fixture::new();
            let mut command = fixture.command(kind);
            command
                .env("CARGO_MAKEFLAGS", format!("--jobserver-auth={auth}"))
                .env("MAKEFLAGS", "--jobserver-auth=999998,999998")
                .env("MFLAGS", "--jobserver-auth=999997,999997")
                .env(DESCENDANT_HANDOFF_ENV, "untrusted-version-query-endpoint")
                .env("BOOTSTRAP_JOBSERVER_TEST_NO_SERVER", "1");
            let (mut child, mut control) = fixture.launch(&mut command);
            line(&mut control, "NO_SERVER");
            send(&mut control, "FINISH");
            assert!(child.wait().success(), "{kind}: {auth}");
        }
    }
}

#[test]
fn unavailable_server_version_exception_never_opens_response_files_or_compiles() {
    for kind in ["version", "literal_version", "wrapped_version"] {
        let fixture = Fixture::new();
        let mut command = fixture.command(kind);
        if kind != "version" {
            command.arg("input.rs");
        }
        let output = command
            .env("CARGO_MAKEFLAGS", "--jobserver-auth=999999,999999")
            .stderr(Stdio::piped())
            .output()
            .unwrap();
        assert!(!output.status.success());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("cannot inherit bootstrap jobserver"), "{kind}: {stderr}");
        assert!(!stderr.contains("failed to load"), "{kind}: {stderr}");
    }
}

#[test]
fn compiler_looking_response_files_refuse_before_version_prefix_recognition() {
    for name in ["trustc", "rustc", "custom-driver", "tippy-driver", "clippy-driver"] {
        for auth in ["bad", "999999,999999"] {
            let fixture = Fixture::new();
            let response_file = fixture.directory.path().join(name);
            // If prefix classification admits this response file, expansion
            // reads these invalid UTF-8 bytes and reports a load failure.
            fs::write(&response_file, [0xff]).unwrap();
            let prefix = format!("@{}", response_file.display());
            let mut command = Command::new(env!("CARGO_BIN_EXE_rustc"));
            command
                .env_clear()
                .env("CARGO_MAKEFLAGS", format!("--jobserver-auth={auth}"))
                .env("CFG_COMPILER_BUILD_TRIPLE", env!("BUILD_TRIPLE"))
                .stdin(Stdio::null())
                .arg(&prefix);
            if name == "custom-driver" {
                command.env("RUSTC", &prefix);
            }
            if name.ends_with("-driver") && name != "custom-driver" {
                command.arg("--rustc");
            }
            let output = command.arg("--version").output().unwrap();
            assert!(!output.status.success());
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert!(stderr.contains("cannot inherit bootstrap jobserver"), "{name}: {stderr}");
            assert!(!stderr.contains("failed to load"), "{name}: {stderr}");
        }
    }
}

#[test]
fn both_shims_reject_advertised_regular_file_descriptors() {
    for kind in ["rustc", "rustdoc"] {
        let fixture = Fixture::new();
        let file = File::open(&fixture.driver).unwrap();
        let fd = file.as_raw_fd();
        let mut command = fixture.command(kind);
        command
            .env("CARGO_MAKEFLAGS", format!("--jobserver-auth={fd},{fd}"))
            .stderr(Stdio::piped());
        // SAFETY: pass this owned regular-file canary so checked import must
        // reject its type, rather than merely detecting a closed number.
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
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("cannot inherit bootstrap jobserver"), "{kind}: {stderr}");
        assert!(stderr.contains("not a pipe"), "{kind}: {stderr}");
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn imported_owner_plain_hop_preserves_the_original_exhausted_pool() {
    shared_tokens("imported_owner");
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn forged_recovery_fields_refuse_before_argument_files_and_keep_the_pool() {
    let fixture = Fixture::new();
    let mut server = Jobserver::new(1).unwrap();
    server.enable_descendant_handoff().unwrap();
    let held = server.client().acquire().unwrap();
    for mutant in ["capability", "pool", "owner", "birth", "flags", "missing"] {
        let mut command = fixture.command("recovery_refusal");
        command.env("BOOTSTRAP_JOBSERVER_TEST_MUTANT", mutant);
        server.configure(&mut command);
        let output = command.stderr(Stdio::piped()).output().unwrap();
        assert!(output.status.success(), "{mutant}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(server.client().available().unwrap(), 0, "{mutant} changed the original pool");
    }
    // A refused request must not poison this live owner's later valid probe.
    let mut command = fixture.command("plain_recovery");
    server.configure(&mut command);
    let (mut child, mut control) = fixture.launch(&mut command);
    line(&mut control, "EXHAUSTED");
    assert_eq!(server.client().available().unwrap(), 0);
    drop(held);
    send(&mut control, "GO");
    line(&mut control, "ACQUIRED");
    assert_eq!(server.client().available().unwrap(), 0);
    send(&mut control, "DROP");
    line(&mut control, "RELEASED");
    assert!(child.wait().success());
    assert_eq!(server.client().available().unwrap(), 1);
}

fn imported_owner_role() {
    // SAFETY: the explicitly inherited original pair is still live; capture
    // precedes this role's file handling and every subsequent spawn.
    let mut server = unsafe { Jobserver::from_env() }.unwrap().unwrap();
    server.enable_descendant_handoff().unwrap();
    let mut command = Command::new(env::current_exe().unwrap());
    command
        .args(["--exact", "child_process", "--nocapture", "--test-threads=1"])
        .env(ROLE, "plain_recovery");
    server.configure(&mut command);
    assert!(command.status().unwrap().success());
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn recovery_refusal_role() {
    use std::os::unix::ffi::{OsStrExt, OsStringExt};

    let original = env::var_os(DESCENDANT_HANDOFF_ENV).unwrap();
    let mut fields =
        original.as_bytes().splitn(6, |byte| *byte == b':').map(<[u8]>::to_vec).collect::<Vec<_>>();
    assert_eq!(fields.len(), 6);
    let mutant = env::var("BOOTSTRAP_JOBSERVER_TEST_MUTANT").unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_rustc"));
    command
        .args(["@/no/such/bootstrap-jobserver-argument-file", "input.rs"])
        .env(ROLE, "probe")
        .stderr(Stdio::piped());
    match mutant.as_str() {
        "capability" => fields[4][0] = if fields[4][0] == b'0' { b'1' } else { b'0' },
        "pool" => {
            fields[3] = b"999995,999996".to_vec();
            command.env(
                "CARGO_MAKEFLAGS",
                "-j --jobserver-fds=999995,999996 --jobserver-auth=999995,999996",
            );
        }
        "owner" => fields[1] = b"4294967294".to_vec(),
        "birth" => fields[2] = if fields[2] == b"1" { b"2".to_vec() } else { b"1".to_vec() },
        "flags" => {
            let mut flags = env::var_os("CARGO_MAKEFLAGS").unwrap();
            flags.push(" ");
            command.env("CARGO_MAKEFLAGS", flags);
        }
        "missing" => {}
        _ => panic!("unknown refusal control {mutant}"),
    }
    if mutant == "missing" {
        command.env_remove(DESCENDANT_HANDOFF_ENV);
    } else {
        command.env(DESCENDANT_HANDOFF_ENV, std::ffi::OsString::from_vec(fields.join(&b':')));
    }
    // No fd opt-in: SP-1 must close the advertised numeric pair before the
    // actual shim considers the altered recovery binding.
    let output = command.output().unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("cannot inherit bootstrap jobserver"), "{mutant}: {stderr}");
    assert!(!stderr.contains("failed to load"), "{mutant}: {stderr}");
    if matches!(mutant.as_str(), "owner" | "birth") {
        assert!(stderr.contains("substituted owner"), "{mutant}: {stderr}");
    } else if mutant == "flags" {
        assert!(stderr.contains("does not bind"), "{mutant}: {stderr}");
    }
}

#[test]
fn child_process() {
    let Ok(role) = env::var(ROLE) else { return };
    if role == "imported_owner" {
        imported_owner_role();
        return;
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if role == "recovery_refusal" {
        recovery_refusal_role();
        return;
    }
    if role == "plain_recovery" {
        let mut command = Command::new(env!("CARGO_BIN_EXE_rustc"));
        command.args(["input.rs", "--crate-name", "fixture"]).env(ROLE, "probe");
        // No pre_exec or fd opt-in: the exact formerly failing middle hop.
        assert!(command.status().unwrap().success());
        return;
    }
    if role == "stdin_build_script" {
        // Exactly the problematic hop: no inherited fd opt-in or pre_exec hook.
        let mut command = Command::new(env!("CARGO_BIN_EXE_rustc"));
        command
            .args(["--crate-type=rlib", "--emit=metadata", "--target", env!("BUILD_TRIPLE")])
            .arg("-o")
            .arg(env::var_os("BOOTSTRAP_JOBSERVER_TEST_OUT").unwrap())
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped());
        let mut child = command.spawn().unwrap();
        // Retain both the write result and the shim's otherwise hidden stderr:
        // an early shim panic must not be reported as an unexplained EPIPE.
        let mut stdin = child.stdin.take().unwrap();
        let writer = std::thread::spawn(move || {
            let input = format!("pub fn probe() -> u8 {{ 7 }}\n/*{}*/\n", "x".repeat(256 * 1024));
            stdin.write_all(input.as_bytes())
        });
        let output = child.wait_with_output().unwrap();
        let written = writer.join().unwrap();
        assert!(
            output.status.success() && written.is_ok(),
            "stdin write: {written:?}; status: {}; shim stderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr),
        );
        return;
    }
    if role.starts_with("relay") {
        // SAFETY: the inherited descriptors are still live; capture precedes
        // this relay's argument/file handling, just like the production shims.
        let inherited = unsafe { InheritedJobserver::from_env() }.unwrap();
        let mut command = Command::new(env::current_exe().unwrap());
        command
            .args(["--exact", "child_process", "--nocapture", "--test-threads=1"])
            .env(ROLE, "probe");
        let mut strip = Vec::new();
        if let Ok(flags) = env::var("CARGO_MAKEFLAGS") {
            let pair = flags
                .split_whitespace()
                .find_map(|flag| flag.strip_prefix("--jobserver-auth="))
                .unwrap();
            strip
                .extend(pair.split(',').map(|fd| fd.parse::<i32>().unwrap()).filter(|fd| *fd >= 0));
        }
        if let Ok(canary) = env::var("BOOTSTRAP_JOBSERVER_TEST_CANARY") {
            strip.push(canary.split(',').next().unwrap().parse().unwrap());
        }
        // SAFETY: emulate Trust std on older/stock std by marking exactly the
        // known original descriptors CLOEXEC. The forwarding hook must restore
        // its OWN advertised copies, not these borrowed original numbers.
        unsafe {
            command.pre_exec(move || {
                for fd in &strip {
                    let flags = libc::fcntl(*fd, libc::F_GETFD);
                    if flags < 0 || libc::fcntl(*fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
        if role == "relay" {
            inherited.configure(&mut command);
        }
        // Even an early wrapper drop must leave the configured command's
        // advertised pair owned until spawn, with no stale descriptor numbers.
        drop(inherited);
        assert!(command.status().unwrap().success());
        return;
    }

    let mut control = BufReader::new(UnixStream::connect(env::var_os(SOCKET).unwrap()).unwrap());
    control.get_mut().set_read_timeout(Some(TIMEOUT)).unwrap();
    // SAFETY: the parent/shim kept the advertised descriptors alive; no code
    // in this probe closes or reassigns them before this checked construction.
    let server = unsafe { Client::from_env_ext(true) }.client;
    assert!(
        env::var_os(DESCENDANT_HANDOFF_ENV).is_none(),
        "leaf driver retained recovery metadata"
    );
    if env::var_os("BOOTSTRAP_JOBSERVER_TEST_NO_SERVER").is_some() {
        let absent = server.unwrap_err().kind();
        if env::var_os("BOOTSTRAP_JOBSERVER_TEST_DISABLED_SERVER").is_some() {
            assert!(matches!(absent, jobserver::FromEnvErrorKind::NegativeFd));
        } else {
            assert!(matches!(absent, jobserver::FromEnvErrorKind::NoEnvVar));
        }
        send(&mut control, "NO_SERVER");
        line(&mut control, "FINISH");
        return;
    }
    if env::var_os("BOOTSTRAP_JOBSERVER_TEST_INVALID_SERVER").is_some() {
        assert!(matches!(
            server.unwrap_err().kind(),
            jobserver::FromEnvErrorKind::CannotOpenFd | jobserver::FromEnvErrorKind::NotAPipe
        ));
        send(&mut control, "INVALID_SERVER");
        line(&mut control, "FINISH");
        return;
    }
    if let Ok(canary) = env::var("BOOTSTRAP_JOBSERVER_TEST_CANARY") {
        let numbers = canary.split(',').map(|n| n.parse::<u64>().unwrap()).collect::<Vec<_>>();
        let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: fstat writes only the provided stat object. Compare identity
        // because a runtime may legitimately reuse the old descriptor number.
        if unsafe { libc::fstat(numbers[0] as i32, metadata.as_mut_ptr()) } == 0 {
            // SAFETY: successful fstat initialized the entire stat object.
            let metadata = unsafe { metadata.assume_init() };
            assert!(
                metadata.st_dev as u64 != numbers[1] || metadata.st_ino as u64 != numbers[2],
                "unrelated descriptor crossed the handoff"
            );
        }
    }
    let server = server.unwrap();
    assert_eq!(server.available().unwrap(), 0, "driver received an independent budget");
    send(&mut control, "EXHAUSTED");
    line(&mut control, "GO");
    let token = server.acquire().unwrap();
    send(&mut control, "ACQUIRED");
    line(&mut control, "DROP");
    drop(token);
    send(&mut control, "RELEASED");
}
