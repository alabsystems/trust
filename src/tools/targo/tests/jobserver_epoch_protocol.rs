// Trust: real private-helper refusals must never manufacture retirement or free CPU debt.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, Read as _, Write as _};
use std::num::NonZeroU32;
use std::os::fd::{AsRawFd as _, OwnedFd};
use std::os::unix::fs::{OpenOptionsExt as _, PermissionsExt as _, symlink};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use trust_build_cpu::{Owner, RETAINED_DIRECTORY_NAME, RetainedLease, RetainedPool};

const EPOCH: &str = "0123456789abcdef0123456789abcdef";
const FINALIZATION: &str = "fedcba9876543210fedcba9876543210";
const HANG: Duration = Duration::from_secs(60);
const FRAME: usize = 16 * 1024;

struct World {
    directory: Option<tempfile::TempDir>,
    passed: bool,
}

impl World {
    fn new() -> Self {
        let directory = tempfile::Builder::new()
            .prefix("targo-epoch-protocol-")
            .suffix(".noindex")
            .tempdir()
            .unwrap();
        fs::create_dir(directory.path().join("home")).unwrap();
        Self {
            directory: Some(directory),
            passed: false,
        }
    }

    fn path(&self) -> &Path {
        self.directory.as_ref().unwrap().path()
    }
}

impl Drop for World {
    fn drop(&mut self) {
        if !self.passed {
            let path = self.directory.take().unwrap().keep();
            eprintln!(
                "private epoch protocol evidence retained at {}",
                path.display()
            );
        }
    }
}

enum Output {
    Frame(io::Result<Vec<u8>>),
    Eof,
}

struct Helper {
    child: Child,
    input: Option<ChildStdin>,
    output: Receiver<Output>,
    reader: Option<std::thread::JoinHandle<()>>,
    frames: Vec<Value>,
}

impl Helper {
    fn start(world: &Path, directory: &Path, backing: u32, roots: u32, epoch: &str) -> Self {
        Self::start_with_stderr(world, directory, backing, roots, epoch, None)
    }

    fn start_with_stderr(
        world: &Path,
        directory: &Path,
        backing: u32,
        roots: u32,
        epoch: &str,
        stderr: Option<fs::File>,
    ) -> Self {
        let cargo_home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                PathBuf::from(std::env::var_os("HOME").expect("parent HOME")).join(".cargo")
            });
        let native_root = stderr.is_some();
        let stderr = stderr.unwrap_or_else(|| {
            OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(world.join("helper.stderr"))
                .unwrap()
        });
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        command
            .args(["--unverified", "__resource-epoch", "--directory"])
            .arg(directory)
            .args([
                "--epoch",
                epoch,
                "--backing",
                &backing.to_string(),
                "--roots",
                &roots.to_string(),
            ])
            .env_clear()
            .env("HOME", world.join("home"))
            .env("CARGO_HOME", cargo_home)
            .env("PATH", std::env::var_os("PATH").expect("parent PATH"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::from(stderr));
        if native_root {
            // Only the pipe regression compiles a genuine root; ordinary
            // protocol refusals retain their existing compiler-free fixture.
            command.env(
                "RUSTC",
                std::env::var_os("RUSTC").expect("native root compiler"),
            );
        }
        let mut child = command.spawn().unwrap();
        let input = child.stdin.take().unwrap();
        // Only our private control write end becomes nonblocking. No inherited
        // GNU description or process-wide environment is mutated.
        let fd = input.as_raw_fd();
        // SAFETY: the live ChildStdin descriptor is owned here.
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        assert!(flags >= 0);
        // SAFETY: this sets flags on our exclusively held control write end.
        assert_eq!(
            unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) },
            0
        );
        let stdout = child.stdout.take().unwrap();
        let mut log = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(world.join("helper.stdout"))
            .unwrap();
        let (send, output) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut stream = io::BufReader::new(stdout);
            let mut total = 0;
            loop {
                let mut bytes = Vec::new();
                let frame = stream
                    .by_ref()
                    .take((FRAME + 1) as u64)
                    .read_until(b'\n', &mut bytes)
                    .and_then(|count| {
                        if count == 0 {
                            return Ok(None);
                        }
                        total += count;
                        if count > FRAME || total > 64 * 1024 || !bytes.ends_with(b"\n") {
                            return Err(io::Error::other("unbounded helper protocol output"));
                        }
                        log.write_all(&bytes)?;
                        Ok(Some(bytes))
                    });
                match frame {
                    Ok(Some(bytes)) => {
                        if send.send(Output::Frame(Ok(bytes))).is_err() {
                            return;
                        }
                    }
                    Ok(None) => {
                        let _ = send.send(Output::Eof);
                        return;
                    }
                    Err(error) => {
                        let _ = send.send(Output::Frame(Err(error)));
                        return;
                    }
                }
            }
        });
        Self {
            child,
            input: Some(input),
            output,
            reader: Some(reader),
            frames: Vec::new(),
        }
    }

    fn event(&mut self, expected: &str) -> Value {
        let deadline = Instant::now() + HANG;
        loop {
            match self
                .output
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .expect("helper response within hang detector")
            {
                Output::Frame(bytes) => {
                    let frame: Value = serde_json::from_slice(&bytes.unwrap()).unwrap();
                    assert_eq!(frame["v"], 4);
                    assert_eq!(frame["epoch"], EPOCH);
                    self.frames.push(frame.clone());
                    if frame["event"] == expected {
                        return frame;
                    }
                }
                Output::Eof => panic!("helper ended before {expected}"),
            }
        }
    }

    fn send(&mut self, bytes: &[u8]) -> io::Result<()> {
        let input = self.input.as_mut().expect("live controller input");
        let deadline = Instant::now() + HANG;
        let mut remaining = bytes;
        while !remaining.is_empty() {
            match input.write(remaining) {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(count) => remaining = &remaining[count..],
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    assert!(
                        Instant::now() < deadline,
                        "control write exceeded hang detector"
                    );
                    let mut poll = libc::pollfd {
                        fd: input.as_raw_fd(),
                        events: libc::POLLOUT,
                        revents: 0,
                    };
                    // SAFETY: poll points to exactly one initialized descriptor.
                    let ready = unsafe { libc::poll(&raw mut poll, 1, 10) };
                    if ready < 0 {
                        let error = io::Error::last_os_error();
                        if error.kind() != io::ErrorKind::Interrupted {
                            return Err(error);
                        }
                    }
                }
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }

    fn request(&mut self, op: &str) {
        let mut request = json!({"v":4,"epoch":EPOCH,"op":op});
        if op == "finalize" {
            request["finalization"] = json!(FINALIZATION);
        }
        let mut bytes = serde_json::to_vec(&request).unwrap();
        bytes.push(b'\n');
        self.send(&bytes).unwrap();
    }

    fn refused(&mut self) {
        // Keep control stdin open here: an ignored malformed message must not
        // pass merely because a later EOF caused the helper to fail.
        let deadline = Instant::now() + HANG;
        let status = loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                break status;
            }
            assert!(
                Instant::now() < deadline,
                "helper refusal exceeded hang detector"
            );
            std::thread::sleep(Duration::from_millis(10));
        };
        assert!(!status.success(), "invalid control must refuse");
        assert_eq!(
            status.code(),
            Some(101),
            "refusal must be the actual helper error exit"
        );
        self.input.take();
        loop {
            match self
                .output
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .expect("helper output EOF within hang detector")
            {
                Output::Frame(bytes) => self
                    .frames
                    .push(serde_json::from_slice(&bytes.unwrap()).unwrap()),
                Output::Eof => break,
            }
        }
        self.reader.take().unwrap().join().unwrap();
        assert!(
            self.frames
                .iter()
                .all(|frame| { frame["event"] != "retired" && frame["event"] != "closed" }),
            "refusal manufactured retirement or obsolete closure"
        );
    }
}

impl Drop for Helper {
    fn drop(&mut self) {
        self.input.take();
        if matches!(self.child.try_wait(), Ok(None)) {
            let _ = self.child.kill();
        }
        let deadline = Instant::now() + HANG;
        loop {
            match self.child.try_wait() {
                Ok(Some(_)) | Err(_) => break,
                Ok(None) => {
                    if Instant::now() >= deadline {
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(10));
                }
            }
        }
        if let Some(reader) = self.reader.take() {
            loop {
                match self
                    .output
                    .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                {
                    Ok(Output::Frame(_)) => {}
                    Ok(Output::Eof) | Err(mpsc::RecvTimeoutError::Disconnected) => {
                        let _ = reader.join();
                        break;
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => break,
                }
            }
        }
    }
}

struct Fixture {
    helper: Option<Helper>,
    leases: Vec<RetainedLease>,
    pool: RetainedPool,
    world: World,
    directory: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        Self::with_units(1)
    }

    fn with_units(units: u32) -> Self {
        let world = World::new();
        let pool = RetainedPool::create_private(
            &world.path().join("cpu.noindex"),
            NonZeroU32::new(units).unwrap(),
        )
        .unwrap();
        let leases = (0..units)
            .map(|_| pool.try_acquire(Owner::current(None)).unwrap().unwrap())
            .collect();
        let directory = world.path().join("epoch.noindex");
        Self {
            helper: None,
            leases,
            pool,
            world,
            directory,
        }
    }

    fn start(&mut self, backing: u32, roots: u32, epoch: &str) {
        self.helper = Some(Helper::start(
            self.world.path(),
            &self.directory,
            backing,
            roots,
            epoch,
        ));
    }

    fn opened(&mut self) -> Value {
        self.start(1, 1, EPOCH);
        let opened = self.helper.as_mut().unwrap().event("opened");
        assert_eq!(opened["published"], 0);
        assert!(
            self.pool
                .try_acquire(Owner::current(None))
                .unwrap()
                .is_none()
        );
        opened
    }

    fn retained(&mut self) {
        self.leases.clear();
        for slot in 0..self.pool.slots().get() {
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .open(
                    self.pool
                        .path()
                        .join(RETAINED_DIRECTORY_NAME)
                        .join(format!("slot-{slot:08x}")),
                )
                .unwrap();
            let deadline = Instant::now() + HANG;
            loop {
                match file.try_lock() {
                    Ok(()) => break,
                    Err(std::fs::TryLockError::WouldBlock) => {
                        assert!(
                            Instant::now() < deadline,
                            "actual CPU kernel release within hang detector"
                        );
                        std::thread::sleep(Duration::from_millis(10));
                    }
                    Err(std::fs::TryLockError::Error(error)) => panic!("kernel probe: {error}"),
                }
            }
            file.unlock().unwrap();
            drop(file);
        }
        let fresh = RetainedPool::open_existing(self.pool.path())
            .unwrap()
            .unwrap();
        assert!(fresh.try_acquire(Owner::current(None)).unwrap().is_none());
        self.world.passed = true;
    }
}

fn private_stderr_pipe() -> (fs::File, fs::File) {
    let (reader, writer) = io::pipe().unwrap();
    let reader = fs::File::from(OwnedFd::from(reader));
    let writer = fs::File::from(OwnedFd::from(writer));
    // SAFETY: only our read end becomes nonblocking, independent of the write
    // description handed to the helper as its stderr.
    let flags = unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_GETFL) };
    assert!(flags >= 0);
    // SAFETY: the exclusively owned read description remains live here.
    assert_eq!(
        unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) },
        0
    );
    (reader, writer)
}

fn fill_then_restore_blocking_stderr(writer: &fs::File) -> usize {
    struct Restore<'a> {
        writer: &'a fs::File,
        flags: i32,
    }
    impl Drop for Restore<'_> {
        fn drop(&mut self) {
            // SAFETY: the borrowed private writer stays open through restoration.
            let _ = unsafe { libc::fcntl(self.writer.as_raw_fd(), libc::F_SETFL, self.flags) };
        }
    }
    // SAFETY: read flags only from our live private pipe write description.
    let flags = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFL) };
    assert!(flags >= 0 && flags & libc::O_NONBLOCK == 0);
    let restore = Restore { writer, flags };
    // SAFETY: the helper shares only this fixture-owned stderr description;
    // it is restored before any refused command is sent.
    assert_eq!(
        unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) },
        0
    );
    let bytes = [b'x'; 4096];
    let mut size = bytes.len();
    let mut filled = 0;
    let deadline = Instant::now() + HANG;
    let mut output = writer;
    loop {
        assert!(Instant::now() < deadline, "private stderr never filled");
        match output.write(&bytes[..size]) {
            Ok(0) => panic!("private stderr write made no progress"),
            Ok(count) => filled += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock && size != 1 => size = 1,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
            Err(error) => panic!("private stderr fill failed: {error}"),
        }
    }
    assert!(filled > 0);
    drop(restore);
    // SAFETY: confirm the same live write description is blocking again.
    assert_eq!(
        unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFL) } & libc::O_NONBLOCK,
        0
    );
    filled
}

#[test]
fn malformed_or_foreign_control_refuses_without_retired_or_free_backing() {
    let bad_frames: Vec<Vec<u8>> = vec![
        b"{not json}\n".to_vec(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"close\",\"unknown\":true}}\n").into_bytes(),
        b"{\"v\":4,\"epoch\":\"ffffffffffffffffffffffffffffffff\",\"op\":\"close\"}\n".to_vec(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"spawn\",\"id\":1,\"manifest\":\"/unused/Cargo.toml\",\"target\":\"/unused/target.noindex\"}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"seal\"}}\n").into_bytes(),
        format!("{{\"v\":1,\"epoch\":\"{EPOCH}\",\"op\":\"close\"}}\n").into_bytes(),
        format!("{{\"v\":2,\"epoch\":\"{EPOCH}\",\"op\":\"close\"}}\n").into_bytes(),
        format!("{{\"v\":3,\"epoch\":\"{EPOCH}\",\"op\":\"close\"}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"close\"}}\n").repeat(2).into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"finalize\"}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"finalize\",\"finalization\":\"{FINALIZATION}\"}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"cancel\",\"id\":0}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"cancel\",\"id\":1}}\n").into_bytes(),
        format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"cancel\",\"id\":0,\"unknown\":true}}\n").into_bytes(),
        vec![b'x'; FRAME + 1],
    ];
    for bytes in bad_frames {
        let mut fixture = Fixture::new();
        fixture.opened();
        let sent = fixture.helper.as_mut().unwrap().send(&bytes);
        if let Err(error) = sent {
            assert!(bytes.len() > FRAME && error.kind() == io::ErrorKind::BrokenPipe);
        }
        fixture.helper.as_mut().unwrap().refused();
        fixture.retained();
    }
}

#[test]
fn controller_eof_never_authorizes_retirement_or_endpoint_removal() {
    let mut fixture = Fixture::new();
    fixture.opened();
    fixture.helper.as_mut().unwrap().input.take();
    fixture.helper.as_mut().unwrap().refused();
    assert!(fixture.directory.join("credits.fifo").exists());
    fixture.retained();
}

#[test]
fn close_acknowledgement_without_finalize_cannot_turn_eof_into_retirement() {
    let mut fixture = Fixture::new();
    fixture.opened();
    let helper = fixture.helper.as_mut().unwrap();
    helper.request("close");
    helper.event("closing");
    assert!(helper.child.try_wait().unwrap().is_none());
    helper.input.take();
    helper.refused();
    assert!(fixture.directory.join("credits.fifo").exists());
    fixture.retained();
}

#[test]
fn full_blocking_stderr_cannot_prevent_actual_root_reap_after_refusal() {
    struct Release(PathBuf);
    impl Drop for Release {
        fn drop(&mut self) {
            // Only this fixture's known Rust root barrier is released, including
            // when its controller fails before the compiled body runs.
            let _ = fs::write(&self.0, b"owned root release\n");
        }
    }
    let mut fixture = Fixture::new();
    let world = fixture.world.path().to_owned();
    let package = world.join("root.noindex");
    fs::create_dir(&package).unwrap();
    fs::write(package.join("Cargo.toml"), b"[package]\nname='blocked_stderr_root'\nversion='0.0.0'\nedition='2024'\n[lib]\npath='lib.rs'\n[workspace]\n").unwrap();
    fs::write(
        package.join("lib.rs"),
        b"pub fn actual_root() -> u32 { 45 }\n",
    )
    .unwrap();
    fs::write(
        package.join("build.rs"),
        r#"
fn main() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::write(root.join("ready.pending"), format!("pid={}\n", std::process::id())).unwrap();
    std::fs::rename(root.join("ready.pending"), root.join("ready")).unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while !root.join("release").exists() {
        assert!(std::time::Instant::now() < deadline, "owned root was not released");
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    println!("cargo:rerun-if-changed=build.rs");
}
"#,
    )
    .unwrap();
    let release = Release(package.join("release"));
    let (mut stderr_reader, stderr_writer) = private_stderr_pipe();
    let mut stderr_log = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(world.join("helper.stderr"))
        .unwrap();
    fixture.helper = Some(Helper::start_with_stderr(
        &world,
        &fixture.directory,
        1,
        1,
        EPOCH,
        Some(stderr_writer.try_clone().unwrap()),
    ));
    let helper = fixture.helper.as_mut().unwrap();
    assert_eq!(helper.event("opened")["published"], 0);
    let target = world.join("target-root.noindex");
    let mut spawn = serde_json::to_vec(&json!({
        "v":4,"epoch":EPOCH,"op":"spawn","id":0,
        "manifest":package.join("Cargo.toml"),"target":target
    }))
    .unwrap();
    spawn.push(b'\n');
    helper.send(&spawn).unwrap();
    let spawned = helper.event("spawned");
    let root = libc::pid_t::try_from(spawned["pid"].as_u64().unwrap()).unwrap();
    assert!(root > 1);
    let mut capture_stderr = |deadline: Instant| {
        let mut bytes = [0; 4096];
        loop {
            assert!(Instant::now() < deadline, "private stderr drain timed out");
            match stderr_reader.read(&mut bytes) {
                Ok(0) => return true,
                Ok(count) => stderr_log.write_all(&bytes[..count]).unwrap(),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return false,
                Err(error) => panic!("private stderr drain failed: {error}"),
            }
        }
    };
    let deadline = Instant::now() + HANG;
    loop {
        assert!(
            !capture_stderr(deadline),
            "helper ended before root readiness"
        );
        if package.join("ready").exists() {
            break;
        }
        assert!(helper.child.try_wait().unwrap().is_none());
        assert!(
            Instant::now() < deadline,
            "actual Rust root never reached its barrier"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    let ready = fs::read_to_string(package.join("ready")).unwrap();
    assert!(ready.starts_with("pid=") && ready.ends_with('\n'));
    let filled = fill_then_restore_blocking_stderr(&stderr_writer);
    // Finalize before Close is invalid regardless of when this actual root
    // finishes. From this point until ESRCH, stderr remains full and unread.
    helper.request("finalize");
    let deadline = Instant::now() + HANG;
    loop {
        // Fatal refusal closes this original private input before diagnostics
        // or root drain. Incomplete probe bytes cannot become another frame
        // and obscure the first command's exact refusal reason.
        match helper.input.as_mut().unwrap().write(b"x") {
            Ok(1) => {}
            Ok(_) => panic!("private refusal probe made no progress"),
            Err(error) if error.kind() == io::ErrorKind::BrokenPipe => break,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
            Err(error) => panic!("private refusal probe failed: {error}"),
        }
        assert!(
            Instant::now() < deadline,
            "fatal refusal never closed its original input"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    assert!(helper.child.try_wait().unwrap().is_none());
    // SAFETY: this is the original positive Spawned root, queried without
    // delivering a signal; its still-held barrier has not been released.
    assert_eq!(unsafe { libc::kill(root, 0) }, 0);
    assert!(!release.0.exists());
    fs::write(&release.0, b"normal root completion\n").unwrap();
    let deadline = Instant::now() + HANG;
    loop {
        // SAFETY: root is the positive original Spawned PID. Signal zero only
        // queries it; a zombie still answers, so only ESRCH proves actual reap.
        if unsafe { libc::kill(root, 0) } != 0 {
            let error = io::Error::last_os_error();
            if error.raw_os_error() == Some(libc::ESRCH) {
                break;
            }
            assert!(
                matches!(error.raw_os_error(), Some(libc::EINTR) | Some(libc::EPERM)),
                "root presence query failed: {error}"
            );
        }
        assert!(
            Instant::now() < deadline,
            "full blocking stderr prevented actual root reap"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    assert!(target.join("debug/libblocked_stderr_root.rlib").is_file());
    fs::write(
        world.join("root-reaped-before-stderr-drain.json"),
        serde_json::to_vec(&json!({
            "original_root":root,"filled_stderr_bytes":filled,
            "blocking_restored_before_refusal":true,"root_esrch_before_stderr_drain":true,
            "fatal_input_broken_pipe_while_root_live":true,
            "actual_artifact_completed":true
        }))
        .unwrap(),
    )
    .unwrap();
    // Only after the helper has reaped its actual root may its ordinary final
    // CLI diagnostic make progress. No reader emptied the pipe before this.
    drop(stderr_writer);
    let deadline = Instant::now() + HANG;
    while !capture_stderr(deadline) {
        std::thread::sleep(Duration::from_millis(10));
    }
    helper.refused();
    assert!(
        fs::read_to_string(world.join("helper.stderr"))
            .unwrap()
            .contains("private epoch finalize requires Close and all owned roots reaped")
    );
    assert!(fixture.directory.join("credits.fifo").exists());
    fixture.retained();
}

#[test]
fn malformed_finalization_challenge_refuses_in_an_otherwise_eligible_phase() {
    for challenge in [
        Value::Null,
        json!("ABCDEF0123456789ABCDEF0123456789"),
        json!("0123456789abcdef0123456789abcde"),
        json!("gggggggggggggggggggggggggggggggg"),
    ] {
        let mut fixture = Fixture::new();
        fixture.opened();
        let helper = fixture.helper.as_mut().unwrap();
        helper.request("close");
        helper.event("closing");
        let mut frame = serde_json::to_vec(
            &json!({"v":4,"epoch":EPOCH,"op":"finalize","finalization":challenge}),
        )
        .unwrap();
        frame.push(b'\n');
        helper.send(&frame).unwrap();
        helper.refused();
        assert!(fixture.directory.join("credits.fifo").exists());
        fixture.retained();
    }
}

#[test]
fn duplicate_finalize_trailing_control_and_queued_eof_cannot_retire() {
    let mut finalize = serde_json::to_vec(
        &json!({"v":4,"epoch":EPOCH,"op":"finalize","finalization":FINALIZATION}),
    )
    .unwrap();
    finalize.push(b'\n');
    for (tail, eof) in [
        (finalize.clone(), false),
        (
            format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"close\"}}\n").into_bytes(),
            false,
        ),
        (b"{not json}\n".to_vec(), false),
        (
            format!("{{\"v\":4,\"epoch\":\"{EPOCH}\",\"op\":\"cancel\",\"id\":0}}\n").into_bytes(),
            false,
        ),
        (b"{".to_vec(), true),
        (Vec::new(), true),
    ] {
        let mut fixture = Fixture::with_units(2);
        fixture.start(2, 1, EPOCH);
        let helper = fixture.helper.as_mut().unwrap();
        let opened = helper.event("opened");
        assert_eq!(opened["published"], 1);
        let client =
            jobserver::Client::from_fifo(Path::new(opened["fifo"].as_str().unwrap())).unwrap();
        // Hold the one genuinely published P byte so no schedule can retire
        // between writing Finalize and queuing the negative tail or EOF.
        let withheld = client.try_acquire().unwrap().unwrap();
        assert!(client.try_acquire().unwrap().is_none());
        helper.request("close");
        helper.event("closing");
        let mut packet = finalize.clone();
        packet.extend(tail);
        // This complete packet is smaller than PIPE_BUF and goes through the
        // fixture's exclusively owned private pipe; no child output is input.
        assert!(packet.len() < 512);
        helper.send(&packet).unwrap();
        if eof {
            helper.input.take();
        }
        drop(withheld);
        helper.refused();
        assert!(
            client.available().unwrap() <= 1,
            "no extra P byte may be minted"
        );
        assert!(fixture.directory.join("credits.fifo").exists());
        drop(client);
        fixture.retained();
    }
}

#[test]
fn unexpected_surplus_token_prevents_retirement() {
    let mut fixture = Fixture::new();
    let opened = fixture.opened();
    let client = jobserver::Client::from_fifo(Path::new(opened["fifo"].as_str().unwrap())).unwrap();
    assert_eq!(client.available().unwrap(), 0);
    client.release_raw().unwrap();
    assert_eq!(client.available().unwrap(), 1);
    let helper = fixture.helper.as_mut().unwrap();
    helper.request("close");
    helper.event("closing");
    helper.request("finalize");
    helper.refused();
    assert!(fixture.directory.join("credits.fifo").exists());
    drop(client);
    fixture.retained();
}

#[test]
fn replaced_fifo_prevents_retirement_and_preserves_both_paths() {
    let mut fixture = Fixture::new();
    fixture.opened();
    let fifo = fixture.directory.join("credits.fifo");
    let old_fifo = fixture.directory.join("displaced.fifo");
    fs::rename(&fifo, &old_fifo).unwrap();
    fs::write(&fifo, b"preserve replacement").unwrap();
    fixture.helper.as_mut().unwrap().request("close");
    fixture.helper.as_mut().unwrap().refused();
    assert_eq!(fs::read(&fifo).unwrap(), b"preserve replacement");
    assert!(old_fifo.exists());
    fixture.retained();
}

#[test]
fn unsafe_or_missing_root_target_refuses_without_starting_a_root() {
    for kind in [
        "missing",
        "relative",
        "inside-epoch",
        "contains-epoch",
        "symlink",
        "parent-traversal",
        "public-parent",
    ] {
        let mut fixture = Fixture::new();
        fixture.opened();
        let package = fixture.world.path().join("package");
        fs::create_dir(&package).unwrap();
        fs::write(package.join("Cargo.toml"), b"[package]\nname='target-refusal'\nversion='0.1.0'\nedition='2024'\n[lib]\npath='lib.rs'\n[workspace]\n").unwrap();
        fs::write(package.join("lib.rs"), b"pub fn value() -> u32 { 1 }\n").unwrap();
        let protected = fixture.world.path().join("protected.noindex");
        fs::create_dir(&protected).unwrap();
        fs::write(protected.join("sentinel"), b"preserve").unwrap();
        let target = match kind {
            "missing" => None,
            "relative" => Some(PathBuf::from("relative.noindex")),
            "inside-epoch" => Some(fixture.directory.join("target.noindex")),
            "contains-epoch" => Some(fixture.world.path().to_path_buf()),
            "symlink" => {
                let alias = fixture.world.path().join("alias.noindex");
                symlink(&protected, &alias).unwrap();
                Some(alias)
            }
            "parent-traversal" => Some(protected.join("..").join("cache.noindex")),
            "public-parent" => {
                fs::set_permissions(&protected, fs::Permissions::from_mode(0o777)).unwrap();
                Some(protected.join("cache.noindex"))
            }
            _ => unreachable!(),
        };
        let mut request =
            json!({"v":4,"epoch":EPOCH,"op":"spawn","id":0,"manifest":package.join("Cargo.toml")});
        if let Some(target) = target {
            request["target"] = json!(target);
        }
        let mut bytes = serde_json::to_vec(&request).unwrap();
        bytes.push(b'\n');
        fixture.helper.as_mut().unwrap().send(&bytes).unwrap();
        fixture.helper.as_mut().unwrap().refused();
        assert!(
            fixture
                .helper
                .as_ref()
                .unwrap()
                .frames
                .iter()
                .all(|frame| frame["event"] != "spawned"),
            "{kind} started a root"
        );
        let stderr = fs::read_to_string(fixture.world.path().join("helper.stderr")).unwrap();
        assert!(
            stderr.contains("target"),
            "{kind} refused for the wrong reason: {stderr}"
        );
        assert_eq!(fs::read(protected.join("sentinel")).unwrap(), b"preserve");
        assert!(fixture.directory.join("credits.fifo").exists());
        fs::set_permissions(&protected, fs::Permissions::from_mode(0o700)).unwrap();
        fixture.retained();
    }
}

#[test]
fn invalid_counts_and_epoch_refuse_before_endpoint_creation() {
    for (backing, roots, epoch) in [
        (0, 1, EPOCH),
        (1, 2, EPOCH),
        (257, 1, EPOCH),
        (1, 1, "NOT-AN-EPOCH"),
    ] {
        let mut fixture = Fixture::new();
        fixture.start(backing, roots, epoch);
        fixture.helper.as_mut().unwrap().refused();
        assert!(fixture.helper.as_ref().unwrap().frames.is_empty());
        assert!(!fixture.directory.exists());
        fixture.retained();
    }
}

#[test]
fn existing_symlink_or_writable_parent_cannot_publish_an_endpoint() {
    for kind in ["existing", "symlink", "public-parent"] {
        let mut fixture = Fixture::new();
        let mut protected = None;
        match kind {
            "existing" => {
                fs::create_dir(&fixture.directory).unwrap();
                fs::write(fixture.directory.join("sentinel"), b"preserve").unwrap();
                protected = Some(fixture.directory.clone());
            }
            "symlink" => {
                let target = fixture.world.path().join("target.noindex");
                fs::create_dir(&target).unwrap();
                fs::write(target.join("sentinel"), b"preserve").unwrap();
                symlink(&target, &fixture.directory).unwrap();
                protected = Some(target);
            }
            "public-parent" => {
                let parent = fixture.world.path().join("public.noindex");
                fs::create_dir(&parent).unwrap();
                fs::set_permissions(&parent, fs::Permissions::from_mode(0o777)).unwrap();
                fixture.directory = parent.join("epoch.noindex");
            }
            _ => unreachable!(),
        }
        fixture.start(1, 1, EPOCH);
        fixture.helper.as_mut().unwrap().refused();
        assert!(fixture.helper.as_ref().unwrap().frames.is_empty());
        if let Some(path) = protected {
            assert_eq!(fs::read(path.join("sentinel")).unwrap(), b"preserve");
            assert!(!path.join("credits.fifo").exists());
        } else {
            assert!(!fixture.directory.exists());
            fs::set_permissions(
                fixture.directory.parent().unwrap(),
                fs::Permissions::from_mode(0o700),
            )
            .unwrap();
        }
        fixture.retained();
    }
}
