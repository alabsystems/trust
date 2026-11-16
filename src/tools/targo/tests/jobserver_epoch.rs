// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::collections::VecDeque;
use std::fs;
use std::io::{self, BufRead, Read, Write};
use std::num::NonZeroU32;
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};

use anyhow::{Context, ensure};
use jobserver::{Acquired, Client};
use serde_json::{Value, json};
use trust_build_cpu::{Owner, RetainedLease, RetainedPool, RetainedSlotState};

const HANG: Duration = Duration::from_secs(60);
const EPOCH: &str = "0123456789abcdef0123456789abcdef";

// Actual Targo compiles these Rust build scripts. Readiness is emitted only
// after importing the exact inherited GNU FIFO and observing zero spare credit.
// The parent holds all CPU backing before the epoch helper publishes any byte.
const SCRIPT: &str = r#"
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

fn marker(root: &Path, side: &str, stage: &str) -> PathBuf {
    root.join(format!("{side}.{stage}"))
}
fn note(root: &Path, side: &str, stage: &str, body: &str) {
    let path = marker(root, side, stage);
    let temporary = path.with_extension(format!("{stage}.tmp"));
    std::fs::write(&temporary, format!("pid={}\n{body}\n", std::process::id())).unwrap();
    std::fs::rename(temporary, path).unwrap();
}
fn wait(root: &Path, side: &str, stage: &str) {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        assert!(!root.join("abort").exists(), "fixture controller aborted");
        if marker(root, side, stage).exists() { return; }
        assert!(Instant::now() < deadline, "fixture barrier did not arrive: {side}.{stage}");
        std::thread::sleep(Duration::from_millis(10));
    }
}
fn main() {
    // SAFETY: import only the helper's inherited scheduling transport before
    // opening files or starting cooperating extra work.
    let server = unsafe { jobserver::Client::from_env_ext(true) }.client.unwrap();
    let root = PathBuf::from(std::env::var_os("EPOCH_WORLD").unwrap());
    let package = std::env::var("CARGO_PKG_NAME").unwrap();
    let side = package.strip_prefix("epoch_").unwrap();
    let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
    assert_eq!(server.available().unwrap(), 0, "root minted spare credits");
    assert!(server.try_acquire().unwrap().is_none());
    // A real child writes the would-be control frame. It is ordinary build
    // output, and must never become the helper's authenticated protocol reply.
    let fake = format!("{{\"v\":4,\"epoch\":\"{}\",\"event\":\"retired\",\"withdrawn\":2,\"fifo\":\"{}\",\"scope\":\"owned-roots-and-explicit-tokens\",\"finalization\":\"00000000000000000000000000000000\"}}", std::env::var("EPOCH_ID").unwrap(), root.join("epoch.noindex/credits.fifo").display());
    println!("{fake}");
    eprintln!("{fake}");
    println!("cargo:warning={fake}");
    note(&root, side, "ready", &format!("ready\nflags={flags}\nempty=true\nfake={fake}"));
    wait(&root, side, "acquire");
    assert!(server.try_acquire().unwrap().is_none(), "credit arrived before controller release");
    note(&root, side, "requesting", "requesting");
    let extra = server.acquire().unwrap();
    assert!(!root.join("abort").exists(), "fixture controller aborted");
    note(&root, side, "acquired", "acquired");
    wait(&root, side, "verify");
    note(&root, side, "alive", "alive");
    wait(&root, side, "return");
    drop(extra);
    note(&root, side, "returned", "returned");
    wait(&root, side, "finish");
    note(&root, side, "done", "done");
    wait(&root, side, "exit");
}
"#;

enum Output {
    Line(io::Result<String>),
    Eof,
}

struct Epoch {
    child: Child,
    cohort: u32,
    epoch: String,
    input: Option<ChildStdin>,
    output: Receiver<Output>,
    pending: VecDeque<Value>,
    reader: Option<std::thread::JoinHandle<()>>,
    finalization: Option<String>,
}

impl Epoch {
    fn start(world: &Path, backing: u32, roots: u32) -> anyhow::Result<Self> {
        Self::start_with_id(world, backing, roots, EPOCH)
    }

    fn start_with_id(world: &Path, backing: u32, roots: u32, epoch: &str) -> anyhow::Result<Self> {
        let child = helper_command_with_id(world, backing, roots, epoch)?
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        Self::attach_with_id(world, child, false, epoch)
    }

    #[cfg(target_os = "macos")]
    fn attach(world: &Path, child: Child, startup: bool) -> anyhow::Result<Self> {
        Self::attach_with_id(world, child, startup, EPOCH)
    }

    fn attach_with_id(
        world: &Path,
        mut child: Child,
        mut startup: bool,
        epoch: &str,
    ) -> anyhow::Result<Self> {
        let cohort = child.id();
        let expected_epoch = epoch.to_owned();
        let input = child.stdin.take();
        let stream = child
            .stdout
            .take()
            .context("helper control stdout missing")?;
        let mut protocol_log = fs::File::create(world.join("helper.stdout"))?;
        let (send, output) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            for line in io::BufReader::new(stream).lines() {
                let line = line.and_then(|text| {
                    writeln!(protocol_log, "{text}")?;
                    Ok(text)
                });
                if startup && let Ok(text) = &line {
                    let held = serde_json::from_str::<Value>(text).ok();
                    if !held.is_some_and(|frame| {
                        frame["v"] == 4
                            && frame["epoch"] == expected_epoch
                            && frame["event"] == "controller-held"
                            && frame["pid"] == cohort
                    }) {
                        continue;
                    }
                    startup = false;
                }
                if send.send(Output::Line(line)).is_err() {
                    return;
                }
            }
            let _ = send.send(Output::Eof);
        });
        Ok(Self {
            child,
            cohort,
            epoch: epoch.to_owned(),
            input,
            output,
            pending: VecDeque::new(),
            reader: Some(reader),
            finalization: None,
        })
    }

    fn send(&mut self, mut request: Value) -> anyhow::Result<()> {
        request["v"] = json!(4);
        request["epoch"] = json!(self.epoch);
        let input = self.input.as_mut().context("helper input already closed")?;
        serde_json::to_writer(&mut *input, &request)?;
        input.write_all(b"\n")?;
        input.flush()?;
        if request["op"] == "finalize" {
            self.finalization = Some(
                request["finalization"]
                    .as_str()
                    .context("fixture Finalize has no private challenge")?
                    .to_owned(),
            );
        }
        Ok(())
    }

    fn frame(&self, line: io::Result<String>) -> anyhow::Result<Value> {
        let line = line?;
        let frame: Value =
            serde_json::from_str(&line).context("non-protocol bytes on helper stdout")?;
        ensure!(
            frame["v"] == 4 && frame["epoch"] == self.epoch,
            "foreign helper control frame: {frame}"
        );
        if frame["event"] == "retired" {
            let expected = self
                .finalization
                .as_ref()
                .context("Retired preceded the controller's complete Finalize write")?;
            ensure!(
                frame["finalization"].as_str() == Some(expected.as_str()),
                "Retired did not answer the actual private Finalize challenge"
            );
        }
        let fields: &[&str] = match frame["event"].as_str() {
            Some("opened") => &["backing", "roots", "published", "fifo"],
            Some("spawned") => &["id", "pid"],
            Some("root-exit") => &["id", "pid", "code", "success"],
            Some("cancelled") => &["id", "pid", "state"],
            Some("closing") => &[],
            Some("retired") => &["withdrawn", "fifo", "scope", "finalization"],
            Some("controller-held") => &["pid", "backing"],
            Some("helper-spawned") => &["pid"],
            _ => anyhow::bail!("unexpected helper response: {frame}"),
        };
        let object = frame
            .as_object()
            .context("helper response is not an object")?;
        ensure!(
            object.len() == 3 + fields.len()
                && fields.iter().all(|name| object.contains_key(*name)),
            "helper response has missing or unknown fields: {frame}"
        );
        Ok(frame)
    }

    fn event(&mut self, expected: &str, id: Option<u64>) -> anyhow::Result<Value> {
        let matches =
            |frame: &Value| frame["event"] == expected && id.is_none_or(|id| frame["id"] == id);
        if let Some(position) = self.pending.iter().position(matches) {
            return Ok(self.pending.remove(position).unwrap());
        }
        let deadline = Instant::now() + HANG;
        loop {
            match self
                .output
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))?
            {
                Output::Line(line) => {
                    let frame = self.frame(line)?;
                    if matches(&frame) {
                        return Ok(frame);
                    }
                    self.pending.push_back(frame);
                }
                Output::Eof => anyhow::bail!("helper ended before {expected}"),
            }
        }
    }

    fn no_retired_frame(&mut self) -> anyhow::Result<()> {
        while let Ok(output) = self.output.try_recv() {
            match output {
                Output::Line(line) => {
                    let frame = self.frame(line)?;
                    self.pending.push_back(frame);
                }
                Output::Eof => anyhow::bail!("helper ended before explicit finalization"),
            }
        }
        ensure!(
            self.pending.iter().all(|frame| frame["event"] != "retired"),
            "child output or premature retirement forged Retired"
        );
        Ok(())
    }

    fn finalize(&mut self) -> anyhow::Result<()> {
        self.no_retired_frame()?;
        ensure!(self.finalization.is_none(), "fixture Finalize is one-use");
        // Mint this only at the actual finalization boundary. Earlier buffered
        // helper output and a build script's forged frame cannot predict it.
        // Exclude the build-script negative control's fixed all-zero value.
        let finalization = format!("{:032x}", rand::random::<u128>().max(1));
        self.send(json!({"op":"finalize", "finalization":finalization}))
    }

    fn finish(&mut self) -> anyhow::Result<()> {
        self.finish_status(true)
    }

    fn finish_status(&mut self, success: bool) -> anyhow::Result<()> {
        let deadline = Instant::now() + HANG;
        let status = loop {
            if let Some(status) = self.child.try_wait()? {
                break status;
            }
            ensure!(
                Instant::now() < deadline,
                "helper did not exit after retirement"
            );
            std::thread::sleep(Duration::from_millis(10));
        };
        ensure!(
            status.success() == success,
            "unexpected helper outcome: {status:?}"
        );
        if !success {
            ensure!(
                status.code() == Some(101),
                "helper refusal was not its actual error exit"
            );
        }
        self.finish_output()
    }

    fn finish_output(&mut self) -> anyhow::Result<()> {
        let deadline = Instant::now() + HANG;
        loop {
            match self
                .output
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))?
            {
                Output::Line(line) => {
                    let frame = self.frame(line)?;
                    self.pending.push_back(frame);
                }
                Output::Eof => break,
            }
        }
        self.reader
            .take()
            .unwrap()
            .join()
            .map_err(|_| anyhow::anyhow!("helper reader panicked"))?;
        self.input.take();
        Ok(())
    }
}

#[cfg(target_os = "macos")]
fn helper_command(world: &Path, backing: u32, roots: u32) -> anyhow::Result<Command> {
    helper_command_with_id(world, backing, roots, EPOCH)
}

fn helper_command_with_id(
    world: &Path,
    backing: u32,
    roots: u32,
    epoch: &str,
) -> anyhow::Result<Command> {
    let mut command = native_targo_command(world)?;
    command
        .args(["--unverified", "__resource-epoch", "--directory"])
        .arg(world.join("epoch.noindex"))
        .args([
            "--epoch",
            epoch,
            "--backing",
            &backing.to_string(),
            "--roots",
            &roots.to_string(),
        ])
        .env("EPOCH_ID", epoch)
        .stderr(Stdio::from(fs::File::create(world.join("helper.stderr"))?));
    Ok(command)
}

fn native_targo_command(world: &Path) -> anyhow::Result<Command> {
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .context("parent build has no Cargo cache location")?;
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .env_clear()
        .env("HOME", world.join("home"))
        .env("CARGO_HOME", cargo_home)
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").context("parent RUSTC missing")?,
        )
        .env(
            "PATH",
            std::env::var_os("PATH").context("parent PATH missing")?,
        )
        .env("EPOCH_WORLD", world)
        .process_group(0);
    Ok(command)
}

struct Endpoint {
    path: PathBuf,
    directory: fs::File,
    fifo: fs::File,
}

fn identity(metadata: &fs::Metadata) -> (u64, u64) {
    (metadata.dev(), metadata.ino())
}

impl Endpoint {
    fn capture(path: &Path) -> anyhow::Result<Self> {
        let directory = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path.parent().context("FIFO has no parent")?)?;
        let fifo = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)?;
        let endpoint = Self {
            path: path.to_owned(),
            directory,
            fifo,
        };
        endpoint.validate()?;
        Ok(endpoint)
    }

    fn validate(&self) -> anyhow::Result<()> {
        let directory = fs::symlink_metadata(self.path.parent().unwrap())?;
        let fifo = fs::symlink_metadata(&self.path)?;
        ensure!(
            directory.is_dir() && identity(&directory) == identity(&self.directory.metadata()?),
            "original FIFO directory identity changed"
        );
        ensure!(
            fifo.file_type().is_fifo()
                && fifo.nlink() == 1
                && identity(&fifo) == identity(&self.fifo.metadata()?),
            "original FIFO identity changed"
        );
        Ok(())
    }

    fn empty(&self) -> anyhow::Result<()> {
        self.validate()?;
        let imported = Client::from_fifo(&self.path)?;
        ensure!(
            imported.available()? == 0 && imported.try_acquire()?.is_none(),
            "retired FIFO is not empty"
        );
        Ok(())
    }

    fn cleanup(self, cohort: u32) -> anyhow::Result<()> {
        // Caller already observed the actual helper exit/EOF. Only a separate
        // kernel observation of the entire old group authorizes node removal.
        group_drained(cohort).with_context(|| {
            format!(
                "observe whole-group drain before removing {}",
                self.path.display()
            )
        })?;
        self.empty().with_context(|| {
            format!(
                "validate original empty FIFO before removing {}",
                self.path.display()
            )
        })?;
        let leaf = std::ffi::CString::new(self.path.file_name().unwrap().as_encoded_bytes())?;
        // SAFETY: use the original held directory descriptor and checked one
        // component, after validating both original inodes and actual drain.
        ensure!(
            unsafe { libc::unlinkat(self.directory.as_raw_fd(), leaf.as_ptr(), 0) } == 0,
            "controller FIFO unlink failed at {} after actual group drain: {}",
            self.path.display(),
            io::Error::last_os_error()
        );
        self.directory.sync_all().with_context(|| {
            format!(
                "sync original FIFO directory after removing {}",
                self.path.display()
            )
        })?;
        Ok(())
    }
}

fn group_drained(group: u32) -> anyhow::Result<()> {
    let group = libc::pid_t::try_from(group)?;
    let deadline = Instant::now() + HANG;
    let mut observation = "not yet observed".to_owned();
    loop {
        ensure!(
            Instant::now() < deadline,
            "actual helper group {group} did not drain within its hang detector; last observation: {observation}"
        );
        // SAFETY: signal zero only observes the known helper group. It never
        // sends a signal to any process, including if the number was reused.
        if unsafe { libc::kill(-group, 0) } < 0 {
            let error = io::Error::last_os_error();
            if error.raw_os_error() == Some(libc::ESRCH) {
                return Ok(());
            }
            match error.raw_os_error() {
                Some(libc::EINTR) => continue,
                Some(libc::EPERM) => observation = format!("unknown/present: {error}"),
                _ => {
                    return Err(error)
                        .with_context(|| format!("observe original helper group {group}"));
                }
            }
        } else {
            observation = "group still present".to_owned();
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

struct Execution {
    world: Option<tempfile::TempDir>,
    epoch: Option<Epoch>,
    direct_root: Option<Child>,
    server: Option<Client>,
    withheld: Vec<Acquired>,
    backing: Vec<RetainedLease>,
    passed: bool,
}

impl Execution {
    fn new() -> anyhow::Result<Self> {
        let base = Path::new("/tmp/.ubd/targo-retained-epoch.noindex");
        fs::create_dir_all(base)?;
        Ok(Self {
            world: Some(tempfile::tempdir_in(base)?),
            epoch: None,
            direct_root: None,
            server: None,
            withheld: Vec::new(),
            backing: Vec::new(),
            passed: false,
        })
    }

    fn path(&self) -> &Path {
        self.world.as_ref().unwrap().path()
    }

    fn release(&self, side: &str, stage: &str) -> io::Result<()> {
        let path = self.path().join(format!("{side}.{stage}"));
        let temporary = path.with_extension(format!("{stage}.tmp"));
        fs::write(&temporary, b"controller release\n")?;
        fs::rename(temporary, path)
    }

    fn note(&self, side: &str, stage: &str) -> anyhow::Result<String> {
        let deadline = Instant::now() + HANG;
        loop {
            match fs::read_to_string(self.path().join(format!("{side}.{stage}"))) {
                Ok(note) => return Ok(note),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
            ensure!(
                Instant::now() < deadline,
                "missing {side}.{stage}; evidence {}",
                self.path().display()
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn stage(&self, side: &str, stage: &str, pid: u32) -> anyhow::Result<()> {
        ensure!(self.note(side, stage)? == format!("pid={pid}\n{stage}\n"));
        Ok(())
    }
}

impl Drop for Execution {
    fn drop(&mut self) {
        if !self.passed {
            let _ = fs::write(self.path().join("abort"), b"fixture cleanup\n");
            for side in ["a", "b", "probe", "a_left", "a_right", "b_left", "b_right"] {
                for stage in [
                    "acquire", "verify", "return", "finish", "exit", "import", "release",
                ] {
                    let _ = fs::write(self.path().join(format!("{side}.{stage}")), b"cleanup\n");
                }
            }
            self.withheld.clear();
        }
        if let Some(root) = self.direct_root.as_mut() {
            let deadline = Instant::now() + HANG;
            while matches!(root.try_wait(), Ok(None)) && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            if matches!(root.try_wait(), Ok(None)) {
                // Only this actual owned direct Child is signalled. Its scripts
                // already received the fixture's normal abort/release above.
                let _ = root.kill();
                let _ = root.wait();
            }
        }
        if let Some(epoch) = self.epoch.as_mut() {
            if epoch.reader.is_some() {
                // EOF asks the helper to refuse completion and retain custody
                // while controlled roots observe the released abort barriers.
                epoch.input.take();
                let deadline = Instant::now() + HANG;
                while matches!(epoch.child.try_wait(), Ok(None)) && Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(10));
                }
                if matches!(epoch.child.try_wait(), Ok(None)) {
                    // Only the original direct Child is signalled. Descendants
                    // receive the controlled barrier/EOF cleanup above.
                    let _ = epoch.child.kill();
                    let _ = epoch.child.wait();
                }
                let deadline = Instant::now() + HANG;
                loop {
                    match epoch
                        .output
                        .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                    {
                        Ok(Output::Line(_)) => {}
                        Ok(Output::Eof) | Err(mpsc::RecvTimeoutError::Disconnected) => {
                            let _ = epoch.reader.take().unwrap().join();
                            break;
                        }
                        Err(mpsc::RecvTimeoutError::Timeout) => break,
                    }
                }
            }
            if !self.passed {
                let _ = group_drained(epoch.cohort);
            }
        }
        if !self.passed {
            eprintln!(
                "kept failed retained-epoch world: {}",
                self.world.take().unwrap().keep().display()
            );
        }
    }
}

fn prepare(root: &Path, jobserver: &Path, side: &str) -> anyhow::Result<()> {
    prepare_script(root, jobserver, side, SCRIPT)
}

fn prepare_script(root: &Path, jobserver: &Path, side: &str, script: &str) -> anyhow::Result<()> {
    fs::create_dir_all(root.join("src"))?;
    let jobserver =
        serde_json::to_string(jobserver.to_str().context("jobserver path is not UTF-8")?)?;
    fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname='epoch_{side}'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[build-dependencies]\njobserver={{path={jobserver}}}\n"
        ),
    )?;
    fs::write(root.join("build.rs"), script)?;
    fs::write(
        root.join("src/main.rs"),
        "fn main() { assert_eq!((0..10).sum::<u64>(), 45); }\n",
    )?;
    Ok(())
}

fn ready(note: &str, fifo: &Path) -> anyhow::Result<u32> {
    let pid = note
        .lines()
        .next()
        .and_then(|line| line.strip_prefix("pid="))
        .context("actual build-script readiness PID missing")?
        .parse::<u32>()?;
    ensure!(pid != 0);
    ensure!(note.contains(&format!("--jobserver-auth=fifo:{}", fifo.display())));
    ensure!(note.contains("\nempty=true\n"));
    ensure!(note.contains(&format!("\"epoch\":\"{EPOCH}\",\"event\":\"retired\"")));
    Ok(pid)
}

fn assert_no_cpu(pool: &RetainedPool) -> anyhow::Result<()> {
    ensure!(pool.try_acquire(Owner::current(None))?.is_none());
    ensure!(
        pool.snapshot()?
            .iter()
            .all(|slot| !matches!(slot, RetainedSlotState::Available { .. }))
    );
    Ok(())
}

// These jobs never import the jobserver or acquire a token themselves. Two
// simultaneous native CustomBuild children require the real Targo driver to
// retain an Acquired guard in addition to that root's implicit unit.
const DRIVER_BARRIER_SCRIPT: &str = r#"
use std::{path::PathBuf, time::{Duration, Instant}};
unsafe extern "C" { fn getppid() -> i32; }
fn note(root:&std::path::Path, unit:&str, stage:&str, nonce:&str) {
    let path=root.join(format!("{unit}.{stage}"));
    let temporary=path.with_extension(format!("{stage}.pending"));
    // SAFETY: getppid only reads this actual running process's parent.
    let parent=unsafe{getppid()};
    std::fs::write(&temporary,format!("pid={}\nppid={parent}\nunit={unit}\nnonce={nonce}\n",std::process::id())).unwrap();
    std::fs::rename(temporary,path).unwrap();
}
fn main() {
    let root=PathBuf::from(std::env::var_os("EPOCH_WORLD").unwrap());
    let package=std::env::var("CARGO_PKG_NAME").unwrap();
    let unit=package.strip_prefix("cancel_").unwrap();
    println!("cargo:rerun-if-env-changed=EPOCH_WORLD");
    note(&root,unit,"ready","");
    let deadline=Instant::now()+Duration::from_secs(60);
    while !root.join(format!("{unit}.release")).exists() {
        if root.join("abort").exists() { return; }
        for stage in ["before-cancel","after-cancel","peer-progress"] {
            let request=root.join(format!("{unit}.{stage}.request"));
            if request.exists() && !root.join(format!("{unit}.{stage}")).exists() {
                let nonce=std::fs::read_to_string(request).unwrap();
                note(&root,unit,stage,&nonce);
            }
        }
        assert!(Instant::now()<deadline,"driver unit was not released: {unit}");
        std::thread::sleep(Duration::from_millis(10));
    }
    note(&root,unit,"done","");
    println!("cargo:rerun-if-changed=build.rs");
}
"#;

fn prepare_driver_project(root: &Path, side: &str) -> anyhow::Result<()> {
    fs::create_dir_all(root.join("src"))?;
    fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname='cancel_{side}'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[build-dependencies]\ncancel_{side}_left={{path='left'}}\ncancel_{side}_right={{path='right'}}\n"
        ),
    )?;
    fs::write(
        root.join("src/main.rs"),
        "fn main(){println!(\"peer-artifact-ok\");}\n",
    )?;
    // Both dependencies must finish before this execution marker is possible.
    // For A it must remain absent even after every active child returns success.
    fs::write(
        root.join("build.rs"),
        format!(
            "fn main(){{ println!(\"cargo:rerun-if-env-changed=EPOCH_WORLD\"); assert_eq!(cancel_{side}_left::value()+cancel_{side}_right::value(),2); let root=std::path::PathBuf::from(std::env::var_os(\"EPOCH_WORLD\").unwrap()); std::fs::write(root.join(\"{side}.dependent\"),b\"actual dependent body\\n\").unwrap(); }}\n"
        ),
    )?;
    for leaf in ["left", "right"] {
        let path = root.join(leaf);
        fs::create_dir(&path)?;
        fs::write(
            path.join("Cargo.toml"),
            format!(
                "[package]\nname='cancel_{side}_{leaf}'\nversion='0.0.0'\nedition='2024'\n[lib]\npath='lib.rs'\n"
            ),
        )?;
        fs::write(path.join("lib.rs"), "pub fn value()->u32{1}\n")?;
        fs::write(path.join("build.rs"), DRIVER_BARRIER_SCRIPT)?;
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NativeProcess {
    pid: u32,
    parent: u32,
    birth: u128,
}

#[cfg(target_os = "linux")]
fn live_process(pid: u32) -> anyhow::Result<NativeProcess> {
    let stat = fs::read_to_string(format!("/proc/{pid}/stat"))?;
    let (head, rest) = stat
        .rsplit_once(')')
        .context("native stat has no command end")?;
    ensure!(
        head.split('(')
            .next()
            .context("native PID missing")?
            .trim()
            .parse::<u32>()?
            == pid
    );
    let fields: Vec<_> = rest.split_whitespace().collect();
    let state = *fields.first().context("native process state missing")?;
    ensure!(!matches!(state, "Z" | "X" | "x"), "native process exited");
    Ok(NativeProcess {
        pid,
        parent: fields.get(1).context("native parent missing")?.parse()?,
        birth: fields.get(19).context("native birth missing")?.parse()?,
    })
}

#[cfg(target_os = "macos")]
fn live_process(pid: u32) -> anyhow::Result<NativeProcess> {
    unsafe extern "C" {
        fn proc_pidinfo(
            pid: i32,
            flavor: i32,
            arg: u64,
            buffer: *mut std::ffi::c_void,
            size: i32,
        ) -> i32;
    }
    let pid_number = i32::try_from(pid)?;
    ensure!(pid_number > 1);
    let mut info = [0u8; 136];
    // SAFETY: PROC_PIDTBSDINFO fills exactly this writable 136-byte record for
    // the known positive PID, without changing or signalling any process.
    ensure!(
        unsafe { proc_pidinfo(pid_number, 3, 0, info.as_mut_ptr().cast(), 136) } == 136,
        "native process birth unavailable"
    );
    let u32_at = |at| u32::from_ne_bytes(info[at..at + 4].try_into().unwrap());
    let u64_at = |at| u64::from_ne_bytes(info[at..at + 8].try_into().unwrap());
    ensure!(
        u32_at(12) == pid && u32_at(4) != 5,
        "native process changed or exited"
    );
    Ok(NativeProcess {
        pid,
        parent: u32_at(16),
        birth: (u128::from(u64_at(120)) << 64) | u128::from(u64_at(128)),
    })
}

fn original_driver_parentage(unit: NativeProcess, driver: NativeProcess) -> anyhow::Result<()> {
    ensure!(live_process(unit.pid)? == unit && live_process(driver.pid)? == driver);
    let mut current = unit;
    for _ in 0..16 {
        if current.parent == driver.pid {
            return Ok(());
        }
        ensure!(
            current.parent > 1 && current.parent != current.pid,
            "unit escaped its actual driver"
        );
        current = live_process(current.parent)?;
    }
    anyhow::bail!("unit has no original driver in its native ancestry")
}

fn driver_ready(
    execution: &Execution,
    name: &str,
    driver: NativeProcess,
) -> anyhow::Result<NativeProcess> {
    let note = execution.note(name, "ready")?;
    let number = |prefix: &str| -> anyhow::Result<u32> {
        Ok(note
            .lines()
            .find_map(|line| line.strip_prefix(prefix))
            .context("unit identity missing")?
            .parse()?)
    };
    let unit = live_process(number("pid=")?)?;
    ensure!(unit.parent == number("ppid=")?);
    ensure!(note.lines().any(|line| line == format!("unit={name}")));
    original_driver_parentage(unit, driver)?;
    Ok(unit)
}

fn first_driver_unit(
    execution: &Execution,
    side: &str,
    driver: NativeProcess,
) -> anyhow::Result<(&'static str, NativeProcess)> {
    let deadline = Instant::now() + HANG;
    loop {
        for leaf in ["left", "right"] {
            let name = format!("{side}_{leaf}");
            if execution.path().join(format!("{name}.ready")).exists() {
                return Ok((leaf, driver_ready(execution, &name, driver)?));
            }
        }
        ensure!(
            Instant::now() < deadline,
            "first actual {side} driver unit did not run"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn challenge_driver_unit(
    execution: &Execution,
    name: &str,
    stage: &str,
    unit: NativeProcess,
    driver: NativeProcess,
) -> anyhow::Result<()> {
    let nonce = format!("{:032x}", rand::random::<u128>());
    let path = execution.path().join(format!("{name}.{stage}.request"));
    let temporary = path.with_extension("request.pending");
    fs::write(&temporary, &nonce)?;
    fs::rename(temporary, path)?;
    let response = execution.note(name, stage)?;
    ensure!(
        response
            .lines()
            .any(|line| line == format!("nonce={nonce}"))
    );
    ensure!(response.starts_with(&format!("pid={}\nppid={}\n", unit.pid, unit.parent)));
    original_driver_parentage(unit, driver)
}

#[test]
fn actual_roots_share_backed_epoch_and_only_complete_drain_can_return_cpu() -> anyhow::Result<()> {
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(4).unwrap())?;
    for _ in 0..4 {
        execution.backing.push(
            pool.try_acquire(Owner::current(None))?
                .context("missing initial CPU unit")?,
        );
    }
    assert_no_cpu(&pool)?;
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    for side in ["a", "b"] {
        prepare(&world.join(side), &jobserver, side)?;
    }
    // All four original capabilities are already held when the helper starts:
    // R=2 implicit roots plus exactly P=N-R=2 explicit reusable FIFO credits.
    execution.epoch = Some(Epoch::start(&world, 4, 2)?);
    let opened = execution.epoch.as_mut().unwrap().event("opened", None)?;
    ensure!(opened["backing"] == 4 && opened["roots"] == 2 && opened["published"] == 2);
    let fifo = PathBuf::from(opened["fifo"].as_str().context("opened reply lacks FIFO")?);
    ensure!(fifo == world.join("epoch.noindex/credits.fifo"));
    ensure!(fs::symlink_metadata(&fifo)?.file_type().is_fifo());
    let endpoint = Endpoint::capture(&fifo)?;
    execution.server = Some(Client::from_fifo(&fifo)?);
    ensure!(execution.server.as_ref().unwrap().available()? == 2);
    for _ in 0..2 {
        execution.withheld.push(
            execution
                .server
                .as_ref()
                .unwrap()
                .try_acquire()?
                .context("missing explicit credit")?,
        );
    }
    ensure!(execution.server.as_ref().unwrap().try_acquire()?.is_none());
    for (id, side) in [(0, "a"), (1, "b")] {
        let epoch = execution.epoch.as_mut().unwrap();
        epoch
            .send(json!({"op":"spawn", "id":id, "manifest":world.join(side).join("Cargo.toml"), "target":world.join(format!("target-{side}.noindex"))}))?;
        let spawned = epoch.event("spawned", Some(id))?;
        ensure!(
            spawned["pid"]
                .as_u64()
                .is_some_and(|pid| pid != 0 && pid != u64::from(epoch.child.id()))
        );
    }
    let a = ready(&execution.note("a", "ready")?, &fifo)?;
    let b = ready(&execution.note("b", "ready")?, &fifo)?;
    ensure!(a != b);
    execution.release("a", "acquire")?;
    execution.stage("a", "requesting", a)?;
    drop(execution.withheld.pop().unwrap());
    execution.stage("a", "acquired", a)?;
    ensure!(execution.server.as_ref().unwrap().available()? == 0);
    execution.release("b", "acquire")?;
    execution.stage("b", "requesting", b)?;
    ensure!(!world.join("b.acquired").exists());
    execution.release("a", "verify")?;
    execution.stage("a", "alive", a)?;
    execution.release("a", "return")?;
    execution.stage("a", "returned", a)?;
    execution.stage("b", "acquired", b)?;
    ensure!(execution.server.as_ref().unwrap().available()? == 0);
    execution.release("a", "finish")?;
    execution.stage("a", "done", a)?;
    execution.release("a", "exit")?;
    let exited = execution
        .epoch
        .as_mut()
        .unwrap()
        .event("root-exit", Some(0))?;
    ensure!(exited["success"] == true && exited["code"] == 0);
    // B proves it is still executing after A's actual Targo root was reaped.
    execution.release("b", "verify")?;
    execution.stage("b", "alive", b)?;
    assert_no_cpu(&pool)?;

    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"close"}))?;
    epoch.event("closing", None)?;
    epoch.no_retired_frame()?;
    ensure!(fs::symlink_metadata(&fifo)?.file_type().is_fifo());

    execution.release("b", "return")?;
    execution.stage("b", "returned", b)?;
    execution.withheld.clear();
    // Even with every explicit byte returned, the still-live root must be able
    // to import this same FIFO; removal would permit fallback to a private pool.
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.no_retired_frame()?;
    ensure!(fs::symlink_metadata(&fifo)?.file_type().is_fifo());
    execution.release("b", "finish")?;
    execution.stage("b", "done", b)?;
    assert_no_cpu(&pool)?;
    execution.release("b", "exit")?;
    let epoch = execution.epoch.as_mut().unwrap();
    let exited = epoch.event("root-exit", Some(1))?;
    ensure!(exited["success"] == true && exited["code"] == 0);
    ensure!(epoch.child.try_wait()?.is_none());
    // Close, all returned credits and actual root reaps still leave this
    // private command pipe live. Only our next valid Finalize authorizes Retired.
    epoch.finalize()?;
    let retired = epoch.event("retired", None)?;
    ensure!(retired["withdrawn"] == 2 && retired["fifo"] == fifo.to_str().unwrap());
    ensure!(retired["scope"] == "owned-roots-and-explicit-tokens");
    endpoint.empty()?;
    execution.server.take();
    assert_no_cpu(&pool)?;
    execution.epoch.as_mut().unwrap().finish()?;
    endpoint.cleanup(execution.epoch.as_ref().unwrap().cohort)?;
    ensure!(fs::symlink_metadata(&fifo).unwrap_err().kind() == io::ErrorKind::NotFound);
    // Only actual helper exit, whole-group drain, and identity-checked durable
    // node cleanup permit settlement of the original N capabilities.
    for capability in execution.backing.drain(..) {
        capability.settle()?;
    }
    ensure!(
        pool.snapshot()?
            .iter()
            .all(|slot| matches!(slot, RetainedSlotState::Available { .. }))
    );
    let mut restored = Vec::new();
    for _ in 0..4 {
        restored.push(
            pool.try_acquire(Owner::current(None))?
                .context("backing unit was not restored")?,
        );
    }
    assert_no_cpu(&pool)?;
    for capability in restored {
        capability.settle()?;
    }
    let fake = format!(
        "{{\"v\":4,\"epoch\":\"{EPOCH}\",\"event\":\"retired\",\"withdrawn\":2,\"fifo\":\"{}\",\"scope\":\"owned-roots-and-explicit-tokens\",\"finalization\":\"00000000000000000000000000000000\"}}",
        fifo.display()
    );
    for id in [0, 1] {
        let stderr = fs::read_to_string(world.join(format!("epoch.noindex/root-{id}.stderr")))?;
        ensure!(
            stderr.contains(&fake),
            "actual child fake frame missing from root log"
        );
    }
    execution.passed = true;
    Ok(())
}

#[test]
fn cooperative_cancel_returns_a_real_driver_guard_without_stopping_its_peer() -> anyhow::Result<()>
{
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(3).unwrap())?;
    for _ in 0..3 {
        execution.backing.push(
            pool.try_acquire(Owner::current(None))?
                .context("missing original N=3 backing")?,
        );
    }
    assert_no_cpu(&pool)?;
    for side in ["a", "b"] {
        prepare_driver_project(&world.join(side), side)?;
    }
    execution.epoch = Some(Epoch::start(&world, 3, 2)?);
    let epoch = execution.epoch.as_mut().unwrap();
    let opened = epoch.event("opened", None)?;
    ensure!(opened["backing"] == 3 && opened["roots"] == 2 && opened["published"] == 1);
    let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
    let endpoint = Endpoint::capture(&fifo)?;
    execution.server = Some(Client::from_fifo(&fifo)?);
    execution.withheld.push(
        execution
            .server
            .as_ref()
            .unwrap()
            .try_acquire()?
            .context("sole P byte missing")?,
    );
    ensure!(execution.server.as_ref().unwrap().try_acquire()?.is_none());

    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"spawn","id":0,"manifest":world.join("a/Cargo.toml"),"target":world.join("target-a.noindex")}))?;
    let spawned_a = epoch.event("spawned", Some(0))?;
    let driver_a = live_process(u32::try_from(
        spawned_a["pid"]
            .as_u64()
            .context("actual A driver missing")?,
    )?)?;
    let (first_a, _) = first_driver_unit(&execution, "a", driver_a)?;
    let other_a = if first_a == "left" { "right" } else { "left" };
    ensure!(!world.join(format!("a_{other_a}.ready")).exists());
    // Only A can borrow the released P byte. Its two actual script bodies do
    // not touch the jobserver, so their overlap witnesses a real driver guard.
    execution.withheld.clear();
    let a_left = driver_ready(&execution, "a_left", driver_a)?;
    let a_right = driver_ready(&execution, "a_right", driver_a)?;
    ensure!(a_left.pid != a_right.pid);
    original_driver_parentage(a_left, driver_a)?;
    ensure!(execution.server.as_ref().unwrap().available()? == 0);

    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"spawn","id":1,"manifest":world.join("b/Cargo.toml"),"target":world.join("target-b.noindex")}))?;
    let spawned_b = epoch.event("spawned", Some(1))?;
    let driver_b = live_process(u32::try_from(
        spawned_b["pid"]
            .as_u64()
            .context("actual B driver missing")?,
    )?)?;
    let (first_b, b_first) = first_driver_unit(&execution, "b", driver_b)?;
    let other_b = if first_b == "left" { "right" } else { "left" };
    let first_b_name = format!("b_{first_b}");
    let other_b_name = format!("b_{other_b}");
    challenge_driver_unit(
        &execution,
        &first_b_name,
        "before-cancel",
        b_first,
        driver_b,
    )?;
    ensure!(!world.join(format!("{other_b_name}.ready")).exists());
    ensure!(execution.server.as_ref().unwrap().try_acquire()?.is_none());
    assert_no_cpu(&pool)?;
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"cancel","id":0}))?;
    let cancelled = epoch.event("cancelled", Some(0))?;
    ensure!(cancelled["pid"] == driver_a.pid && cancelled["state"] == "stopped");
    // The original driver's sticky gate acknowledged before these still-live
    // active bodies were released; cancellation never kills the peer's group.
    challenge_driver_unit(&execution, "a_left", "after-cancel", a_left, driver_a)?;
    challenge_driver_unit(&execution, "a_right", "after-cancel", a_right, driver_a)?;
    challenge_driver_unit(&execution, &first_b_name, "after-cancel", b_first, driver_b)?;
    ensure!(!world.join("a.dependent").exists());
    ensure!(!world.join(format!("{other_b_name}.ready")).exists());
    execution
        .epoch
        .as_mut()
        .unwrap()
        .send(json!({"op":"cancel","id":0}))?;
    fs::write(
        world.join("driver-held-before-cancel.json"),
        serde_json::to_vec_pretty(&json!({
            "backing":3,"roots":2,"published":1,"driver_a":driver_a.pid,"driver_a_birth":driver_a.birth.to_string(),
            "a_left":a_left.pid,"a_left_birth":a_left.birth.to_string(),"a_right":a_right.pid,"a_right_birth":a_right.birth.to_string(),
            "driver_b":driver_b.pid,"driver_b_birth":driver_b.birth.to_string(),"b_implicit_unit":b_first.pid,
            "actual_driver_guard":true,"active_scripts_acquire_no_jobserver_credit":true,"cancel_ack_before_active_release":true
        }))?,
    )?;
    execution.release("a_left", "release")?;
    execution.release("a_right", "release")?;
    let b_second = driver_ready(&execution, &other_b_name, driver_b)?;
    ensure!(b_first.pid != b_second.pid);
    challenge_driver_unit(
        &execution,
        &first_b_name,
        "peer-progress",
        b_first,
        driver_b,
    )?;
    ensure!(execution.server.as_ref().unwrap().available()? == 0);
    let epoch = execution.epoch.as_mut().unwrap();
    let exited_a = epoch.event("root-exit", Some(0))?;
    ensure!(
        exited_a["pid"] == driver_a.pid && exited_a["success"] == false && exited_a["code"] == 101
    );
    ensure!(!world.join("a.dependent").exists());
    ensure!(!world.join("target-a.noindex/debug/cancel_a").exists());
    epoch.no_retired_frame()?;
    assert_no_cpu(&pool)?;

    // Do not Close before B borrows the returned guard: Close itself withdraws
    // P. Only now seal births while B's original two active bodies remain live.
    epoch.send(json!({"op":"close"}))?;
    epoch.event("closing", None)?;
    epoch.no_retired_frame()?;
    original_driver_parentage(b_first, driver_b)?;
    original_driver_parentage(b_second, driver_b)?;
    execution.release("b_left", "release")?;
    execution.release("b_right", "release")?;
    let epoch = execution.epoch.as_mut().unwrap();
    let exited_b = epoch.event("root-exit", Some(1))?;
    ensure!(
        exited_b["pid"] == driver_b.pid && exited_b["success"] == true && exited_b["code"] == 0
    );
    ensure!(world.join("b.dependent").is_file());
    // A first cancellation after actual completion is a distinct truthful
    // receipt, and remains valid during Closing without altering RootExit.
    epoch.send(json!({"op":"cancel","id":1}))?;
    let already = epoch.event("cancelled", Some(1))?;
    ensure!(already["pid"] == driver_b.pid && already["state"] == "already-exited");
    epoch.no_retired_frame()?;
    assert_no_cpu(&pool)?;
    epoch.finalize()?;
    let retired = epoch.event("retired", None)?;
    ensure!(retired["withdrawn"] == 1 && retired["fifo"] == fifo.to_str().unwrap());
    endpoint.empty()?;
    execution.server.take();
    epoch.finish()?;
    ensure!(
        epoch.pending.is_empty(),
        "repeated Cancel duplicated a receipt or manufactured a frame"
    );
    endpoint.cleanup(epoch.cohort)?;
    assert_no_cpu(&pool)?;
    for capability in execution.backing.drain(..) {
        capability.settle()?;
    }
    let mut restored = Vec::new();
    for _ in 0..3 {
        restored.push(
            pool.try_acquire(Owner::current(None))?
                .context("original N=3 was not restored")?,
        );
    }
    assert_no_cpu(&pool)?;
    for capability in restored {
        capability.settle()?;
    }
    execute_artifact_with_output(
        &world.join("target-b.noindex/debug/cancel_b"),
        &world,
        b"peer-artifact-ok\n",
    )?;
    execution.passed = true;
    Ok(())
}

#[test]
fn managed_root_cancellation_stops_new_work_even_with_keep_going() -> anyhow::Result<()> {
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    prepare_driver_project(&world.join("a"), "a")?;
    let fifo = world.join("direct-root.fifo");
    let path = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes())?;
    // SAFETY: this terminated pathname is inside our original private world;
    // no node exists here yet. Only this direct fixture seeds its one byte.
    ensure!(
        unsafe { libc::mkfifo(path.as_ptr(), 0o600) } == 0,
        "create direct root FIFO: {}",
        io::Error::last_os_error()
    );
    let server = Client::from_fifo(&fifo)?;
    ensure!(server.available()? == 0);
    server.release_raw()?;
    execution.withheld.push(
        server
            .try_acquire()?
            .context("direct root's sole explicit credit missing")?,
    );
    ensure!(server.try_acquire()?.is_none());
    let (mut control, root_control) = UnixStream::pair()?;
    control.set_read_timeout(Some(HANG))?;
    control.set_write_timeout(Some(HANG))?;
    let mut command = native_targo_command(&world)?;
    command
        .args([
            "--unverified",
            "build",
            "--offline",
            "--keep-going",
            "--__resource-root-control",
            "--manifest-path",
        ])
        .arg(world.join("a/Cargo.toml"))
        .arg("--target-dir")
        .arg(world.join("target-a.noindex"))
        .stdin(Stdio::from(OwnedFd::from(root_control)))
        .stdout(Stdio::from(fs::File::create(world.join("root.stdout"))?))
        .stderr(Stdio::from(fs::File::create(world.join("root.stderr"))?));
    server.configure(&mut command);
    execution.direct_root = Some(command.spawn()?);
    // Command retains its configured Stdio; release the parent's duplicate so
    // only the actual root owns that endpoint while the socket is challenged.
    drop(command);
    let driver = live_process(execution.direct_root.as_ref().unwrap().id())?;
    let (first, _) = first_driver_unit(&execution, "a", driver)?;
    let other = if first == "left" { "right" } else { "left" };
    ensure!(!world.join(format!("a_{other}.ready")).exists());
    execution.withheld.clear();
    let left = driver_ready(&execution, "a_left", driver)?;
    let right = driver_ready(&execution, "a_right", driver)?;
    ensure!(left.pid != right.pid && server.available()? == 0);
    ensure!(!world.join("a.dependent").exists());

    control.write_all(b"C")?;
    let mut acknowledgement = [0u8; 1];
    control.read_exact(&mut acknowledgement)?;
    ensure!(
        acknowledgement == *b"A",
        "actual driver did not acknowledge its stop gate"
    );
    // Neither active child fails: --keep-going would otherwise launch the
    // newly eligible dependent unless the actual driver has a separate stop.
    challenge_driver_unit(&execution, "a_left", "after-cancel", left, driver)?;
    challenge_driver_unit(&execution, "a_right", "after-cancel", right, driver)?;
    ensure!(!world.join("a.dependent").exists());
    execution.release("a_left", "release")?;
    execution.release("a_right", "release")?;
    let deadline = Instant::now() + HANG;
    let outcome = loop {
        if let Some(outcome) = execution.direct_root.as_mut().unwrap().try_wait()? {
            break outcome;
        }
        ensure!(
            Instant::now() < deadline,
            "cancelled --keep-going root did not drain"
        );
        std::thread::sleep(Duration::from_millis(10));
    };
    ensure!(
        outcome.code() == Some(101),
        "cancelled --keep-going root falsely succeeded: {outcome:?}"
    );
    for unit in ["a_left", "a_right"] {
        ensure!(
            execution
                .note(unit, "done")?
                .contains(&format!("unit={unit}\n"))
        );
    }
    ensure!(!world.join("a.dependent").exists());
    ensure!(!world.join("target-a.noindex/debug/cancel_a").exists());
    group_drained(execution.direct_root.as_ref().unwrap().id())?;
    execution.direct_root.take();
    let returned = server
        .try_acquire()?
        .context("cancelled --keep-going driver retained its original explicit credit")?;
    ensure!(
        server.try_acquire()?.is_none(),
        "cancelled driver minted an extra credit"
    );
    drop(returned);
    ensure!(server.available()? == 1);
    execution.passed = true;
    Ok(())
}

#[test]
fn finalize_refuses_while_an_actual_root_is_still_barrier_live() -> anyhow::Result<()> {
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(2).unwrap())?;
    for _ in 0..2 {
        execution.backing.push(
            pool.try_acquire(Owner::current(None))?
                .context("premature-Finalize backing missing")?,
        );
    }
    assert_no_cpu(&pool)?;
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    prepare(&world.join("a"), &jobserver, "a")?;
    execution.epoch = Some(Epoch::start(&world, 2, 1)?);
    let epoch = execution.epoch.as_mut().unwrap();
    let opened = epoch.event("opened", None)?;
    ensure!(opened["published"] == 1);
    let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
    let endpoint = Endpoint::capture(&fifo)?;
    execution.server = Some(Client::from_fifo(&fifo)?);
    execution.withheld.push(
        execution
            .server
            .as_ref()
            .unwrap()
            .try_acquire()?
            .context("missing P byte")?,
    );
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"spawn","id":0,"manifest":world.join("a/Cargo.toml"),"target":world.join("target-a.noindex")}))?;
    let spawned = epoch.event("spawned", Some(0))?;
    let root = libc::pid_t::try_from(spawned["pid"].as_u64().context("root PID missing")?)?;
    let a = ready(&execution.note("a", "ready")?, &fifo)?;
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"close"}))?;
    epoch.event("closing", None)?;
    epoch.finalize()?;
    let deadline = Instant::now() + HANG;
    loop {
        let stderr = fs::read_to_string(world.join("helper.stderr"))?;
        if stderr.contains("private epoch refused before root drain: private epoch finalize requires Close and all owned roots reaped") {
            break;
        }
        ensure!(
            epoch.child.try_wait()?.is_none() && Instant::now() < deadline,
            "helper did not report actual live-root Finalize refusal"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    // The exact refusal is observed before releasing any script barrier. This
    // SAFETY: root is checked positive and signal zero only observes that
    // original root number; it delivers no signal or process-control authority.
    ensure!(root > 1 && unsafe { libc::kill(root, 0) } == 0);
    ensure!(epoch.child.try_wait()?.is_none());
    epoch.no_retired_frame()?;
    assert_no_cpu(&pool)?;
    ensure!(fs::symlink_metadata(&fifo)?.file_type().is_fifo());

    // The helper retains its actual child on error. Let only this known Rust
    // fixture drain normally after the causal refusal observation above.
    execution.release("a", "acquire")?;
    execution.stage("a", "requesting", a)?;
    execution.withheld.clear();
    execution.stage("a", "acquired", a)?;
    execution.release("a", "verify")?;
    execution.stage("a", "alive", a)?;
    execution.release("a", "return")?;
    execution.stage("a", "returned", a)?;
    execution.release("a", "finish")?;
    execution.stage("a", "done", a)?;
    execution.release("a", "exit")?;
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.finish_status(false)?;
    epoch.no_retired_frame()?;
    // Refusal did not consume or mint a GNU credit. Withdraw the exact P byte
    // only for private fixture-node cleanup after its real roots have drained.
    let server = execution.server.as_ref().unwrap();
    ensure!(server.available()? == 1);
    server
        .try_acquire()?
        .context("returned P byte missing after refusal")?
        .drop_without_releasing();
    ensure!(server.try_acquire()?.is_none());
    endpoint.empty()?;
    execution.server.take();
    let cohort = execution.epoch.as_ref().unwrap().cohort;
    endpoint.cleanup(cohort)?;
    execution.backing.clear(); // No Retired: lost original capabilities remain debt.
    assert_kernel_free_and_debt_retained(&pool, std::process::id())?;
    execution.passed = true;
    Ok(())
}

// launchd reaps the genuinely orphaned helper after the direct CPU owner dies.
// Linux's surrounding PID 1 may not reap orphans; this slice deliberately makes
// no Linux crash-runtime claim or process-wide subreaper change.
#[cfg(target_os = "macos")]
const CONTROLLER_WORLD: &str = "TARGO_EPOCH_TEST_CPU_CONTROLLER";

#[cfg(target_os = "macos")]
#[test]
fn cpu_controller_actor_if_requested() -> anyhow::Result<()> {
    use std::os::fd::AsFd as _;
    let Some(world) = std::env::var_os(CONTROLLER_WORLD) else {
        return Ok(());
    };
    let world = PathBuf::from(world);
    let pool =
        RetainedPool::open_existing(&world.join("cpu.noindex"))?.context("CPU domain missing")?;
    let mut backing = Vec::new();
    for _ in 0..2 {
        backing.push(
            pool.try_acquire(Owner::current(None))?
                .context("CPU owner could not retain N")?,
        );
    }
    assert_no_cpu(&pool)?;
    println!(
        "\n{}",
        json!({"v":4,"epoch":EPOCH,"event":"controller-held","pid":std::process::id(),"backing":2})
    );
    io::stdout().flush()?;
    // The outer fixture retains the actual GNU control pipes for deterministic
    // orphan cleanup. This actor owns all CPU release capabilities and launches
    // the real helper as its child, without passing any CPU descriptor to it.
    let input = io::stdin().as_fd().try_clone_to_owned()?;
    let output = io::stdout().as_fd().try_clone_to_owned()?;
    let mut helper = helper_command(&world, 2, 1)?
        .stdin(Stdio::from(input))
        .stdout(Stdio::from(output))
        .spawn()?;
    println!(
        "{}",
        json!({"v":4,"epoch":EPOCH,"event":"helper-spawned","pid":helper.id()})
    );
    io::stdout().flush()?;
    let status = helper.wait()?;
    ensure!(
        status.success(),
        "helper failed before the CPU owner's required crash: {status:?}"
    );
    anyhow::bail!("CPU owner must be killed while the actual helper and build remain live")
}

fn assert_kernel_free_and_debt_retained(pool: &RetainedPool, pid: u32) -> anyhow::Result<()> {
    for number in 0..2 {
        let path = pool
            .path()
            .join(trust_build_cpu::RETAINED_DIRECTORY_NAME)
            .join(format!("slot-{number:08x}"));
        let file = fs::OpenOptions::new().read(true).write(true).open(path)?;
        let deadline = Instant::now() + HANG;
        loop {
            match file.try_lock() {
                Ok(()) => break,
                Err(std::fs::TryLockError::WouldBlock) => {
                    ensure!(
                        Instant::now() < deadline,
                        "CPU descriptor remains held after capability loss"
                    );
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(std::fs::TryLockError::Error(error)) => return Err(error.into()),
            }
        }
        file.unlock()?;
        drop(file);
    }
    // Every raw probe is unlocked and closed before the API denial. The live
    // helper/build cannot explain that denial through inherited kernel locks.
    let fresh = RetainedPool::open_existing(pool.path())?.context("CPU domain disappeared")?;
    assert_no_cpu(&fresh)?;
    for state in fresh.snapshot()? {
        ensure!(
            matches!(state, RetainedSlotState::Retained { reported_owner: Owner { pid: owner, birth: None }, .. } if owner == pid)
        );
    }
    Ok(())
}

#[cfg(target_os = "macos")]
#[test]
fn sigkilled_cpu_owner_leaves_debt_while_actual_helper_and_build_survive() -> anyhow::Result<()> {
    use std::os::unix::process::ExitStatusExt as _;
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(2).unwrap())?;
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    prepare(&world.join("a"), &jobserver, "a")?;
    let child = Command::new(std::env::current_exe()?)
        .args([
            "--exact",
            "cpu_controller_actor_if_requested",
            "--test-threads=1",
            "--nocapture",
        ])
        .env(CONTROLLER_WORLD, &world)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::from(fs::File::create(
            world.join("controller.stderr"),
        )?))
        .process_group(0)
        .spawn()?;
    execution.epoch = Some(Epoch::attach(&world, child, true)?);
    let epoch = execution.epoch.as_mut().unwrap();
    let owner = epoch.child.id();
    let held = epoch.event("controller-held", None)?;
    ensure!(held["pid"] == owner && held["backing"] == 2);
    assert_no_cpu(&pool)?;
    let spawned = epoch.event("helper-spawned", None)?;
    let helper = u32::try_from(
        spawned["pid"]
            .as_u64()
            .context("actual helper PID missing")?,
    )?;
    ensure!(helper != owner && helper > 1);
    epoch.cohort = helper;
    let opened = epoch.event("opened", None)?;
    ensure!(opened["backing"] == 2 && opened["roots"] == 1 && opened["published"] == 1);
    let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
    let endpoint = Endpoint::capture(&fifo)?;
    execution.server = Some(Client::from_fifo(&fifo)?);
    execution.withheld.push(
        execution
            .server
            .as_ref()
            .unwrap()
            .try_acquire()?
            .context("explicit credit missing")?,
    );
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"spawn","id":0,"manifest":world.join("a/Cargo.toml"),"target":world.join("target-a.noindex")}))?;
    epoch.event("spawned", Some(0))?;
    let a = ready(&execution.note("a", "ready")?, &fifo)?;
    execution.release("a", "acquire")?;
    execution.stage("a", "requesting", a)?;
    execution.withheld.clear();
    execution.stage("a", "acquired", a)?;
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.child.kill()?;
    let deadline = Instant::now() + HANG;
    let killed = loop {
        if let Some(status) = epoch.child.try_wait()? {
            break status;
        }
        ensure!(Instant::now() < deadline, "CPU owner did not die");
        std::thread::sleep(Duration::from_millis(10));
    };
    ensure!(killed.signal() == Some(libc::SIGKILL));
    // The helper responds through its original control pipe after its parent
    // dies, and the actual build script then proves it remains alive as well.
    epoch.send(json!({"op":"close"}))?;
    epoch.event("closing", None)?;
    epoch.no_retired_frame()?;
    execution.release("a", "verify")?;
    execution.stage("a", "alive", a)?;
    assert_kernel_free_and_debt_retained(&pool, owner)?;
    execution.release("a", "return")?;
    execution.stage("a", "returned", a)?;
    execution.release("a", "finish")?;
    execution.stage("a", "done", a)?;
    execution.release("a", "exit")?;
    let epoch = execution.epoch.as_mut().unwrap();
    ensure!(epoch.event("root-exit", Some(0))?["success"] == true);
    epoch.finalize()?;
    ensure!(epoch.event("retired", None)?["withdrawn"] == 1);
    endpoint.empty()?;
    execution.server.take();
    execution.epoch.as_mut().unwrap().finish_output()?;
    endpoint.cleanup(helper)?;
    // Even after actual helper EOF and complete kernel cohort drain, the lost
    // original capabilities cannot be reconstructed from a path or Retired.
    assert_kernel_free_and_debt_retained(&pool, owner)?;
    execution.passed = true;
    Ok(())
}

// The build script deliberately launches its own compiled Rust image without
// waiting for it: that grandchild is the real work the root-exit shortcut loses.
// Its output is redirected so it cannot keep Targo's build-script pipe open.
#[cfg(target_os = "macos")]
const ORPHAN_SCRIPT: &str = r#"
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

unsafe extern "C" { fn getpgrp() -> i32; }

fn note(root: &Path, stage: &str, body: &str) {
    let path = root.join(format!("probe.{stage}"));
    let temporary = path.with_extension(format!("{stage}.tmp"));
    std::fs::write(&temporary, format!("pid={}\n{body}\n", std::process::id())).unwrap();
    std::fs::rename(temporary, path).unwrap();
}
fn wait(root: &Path, stage: &str) {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        assert!(!root.join("abort").exists(), "controller aborted orphan fixture");
        if root.join(format!("probe.{stage}")).exists() { return; }
        assert!(Instant::now() < deadline, "orphan barrier missing: {stage}");
        std::thread::sleep(Duration::from_millis(10));
    }
}
fn main() {
    let root = PathBuf::from(std::env::var_os("EPOCH_WORLD").unwrap());
    if std::env::var_os("EPOCH_ORPHAN_PROBE").is_some() {
        let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
        assert!(flags.contains("--jobserver-auth=fifo:"));
        // SAFETY: getpgrp observes only this actual process's current group.
        let group = unsafe { getpgrp() };
        note(&root, "ready", &format!("ready\npgid={group}\nflags={flags}"));
        wait(&root, "import");
        // SAFETY: this known fixture metadata names the original FIFO, not
        // numeric descriptors which earlier file opens could have reused.
        let server = unsafe { jobserver::Client::from_env_ext(true) }.client.unwrap();
        assert_eq!(server.available().unwrap(), 0);
        assert!(server.try_acquire().unwrap().is_none());
        note(&root, "imported", &format!("imported\npgid={group}\nflags={flags}\nempty=true"));
        wait(&root, "release");
        note(&root, "released", "released");
        return;
    }
    // SAFETY: the actual root supplied this build script's inherited FIFO.
    let _server = unsafe { jobserver::Client::from_env_ext(true) }.client.unwrap();
    let child = Command::new(std::env::current_exe().unwrap())
        .env("EPOCH_ORPHAN_PROBE", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::from(std::fs::File::create(root.join("probe.stdout")).unwrap()))
        .stderr(Stdio::from(std::fs::File::create(root.join("probe.stderr")).unwrap()))
        .spawn().unwrap();
    wait(&root, "ready");
    assert!(std::fs::read_to_string(root.join("probe.ready")).unwrap().starts_with(&format!("pid={}\n", child.id())));
    drop(child); // Intentionally survive this root; the outer controller owns its release barrier.
    println!("cargo:rerun-if-changed=build.rs");
}
"#;

#[cfg(target_os = "macos")]
#[test]
fn actual_orphan_imports_the_same_empty_fifo_after_root_and_helper_exit() -> anyhow::Result<()> {
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(2).unwrap())?;
    for _ in 0..2 {
        execution.backing.push(
            pool.try_acquire(Owner::current(None))?
                .context("initial backing missing")?,
        );
    }
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    prepare_script(&world.join("orphan"), &jobserver, "orphan", ORPHAN_SCRIPT)?;
    execution.epoch = Some(Epoch::start(&world, 2, 1)?);
    let epoch = execution.epoch.as_mut().unwrap();
    let opened = epoch.event("opened", None)?;
    ensure!(opened["published"] == 1);
    let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
    let endpoint = Endpoint::capture(&fifo)?;
    let cohort = epoch.cohort;
    epoch.send(json!({"op":"spawn","id":0,"manifest":world.join("orphan/Cargo.toml"),"target":world.join("target-orphan.noindex")}))?;
    epoch.event("spawned", Some(0))?;
    let ready = execution.note("probe", "ready")?;
    ensure!(ready.contains(&format!("\npgid={cohort}\n")));
    ensure!(ready.contains(&format!("--jobserver-auth=fifo:{}", fifo.display())));
    let pid = ready
        .lines()
        .next()
        .and_then(|line| line.strip_prefix("pid="))
        .context("probe PID missing")?
        .parse::<u32>()?;
    let epoch = execution.epoch.as_mut().unwrap();
    epoch.send(json!({"op":"close"}))?;
    epoch.event("closing", None)?;
    ensure!(epoch.event("root-exit", Some(0))?["success"] == true);
    ensure!(epoch.child.try_wait()?.is_none());
    epoch.finalize()?;
    ensure!(epoch.event("retired", None)?["withdrawn"] == 1);
    epoch.finish()?;
    // The direct helper is actually reaped now. The original group remains
    // alive because this known Rust grandchild is waiting for our next command.
    let group = libc::pid_t::try_from(cohort)?;
    // SAFETY: signal zero only observes the original helper group; it sends no
    // signal, and the known Rust probe independently reports that same group.
    ensure!(unsafe { libc::kill(-group, 0) } == 0);
    endpoint.empty()?;
    assert_no_cpu(&pool)?;
    execution.release("probe", "import")?;
    let imported = execution.note("probe", "imported")?;
    ensure!(imported.starts_with(&format!("pid={pid}\nimported\npgid={cohort}\n")));
    ensure!(imported.contains(&format!("--jobserver-auth=fifo:{}", fifo.display())));
    ensure!(imported.ends_with("\nempty=true\n"));
    assert_no_cpu(&pool)?;
    execution.release("probe", "release")?;
    execution.stage("probe", "released", pid)?;
    endpoint.cleanup(cohort)?;
    ensure!(fs::symlink_metadata(&fifo).unwrap_err().kind() == io::ErrorKind::NotFound);
    for capability in execution.backing.drain(..) {
        capability.settle()?;
    }
    let mut restored = Vec::new();
    for _ in 0..2 {
        restored.push(
            pool.try_acquire(Owner::current(None))?
                .context("lost restored unit")?,
        );
    }
    assert_no_cpu(&pool)?;
    for capability in restored {
        capability.settle()?;
    }
    execution.passed = true;
    Ok(())
}

const WARM_SCRIPT: &str = r#"
fn main() {
    // SAFETY: capture the actual new root's explicit inherited GNU FIFO before work.
    let server = unsafe { jobserver::Client::from_env_ext(true) }.client.unwrap();
    assert_eq!(server.available().unwrap(), 0);
    assert!(server.try_acquire().unwrap().is_none());
    let root = std::path::PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let counter = root.join("build-runs");
    let prior = match std::fs::read_to_string(&counter) {
        Ok(value) => value.trim().parse::<u32>().unwrap(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => 0,
        Err(error) => panic!("counter read failed: {error}"),
    };
    std::fs::write(counter, format!("{}\n", prior + 1)).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
"#;

fn execute_artifact(path: &Path, run: &Path) -> anyhow::Result<()> {
    execute_artifact_with_output(path, run, b"warm-artifact-ok\n")
}

fn execute_artifact_with_output(path: &Path, run: &Path, expected: &[u8]) -> anyhow::Result<()> {
    let mut child = Command::new(path)
        .env_clear()
        .stdout(Stdio::from(fs::File::create(run.join("artifact.stdout"))?))
        .stderr(Stdio::from(fs::File::create(run.join("artifact.stderr"))?))
        .process_group(0)
        .spawn()?;
    let deadline = Instant::now() + HANG;
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            anyhow::bail!("actual emitted Rust artifact did not finish");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    ensure!(status.success());
    ensure!(fs::read(run.join("artifact.stdout"))? == expected);
    Ok(())
}

#[test]
fn fresh_transport_epochs_reuse_the_same_actual_target_without_rerunning_build_script()
-> anyhow::Result<()> {
    let mut execution = Execution::new()?;
    let world = execution.path().to_owned();
    let pool =
        RetainedPool::create_private(&world.join("cpu.noindex"), NonZeroU32::new(2).unwrap())?;
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    let project = world.join("warm");
    prepare_script(&project, &jobserver, "warm", WARM_SCRIPT)?;
    fs::write(
        project.join("src/main.rs"),
        "fn main() { assert_eq!((0..10).sum::<u64>(), 45); println!(\"warm-artifact-ok\"); }\n",
    )?;
    let cache = world.join("stable-cache.noindex");
    fs::create_dir(&cache)?;
    let target = cache.join("target.noindex");
    let artifact = target.join("debug/epoch_warm");
    let mut original = None;
    for (index, id) in [
        "11111111111111111111111111111111",
        "22222222222222222222222222222222",
    ]
    .iter()
    .enumerate()
    {
        let run = world.join(format!("run-{index}"));
        fs::create_dir(&run)?;
        for _ in 0..2 {
            execution.backing.push(
                pool.try_acquire(Owner::current(None))?
                    .context("warm epoch backing missing")?,
            );
        }
        assert_no_cpu(&pool)?;
        execution.epoch = Some(Epoch::start_with_id(&run, 2, 2, id)?);
        let epoch = execution.epoch.as_mut().unwrap();
        let opened = epoch.event("opened", None)?;
        ensure!(opened["published"] == 0);
        let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
        let endpoint = Endpoint::capture(&fifo)?;
        epoch.send(
            json!({"op":"spawn","id":0,"manifest":project.join("Cargo.toml"),"target":target}),
        )?;
        epoch.event("spawned", Some(0))?;
        epoch.send(json!({"op":"close"}))?;
        epoch.event("closing", None)?;
        ensure!(epoch.event("root-exit", Some(0))?["success"] == true);
        ensure!(epoch.child.try_wait()?.is_none());
        epoch.finalize()?;
        ensure!(epoch.event("retired", None)?["withdrawn"] == 0);
        epoch.finish()?;
        endpoint.cleanup(epoch.cohort)?;
        ensure!(
            fs::read(project.join("build-runs"))? == b"1\n",
            "fresh epoch reran the actual build script"
        );
        let metadata = fs::metadata(&artifact)?;
        let receipt = (
            identity(&metadata),
            metadata.len(),
            metadata.modified()?,
            fs::read(&artifact)?,
        );
        fs::write(
            run.join("artifact.receipt.json"),
            serde_json::to_vec_pretty(&json!({
                "path": artifact, "identity": receipt.0, "length": receipt.1,
                "modified": format!("{:?}", receipt.2),
            }))?,
        )?;
        if let Some(first) = &original {
            let (first_identity, first_length, first_modified, first_bytes) = first;
            let comparison = json!({
                "same_identity": receipt.0 == *first_identity,
                "first_identity": first_identity, "actual_identity": receipt.0,
                "same_length": receipt.1 == *first_length,
                "first_length": first_length, "actual_length": receipt.1,
                "same_modified": receipt.2 == *first_modified,
                "first_modified": format!("{first_modified:?}"),
                "actual_modified": format!("{:?}", receipt.2),
                "same_bytes": &receipt.3 == first_bytes,
            });
            fs::write(
                run.join("artifact.comparison.json"),
                serde_json::to_vec_pretty(&comparison)?,
            )?;
            ensure!(
                &receipt == first,
                "warm epoch rewrote the emitted artifact: {comparison}"
            );
        } else {
            original = Some(receipt);
        }
        execute_artifact(&artifact, &run)?;
        assert_no_cpu(&pool)?;
        for capability in execution.backing.drain(..) {
            capability.settle()?;
        }
    }
    // Reuse the already warmed target for these controls: no additional cold
    // compilation is needed. Completion followed by cancellation reserves both
    // the original ID and target for the whole epoch, including a normalized
    // duplicate and an ancestor alias.
    for (index, (id, rejected_id, alias)) in [
        (
            "33333333333333333333333333333333",
            1,
            Some(cache.join(".").join("target.noindex")),
        ),
        ("44444444444444444444444444444444", 1, Some(cache.clone())),
        ("55555555555555555555555555555555", 0, None),
    ]
    .iter()
    .enumerate()
    {
        let run = world.join(format!("alias-{index}"));
        fs::create_dir(&run)?;
        let alias_pool =
            RetainedPool::create_private(&run.join("cpu.noindex"), NonZeroU32::new(2).unwrap())?;
        for _ in 0..2 {
            execution.backing.push(
                alias_pool
                    .try_acquire(Owner::current(None))?
                    .context("alias epoch backing missing")?,
            );
        }
        execution.epoch = Some(Epoch::start_with_id(&run, 2, 2, id)?);
        let epoch = execution.epoch.as_mut().unwrap();
        let opened = epoch.event("opened", None)?;
        let fifo = PathBuf::from(opened["fifo"].as_str().context("FIFO missing")?);
        let endpoint = Endpoint::capture(&fifo)?;
        epoch.send(
            json!({"op":"spawn","id":0,"manifest":project.join("Cargo.toml"),"target":target}),
        )?;
        let spawned = epoch.event("spawned", Some(0))?;
        ensure!(epoch.event("root-exit", Some(0))?["success"] == true);
        epoch.send(json!({"op":"cancel","id":0}))?;
        let cancelled = epoch.event("cancelled", Some(0))?;
        ensure!(cancelled["pid"] == spawned["pid"] && cancelled["state"] == "already-exited");
        // Both aliases are otherwise valid and the first actual root is already
        // reaped and cancelled. The third case instead uses a fresh target to
        // distinguish the original root ID's one-use reservation.
        let alias = alias
            .clone()
            .unwrap_or_else(|| run.join("reused-id-target.noindex"));
        epoch.send(
            json!({"op":"spawn","id":rejected_id,"manifest":project.join("Cargo.toml"),"target":alias}),
        )?;
        // If a regression accepts the alias, Close and Finalize let it either
        // retire or refuse premature finalization. Its actual Spawned frame
        // still fails the control below rather than stranding the helper.
        let _ = epoch.send(json!({"op":"close"}));
        // Do not receive here: a correct refusal may already have queued its
        // sole EOF, which finish_status must still consume and join below.
        let finalization = format!("{:032x}", rand::random::<u128>().max(1));
        let _ = epoch.send(json!({"op":"finalize", "finalization":finalization}));
        epoch.finish_status(false)?;
        ensure!(
            epoch
                .pending
                .iter()
                .all(
                    |frame| !(frame["event"] == "spawned" && frame["id"] == *rejected_id)
                        && frame["event"] != "retired"
                ),
            "reserved target or root ID launched another root or falsely retired"
        );
        assert_no_cpu(&alias_pool)?;
        // A refusal without Retired supplies no release authority. This
        // independent negative-control domain keeps debt after dropping its
        // actual capabilities, even once the test's owned cohort drains.
        endpoint.cleanup(epoch.cohort)?;
        ensure!(fs::read(project.join("build-runs"))? == b"1\n");
        execution.backing.clear();
        assert_kernel_free_and_debt_retained(&alias_pool, std::process::id())?;
    }
    ensure!(
        pool.snapshot()?
            .iter()
            .all(|state| matches!(state, RetainedSlotState::Available { .. }))
    );
    execution.passed = true;
    Ok(())
}
