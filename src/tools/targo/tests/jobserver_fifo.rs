// Trust: actual build roots consuming one explicitly supplied GNU FIFO.
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::ffi::CString;
use std::fs;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, ensure};
use jobserver::{Acquired, Client};

const HANG: Duration = Duration::from_secs(60);

// These are ordinary Rust build scripts, compiled by the Targo under test.
// Their one acquired guard models cooperating extra work, not arbitrary thread
// confinement. The two root implicit credits remain held by the controller.
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
    // SAFETY: capture the inherited scheduling transport before this script
    // opens files or starts work. The controller supplied its exact FIFO.
    let server = unsafe { jobserver::Client::from_env_ext(true) }.client.unwrap();
    let root = PathBuf::from(std::env::var_os("FIFO_WORLD").unwrap());
    let side = std::env::var("FIFO_SIDE").unwrap();
    let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
    assert_eq!(server.available().unwrap(), 0, "root minted extra initial credits");
    assert!(server.try_acquire().unwrap().is_none());
    note(&root, &side, "ready", &format!("ready\nflags={flags}\nempty=true"));
    wait(&root, &side, "acquire");
    assert!(server.try_acquire().unwrap().is_none(), "extra credit issued before release");
    note(&root, &side, "requesting", "requesting");
    let extra = server.acquire().unwrap();
    assert!(!root.join("abort").exists(), "fixture controller aborted");
    note(&root, &side, "acquired", "acquired");
    wait(&root, &side, "return");
    drop(extra);
    note(&root, &side, "returned", "returned");
    wait(&root, &side, "finish");
    note(&root, &side, "done", "done");
    wait(&root, &side, "exit");
}
"#;

struct Root {
    side: &'static str,
    child: Option<Child>,
    status: Option<ExitStatus>,
}

// One controller owns both roots, waits and retained root guards. Failed worlds
// survive every early return or panic with compiler logs and barrier receipts.
struct Execution {
    world: Option<tempfile::TempDir>,
    roots: Vec<Root>,
    implicit: Vec<Acquired>,
    withheld: Vec<Acquired>,
    passed: bool,
}

impl Execution {
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
            for root in &self.roots {
                ensure!(
                    !exited(root.child.as_ref().unwrap())?,
                    "root {} exited before {side}.{stage}; evidence: {}",
                    root.side,
                    self.path().display()
                );
            }
            match fs::read_to_string(self.path().join(format!("{side}.{stage}"))) {
                Ok(note) => return Ok(note),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
            ensure!(
                Instant::now() < deadline,
                "missing {side}.{stage}; evidence: {}",
                self.path().display()
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn finish_roots(&mut self) -> anyhow::Result<()> {
        let deadline = Instant::now() + HANG;
        loop {
            let done = self
                .roots
                .iter()
                .filter_map(|root| root.child.as_ref().map(exited))
                .collect::<io::Result<Vec<_>>>()?;
            if done.iter().all(|done| *done) {
                break;
            }
            ensure!(Instant::now() < deadline, "Targo roots did not finish");
            std::thread::sleep(Duration::from_millis(10));
        }
        for root in &mut self.roots {
            if let Some(child) = root.child.as_mut() {
                root.status = Some(child.wait()?);
                root.child.take();
            }
        }
        for root in &self.roots {
            ensure!(
                root.status.unwrap().success(),
                "root {} failed: {:?}; compiler evidence: {}",
                root.side,
                root.status,
                self.path().display()
            );
        }
        Ok(())
    }

    fn returned_credit(&self, server: &Client) -> anyhow::Result<Acquired> {
        let deadline = Instant::now() + HANG;
        loop {
            if let Some(credit) = server.try_acquire()? {
                return Ok(credit);
            }
            ensure!(Instant::now() < deadline, "returned shared credit missing");
            // Targo's own helper may transiently receive a returned byte, then
            // relinquish it while its single build script remains active.
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for Execution {
    fn drop(&mut self) {
        if self.roots.iter().any(|root| root.child.is_some()) {
            let _ = fs::write(self.path().join("abort"), b"controller cleanup\n");
            for side in ["a", "b"] {
                for stage in ["acquire", "return", "finish", "exit"] {
                    let _ = self.release(side, stage);
                }
            }
            // Release only withheld extras: blocked acquires can then observe
            // abort and return their own guards. Root backing stays retained.
            self.withheld.clear();
            let deadline = Instant::now() + HANG;
            while self.roots.iter().any(|root| {
                root.child
                    .as_ref()
                    .is_some_and(|child| !exited(child).unwrap_or(false))
            }) && Instant::now() < deadline
            {
                std::thread::sleep(Duration::from_millis(10));
            }
            for root in &mut self.roots {
                if let Some(mut child) = root.child.take() {
                    // SAFETY: this direct child has never been reaped. Its PID
                    // pins the private process-group identity created at spawn;
                    // only our known fixture descendants join that group.
                    unsafe { libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL) };
                    let _ = child.kill();
                    let _ = child.wait();
                }
            }
        }
        if !self.passed {
            eprintln!(
                "kept failed shared-FIFO world: {}",
                self.world.take().unwrap().keep().display()
            );
        }
    }
}

fn exited(child: &Child) -> io::Result<bool> {
    let pid = libc::pid_t::try_from(child.id())
        .map_err(|_| io::Error::other("owned child PID does not fit pid_t"))?;
    loop {
        // SAFETY: info is an initialized output buffer for our still-owned
        // direct child. WNOWAIT leaves its PID pinned; this controller alone
        // performs the eventual wait, after any owned group cleanup.
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        let result = unsafe {
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                &mut info,
                libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
            )
        };
        if result == 0 {
            #[cfg(target_os = "macos")]
            return Ok(info.si_pid == pid);
            #[cfg(target_os = "linux")]
            return Ok(unsafe { info.si_pid() } == pid);
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}

fn ready_pid(note: &str, flags: &str) -> anyhow::Result<u32> {
    let pid = note
        .lines()
        .next()
        .and_then(|line| line.strip_prefix("pid="))
        .context("ready record missing actor PID")?
        .parse::<u32>()?;
    ensure!(pid != 0);
    ensure!(note == format!("pid={pid}\nready\nflags={flags}\nempty=true\n"));
    Ok(pid)
}

fn prepare(root: &Path, jobserver: &Path, side: &str) -> anyhow::Result<()> {
    fs::create_dir_all(root.join("src"))?;
    // JSON quoting is also a TOML basic string for this absolute fixture path.
    let jobserver = serde_json::to_string(&jobserver.to_str().unwrap())?;
    fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname='fifo_{side}'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[build-dependencies]\njobserver={{path={jobserver}}}\n"
        ),
    )?;
    fs::write(root.join("build.rs"), SCRIPT)?;
    fs::write(
        root.join("src/main.rs"),
        format!(
            "fn main() {{ assert_eq!((0..10).sum::<u64>(), 45); println!(\"fifo-{side}-ok\"); }}\n"
        ),
    )?;
    Ok(())
}

#[test]
fn two_native_build_roots_exchange_one_shared_fifo_credit_without_restart() -> anyhow::Result<()> {
    // GNU's whitespace-separated metadata cannot carry a FIFO pathname with
    // spaces, even when the source checkout itself has them. Keep this private
    // fixture outside the checkout and out of both filesystem indexing lanes.
    let base = Path::new("/tmp/.ubd/targo-shared-fifo.noindex");
    fs::create_dir_all(base)?;
    let mut execution = Execution {
        world: Some(tempfile::tempdir_in(base)?),
        roots: Vec::new(),
        implicit: Vec::new(),
        withheld: Vec::new(),
        passed: false,
    };
    let path = execution.path().join("shared.fifo");
    let cpath = CString::new(path.as_os_str().as_bytes())?;
    // SAFETY: cpath is terminated and live; the private world has no such node.
    ensure!(
        unsafe { libc::mkfifo(cpath.as_ptr(), 0o600) } == 0,
        "{}",
        io::Error::last_os_error()
    );
    let server = Client::from_fifo(&path)?;
    for _ in 0..4 {
        server.release_raw()?;
    }
    for _ in 0..2 {
        execution.implicit.push(server.acquire()?);
        execution.withheld.push(server.acquire()?);
    }
    ensure!(server.try_acquire()?.is_none());
    let jobserver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../vendor/jobserver")
        .canonicalize()?;
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .context("parent build has no Cargo cache location")?;
    let mut flags = None;
    for side in ["a", "b"] {
        let root = execution.path().join(side);
        prepare(&root, &jobserver, side)?;
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        command
            .env_clear()
            .env("HOME", execution.path().join("home"))
            .env("CARGO_HOME", &cargo_home)
            .env("CARGO_TARGET_DIR", root.join("target.noindex"))
            .env(
                "RUSTC",
                std::env::var_os("RUSTC").context("parent RUSTC missing")?,
            )
            .env(
                "PATH",
                std::env::var_os("PATH").context("parent PATH missing")?,
            )
            .env("FIFO_WORLD", execution.path())
            .env("FIFO_SIDE", side)
            .current_dir(&root)
            .args(["--unverified", "build", "--offline"])
            .stdout(Stdio::from(fs::File::create(root.join("stdout.log"))?))
            .stderr(Stdio::from(fs::File::create(root.join("stderr.log"))?))
            .process_group(0);
        server.configure(&mut command);
        let configured = command
            .get_envs()
            .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
            .context("shared FIFO metadata missing")?
            .to_str()
            .context("shared FIFO metadata is not UTF-8")?
            .to_owned();
        ensure!(configured.contains(&format!("--jobserver-auth=fifo:{}", path.display())));
        if let Some(flags) = &flags {
            ensure!(flags == &configured);
        }
        flags = Some(configured);
        execution.roots.push(Root {
            side,
            child: Some(command.spawn()?),
            status: None,
        });
    }
    let flags = flags.unwrap();
    let a = ready_pid(&execution.note("a", "ready")?, &flags)?;
    let b = ready_pid(&execution.note("b", "ready")?, &flags)?;
    ensure!(a != b);
    execution.release("a", "acquire")?;
    ensure!(execution.note("a", "requesting")? == format!("pid={a}\nrequesting\n"));
    drop(execution.withheld.pop().unwrap());
    ensure!(execution.note("a", "acquired")? == format!("pid={a}\nacquired\n"));
    ensure!(server.available()? == 0);
    execution.release("b", "acquire")?;
    ensure!(execution.note("b", "requesting")? == format!("pid={b}\nrequesting\n"));
    ensure!(!execution.path().join("b.acquired").exists());
    ensure!(server.available()? == 0);
    execution.release("a", "return")?;
    ensure!(execution.note("a", "returned")? == format!("pid={a}\nreturned\n"));
    ensure!(execution.note("b", "acquired")? == format!("pid={b}\nacquired\n"));
    ensure!(server.available()? == 0);
    execution.release("b", "return")?;
    ensure!(execution.note("b", "returned")? == format!("pid={b}\nreturned\n"));
    let returned = execution.returned_credit(&server)?;
    execution.withheld.push(returned);
    ensure!(server.try_acquire()?.is_none());
    for (side, pid) in [("a", a), ("b", b)] {
        execution.release(side, "finish")?;
        ensure!(execution.note(side, "done")? == format!("pid={pid}\ndone\n"));
    }
    for side in ["a", "b"] {
        execution.release(side, "exit")?;
    }
    execution.finish_roots()?;
    execution.implicit.clear();
    execution.withheld.clear();
    ensure!(
        server.available()? == 4,
        "root and extra credits did not return exactly"
    );
    let restored = (0..4)
        .map(|_| server.try_acquire()?.context("missing restored credit"))
        .collect::<anyhow::Result<Vec<_>>>()?;
    ensure!(
        server.try_acquire()?.is_none(),
        "an extra credit was minted"
    );
    drop(restored);
    for (side, label) in [("a", "a-program"), ("b", "b-program")] {
        let root = execution.path().join(side);
        let child = Command::new(root.join(format!("target.noindex/debug/fifo_{side}")))
            .env_clear()
            .stdout(Stdio::from(fs::File::create(root.join("program.stdout"))?))
            .stderr(Stdio::from(fs::File::create(root.join("program.stderr"))?))
            .process_group(0)
            .spawn()?;
        execution.roots.push(Root {
            side: label,
            child: Some(child),
            status: None,
        });
    }
    execution.finish_roots()?;
    for side in ["a", "b"] {
        ensure!(
            fs::read(execution.path().join(side).join("program.stdout"))?
                == format!("fifo-{side}-ok\n").as_bytes()
        );
    }
    ensure!(server.available()? == 4);
    execution.passed = true;
    Ok(())
}
