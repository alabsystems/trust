use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
static NEXT: AtomicU64 = AtomicU64::new(1);
const CAPTURE: usize = 8192;
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Result<Self> {
        let path = std::env::temp_dir().join(format!(
            "trust-worker-b2-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path)?;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700))?;
        Ok(Self(path))
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn readonly_snapshot(bytes: &[u8]) -> Result<File> {
    // SAFETY: constant NUL-terminated name and scalar memfd flags request a new
    // owned fixture file. No ambient path or existing descriptor is modified.
    let fd = unsafe {
        libc::memfd_create(
            c"b2-immutable-fixture".as_ptr(),
            libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING | 0x10,
        )
    };
    if fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful memfd_create returned unique ownership of this FD.
    let mut file = unsafe { File::from_raw_fd(fd) };
    file.write_all(bytes)?;
    // SAFETY: adding the complete immutable seal set restricts this owned file;
    // there are no existing writable mappings in the fixture.
    if unsafe {
        libc::fcntl(
            fd,
            libc::F_ADD_SEALS,
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL,
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error().into());
    }
    // Reopen only in trusted fixture setup to obtain a read-only capability;
    // no pathname reopening is admitted after the worker restrictions.
    let read = File::open(format!("/proc/self/fd/{fd}"))?;
    drop(file);
    Ok(read)
}
fn high(fd: i32) -> Result<OwnedFd> {
    // SAFETY: F_DUPFD_CLOEXEC gives unique ownership of a fresh high-numbered FD;
    // this prevents the child remapping from overwriting another source FD.
    let value = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 64) };
    if value < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: value is the newly allocated owned descriptor, not the source.
    Ok(unsafe { OwnedFd::from_raw_fd(value) })
}
fn nonblocking(fd: i32) -> Result<()> {
    // SAFETY: F_GETFL only reads flags on this owned test capture pipe.
    let old = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if old < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: F_SETFL affects only this test-owned read endpoint.
    if unsafe { libc::fcntl(fd, libc::F_SETFL, old | libc::O_NONBLOCK) } != 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    Ok(())
}
struct OwnedWorker {
    child: Child,
    reaped: bool,
}
impl OwnedWorker {
    fn exited(&self) -> Result<bool> {
        let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
        // SAFETY: waitid writes to a full initialized siginfo_t buffer and uses
        // WNOWAIT to retain the child identity until group cleanup and reaping.
        if unsafe {
            libc::waitid(
                libc::P_PID,
                self.child.id(),
                info.as_mut_ptr(),
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        } != 0
        {
            return Err(std::io::Error::last_os_error().into());
        }
        // SAFETY: successful waitid initialized the record; si_pid is the child
        // identity field for CLD_* notifications, or zero for WNOHANG.
        Ok(unsafe { info.assume_init().si_pid() } != 0)
    }
    fn stop_and_reap(&mut self) -> Result<ExitStatus> {
        // SAFETY: the unreaped child PID still pins its private group identity;
        // every terminal path kills the whole group before releasing that PID.
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGKILL);
        }
        let status = self.child.wait()?;
        self.reaped = true;
        Ok(status)
    }
}
impl Drop for OwnedWorker {
    fn drop(&mut self) {
        if !self.reaped {
            // SAFETY: this owned unreaped leader still pins the group, even on
            // assertion panic/error; no unrelated process group is addressed.
            unsafe {
                libc::kill(-(self.child.id() as i32), libc::SIGKILL);
            }
            let _ = self.child.wait();
        }
    }
}
#[derive(Debug, PartialEq, Eq)]
enum Cause {
    Exit,
    Deadline,
    OutputLimit,
}
struct Observation {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    control: Vec<u8>,
    cause: Cause,
    leader_zombie_before_reap: bool,
}
fn capture(stream: &mut impl Read, output: &mut Vec<u8>) -> Result<bool> {
    let mut block = [0u8; 1024];
    for _ in 0..16 {
        match stream.read(&mut block) {
            Ok(0) => return Ok(false),
            Ok(count) => {
                if count > CAPTURE.saturating_sub(output.len()) {
                    return Ok(true);
                }
                output.extend_from_slice(&block[..count]);
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => return Ok(false),
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error.into()),
        }
    }
    Ok(false)
}
fn run(mode: &str, modified: Option<&str>) -> Result<Observation> {
    run_fixture(mode, modified, Path::new(env!("CARGO_BIN_EXE_restriction-fixture")))
}
fn run_fixture(mode: &str, modified: Option<&str>, executable_path: &Path) -> Result<Observation> {
    let deadline = Instant::now()
        + if mode == "stall" {
            Duration::from_millis(500)
        } else if mode == "leader-exit" {
            Duration::from_secs(5)
        } else {
            Duration::from_secs(10)
        };
    let root = Scratch::new()?;
    let scratch = root.0.join("scratch");
    fs::create_dir(&scratch)?;
    fs::set_permissions(&scratch, fs::Permissions::from_mode(0o700))?;
    let canary = root.0.join("outside-canary");
    fs::write(&canary, b"fixture-only outside bytes")?;
    let mut data = [0u8; 4096];
    data[..6].copy_from_slice(b"pinned");
    let digest = Sha256::digest(data);
    let mut hex = digest.iter().map(|b| format!("{b:02x}")).collect::<String>();
    if modified == Some("hash") {
        hex.replace_range(..2, &format!("{:02x}", digest[0] ^ 1));
    }
    let input = if modified == Some("unsealed") {
        let path = root.0.join("unsealed");
        fs::write(&path, data)?;
        File::open(path)?
    } else {
        readonly_snapshot(&data)?
    };
    if executable_path.metadata()?.len() > 64 * 1024 * 1024 {
        return Err("oversized fixture executable".into());
    }
    // Actual fixture execution uses this immutable descriptor snapshot, not the
    // mutable target path. Its dynamic runtime closure is not qualified here.
    let executable = readonly_snapshot(&fs::read(executable_path)?)?;
    let (mut control, worker_control) = UnixStream::pair()?;
    control.set_nonblocking(true)?;
    let directory = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_PATH | libc::O_DIRECTORY)
        .open(&scratch)?;
    let input_count = if mode == "max-inputs" { 27 } else { 1 };
    let mut originals = Vec::with_capacity(input_count + 3);
    originals.push(high(worker_control.as_raw_fd())?);
    originals.push(high(directory.as_raw_fd())?);
    for _ in 0..input_count {
        originals.push(high(input.as_raw_fd())?);
    }
    originals.push(high(executable.as_raw_fd())?);
    let sources = originals.iter().map(AsRawFd::as_raw_fd).collect::<Vec<_>>();
    let resource_roles = mode.starts_with("resource-");
    let resource_statm = match mode {
        "resource-wrong-role" => c"/proc/meminfo",
        "resource-imitation" => c"/dev/null",
        _ => c"/proc/self/statm",
    };
    let executable_fd = if resource_roles { 8 } else { (5 + input_count) as i32 };
    let parent = if modified == Some("parent") { 1 } else { std::process::id() };
    let mut command = Command::new(format!("/proc/self/fd/{executable_fd}"));
    command
        .env_clear()
        .args([mode, &parent.to_string(), &hex, canary.to_str().ok_or("non-UTF8 fixture path")?])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if modified == Some("environment") {
        command.env("B2_FIXTURE_AMBIENT_CANARY", "refuse");
    }
    let preexec_thread_limits =
        executable_path == Path::new(env!("CARGO_BIN_EXE_checker-threads-fixture"));
    // SAFETY: this child-only pre_exec closure performs only async-signal-safe
    // scalar syscalls. Sources are high unique descriptors; low destinations
    // cannot overwrite them. No allocation, Rust lock, or environment mutation
    // occurs after fork. The exec FD closes at exec; all undeclared FDs close.
    // This closes std::process's private exec-error pipe too: errors surface as
    // worker exit/status, not precise spawn io::Error. Not a production launcher.
    unsafe {
        command.pre_exec(move || {
            if libc::setpgid(0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            for (index, source) in sources.iter().copied().enumerate() {
                let destination =
                    if index + 1 == sources.len() { executable_fd } else { 3 + index as i32 };
                if libc::dup3(
                    source,
                    destination,
                    if destination == executable_fd { libc::O_CLOEXEC } else { 0 },
                ) < 0
                {
                    return Err(std::io::Error::last_os_error());
                }
            }
            if resource_roles {
                // Fixed, trusted fixture leaves. Opening after fork binds statm
                // to this child; the post-exec production entry independently
                // authenticates the actual procfs/dev/inode/read-only identities.
                // This fixture owns every low destination; source high copies
                // and the executable at8 cannot collide with resource roles.
                for (leaf, destination) in [(resource_statm, 6), (c"/proc/meminfo", 7)] {
                    let fd = libc::open(leaf.as_ptr(), libc::O_RDONLY | libc::O_NOFOLLOW);
                    if fd < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    if fd != destination {
                        let copied = libc::dup3(fd, destination, 0);
                        let closed = libc::close(fd);
                        if copied < 0 || closed != 0 {
                            return Err(std::io::Error::last_os_error());
                        }
                    }
                }
            }
            if libc::syscall(libc::SYS_close_range, (executable_fd + 1) as u32, u32::MAX, 0u32) != 0
            {
                return Err(std::io::Error::last_os_error());
            }
            if preexec_thread_limits {
                for (resource, limit) in
                    [(libc::RLIMIT_AS, 256 * 1024 * 1024), (libc::RLIMIT_STACK, 8 * 1024 * 1024)]
                {
                    let value = libc::rlimit { rlim_cur: limit, rlim_max: limit };
                    if libc::setrlimit(resource, &value) != 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                }
            }
            Ok(())
        });
    }
    let mut owner = OwnedWorker { child: command.spawn()?, reaped: false };
    let mut stdout = owner.child.stdout.take().ok_or("missing stdout")?;
    let mut stderr = owner.child.stderr.take().ok_or("missing stderr")?;
    nonblocking(stdout.as_raw_fd())?;
    nonblocking(stderr.as_raw_fd())?;
    let mut out = Vec::new();
    let mut err = Vec::new();
    let mut ipc = Vec::new();
    let mut leader_zombie_before_reap = false;
    let cause = loop {
        if capture(&mut stdout, &mut out)?
            || capture(&mut stderr, &mut err)?
            || capture(&mut control, &mut ipc)?
        {
            break Cause::OutputLimit;
        }
        if owner.exited()? {
            break Cause::Exit;
        }
        if mode == "leader-exit" {
            // Trusted parent observation, never a worker completion assertion.
            let stat = fs::read_to_string(format!("/proc/{}/stat", owner.child.id()))?;
            leader_zombie_before_reap |=
                stat.rsplit_once(')').is_some_and(|(_, tail)| tail.starts_with(" Z "));
        }
        if Instant::now() >= deadline {
            break Cause::Deadline;
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    let status = owner.stop_and_reap()?;
    let _ = capture(&mut stdout, &mut out)?;
    let _ = capture(&mut stderr, &mut err)?;
    let _ = capture(&mut control, &mut ipc)?;
    Ok(Observation {
        status,
        stdout: out,
        stderr: err,
        control: ipc,
        cause,
        leader_zombie_before_reap,
    })
}

#[test]
fn real_restrictions_allow_declared_inputs_and_control() -> Result<()> {
    let r = run("positive", None)?;
    assert_eq!(r.cause, Cause::Exit);
    assert!(
        r.status.success(),
        "status={} stderr={}",
        r.status,
        String::from_utf8_lossy(&r.stderr)
    );
    assert_eq!(r.stdout, b"INSTALLED\nPASS\n");
    assert_eq!(r.control, b"IPC-OK");
    Ok(())
}
#[test]
fn maximum_dense_input_layout_installs_and_retains_role_guards() -> Result<()> {
    let r = run("max-inputs", None)?;
    assert_eq!(r.cause, Cause::Exit);
    assert!(r.status.success(), "{} {}", r.status, String::from_utf8_lossy(&r.stderr));
    assert_eq!(r.stdout, b"INSTALLED\nPASS\n");
    assert_eq!(r.control, b"IPC-OK");
    Ok(())
}
#[test]
fn all_path_opens_including_procfd_aliases_are_denied() -> Result<()> {
    for mode in
        ["outside-read", "procfd-output-read", "procfd-input-reopen", "procfd-control-reopen"]
    {
        let r = run(mode, None)?;
        assert_eq!(
            r.status.signal(),
            Some(libc::SIGSYS),
            "{mode}: {} {}",
            r.status,
            String::from_utf8_lossy(&r.stderr)
        );
        assert_eq!(r.stdout, b"INSTALLED\n");
    }
    Ok(())
}
#[test]
fn seccomp_terminates_every_forbidden_authority_attempt() -> Result<()> {
    for mode in [
        "input-write",
        "input-close",
        "socket",
        "exec",
        "fork",
        "wx",
        "mprotect-exec",
        "undeclared-exec",
    ] {
        let r = run(mode, None)?;
        assert_eq!(r.cause, Cause::Exit, "{mode}");
        assert_eq!(
            r.status.signal(),
            Some(libc::SIGSYS),
            "{mode}: {} {}",
            r.status,
            String::from_utf8_lossy(&r.stderr)
        );
        assert_eq!(r.stdout, b"INSTALLED\n", "{mode}");
    }
    Ok(())
}
#[test]
fn input_and_environment_admission_never_fall_back() -> Result<()> {
    for (mutation, reason) in [
        ("hash", "input digest"),
        ("unsealed", "input seals"),
        ("environment", "ambient environment"),
    ] {
        let r = run("positive", Some(mutation))?;
        assert_eq!(r.status.code(), Some(72), "{mutation}: {}", r.status);
        assert!(r.stdout.is_empty());
        assert!(r.stderr.starts_with(b"REFUSED: "));
        assert!(
            String::from_utf8_lossy(&r.stderr).contains(reason),
            "{}",
            String::from_utf8_lossy(&r.stderr)
        );
    }
    for (mode, reason) in [
        ("read-implies-exec", "non-native personality"),
        ("existing-wx", "existing writable executable mapping"),
    ] {
        let r = run(mode, None)?;
        assert_eq!(
            r.status.code(),
            Some(72),
            "{mode}: {} {}",
            r.status,
            String::from_utf8_lossy(&r.stderr)
        );
        assert!(r.stdout.is_empty());
        assert!(r.stderr.starts_with(b"REFUSED: "));
        assert!(
            String::from_utf8_lossy(&r.stderr).contains(reason),
            "{}",
            String::from_utf8_lossy(&r.stderr)
        );
    }
    Ok(())
}
#[test]
fn owned_parent_stops_output_flood_and_deadline_then_reaps() -> Result<()> {
    let flood = run("output-flood", None)?;
    assert_eq!(flood.cause, Cause::OutputLimit);
    assert_eq!(flood.status.signal(), Some(libc::SIGKILL));
    assert!(flood.stdout.len() <= CAPTURE);
    let stalled = run("stall", None)?;
    assert_eq!(stalled.cause, Cause::Deadline);
    assert_eq!(stalled.status.signal(), Some(libc::SIGKILL));
    Ok(())
}

#[path = "kernel/checker_threads.rs"]
mod checker_threads;

#[path = "kernel/checker_resources.rs"]
mod checker_resources;
