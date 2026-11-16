#![cfg(unix)]

use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use std::{fs, thread};

/// The variable that moves targo-trust's memory-authority endpoint into
/// [`FakeTrustd::runtime_dir`].
pub(crate) const RUNTIME_DIR_ENV: &str = trust_router::coordinator::RUNTIME_DIR_ENV;

/// Install a protocol-capable sibling `trustd` together with a PRIVATE memory
/// domain for it: a fresh 0700 runtime directory that the tested command is
/// pointed at through [`RUNTIME_DIR_ENV`] (see [`FakeTrustd::runtime_dir`]).
///
/// These tests used to share the production per-euid endpoint, serialized by a
/// process-global mutex that only one test binary could see. Two concurrent
/// runs of the suites (another session, the other test binary) therefore
/// collided on the one socket, and whenever a real verified build's trustd was
/// live every stub-using test had to refuse (30 of 32 red, measured
/// 2026-09-24), because the only alternative was the 2026-09-19 incident in
/// which a stub displaced a live gate's daemon. A per-test directory removes
/// the shared resource, so there is nothing left to serialize or to protect.
///
/// The stub is also STARTED here, and `install` returns only once it serves on
/// that private endpoint as exactly these bytes. The command under test then
/// finds a compatible daemon already listening and reuses it, so it never has
/// to spawn one. Its spawn path gives a new daemon a fixed 5 s
/// (SPAWN_READY_TIMEOUT) to become ready, and a Python stub on a loaded host
/// can miss that even after the warm-up below: measured 2026-09-29 at load
/// average 60, `trust_profile_sets_tracked_hardened_options` exited 2 with
/// "did not establish exact-identity readiness within 5s" on this private
/// endpoint. Waiting here ends on an event (the stub serves, or it exits), not
/// on a deadline; the production deadline is untouched.
pub(crate) fn install(bin_dir: &Path) -> FakeTrustd {
    let path = bin_dir.join(format!("trustd{}", std::env::consts::EXE_SUFFIX));
    fs::write(&path, script()).expect("write fake trustd");
    let mut permissions = fs::metadata(&path).expect("fake trustd metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("make fake trustd executable");
    // Execute the stub once, untimed, before targo-trust does. macOS assesses a
    // NEWLY WRITTEN executable on its first exec, and on a loaded host that
    // took 6-10 s per file (measured 2026-09-27: `sample` showed stubs parked
    // at `_dyld_start`; a second exec of the same file took 0.04 s). targo-trust
    // gives a spawned daemon a fixed 5 s to become ready, so a stub paying that
    // first-exec cost inside the window failed tests at random — with or
    // without a shared socket. A packaged trustd has long since been executed;
    // warming the stub makes the fixture match that, and leaves the production
    // deadline untouched.
    let warm = Command::new(&path).arg("--version").output().expect("run fake trustd --version");
    assert!(
        warm.status.success()
            && String::from_utf8_lossy(&warm.stdout).contains("trust.identity=trustd"),
        "fake trustd --version failed: {warm:?}"
    );
    let runtime_dir = private_runtime_dir();
    let socket = trust_router::coordinator::host_socket_path_in(&runtime_dir)
        .expect("the per-test runtime directory satisfies the endpoint's privacy rules");
    let served_marker = bin_dir.join("trustd.served");
    let stub = start_and_await(&path, &socket);
    FakeTrustd { runtime_dir, socket, served_marker, stub: Some(stub) }
}

/// Start the stub on `socket` and return once it identifies as the bytes at
/// `executable` with an acceptable STATUS: the same exact-identity check
/// targo-trust makes before it reuses a live daemon. Each probe is bounded by
/// the coordinator's observer deadline, but the wait is not: it ends when the
/// stub serves, or fails when the stub exits.
fn start_and_await(executable: &Path, socket: &Path) -> Child {
    let started = Instant::now();
    let mut notes = 0;
    let mut child = Command::new(executable)
        .arg("--socket")
        .arg(socket)
        .env(OWNER_PID_ENV, std::process::id().to_string())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .spawn()
        .unwrap_or_else(|error| panic!("start fake trustd {}: {error}", executable.display()));
    while !trust_router::coordinator::daemon_matches_executable(socket, executable) {
        if let Some(status) = child.try_wait().expect("poll fake trustd") {
            panic!(
                "fake trustd {} exited ({status}) before it served {}",
                executable.display(),
                socket.display()
            );
        }
        note_if_still_waiting(started, &mut notes, || {
            format!("fake trustd pid {} to serve {}", child.id(), socket.display())
        });
        thread::sleep(Duration::from_millis(10));
    }
    child
}

/// How often a wait in this module says what it is still waiting for.
const STILL_WAITING_NOTE: Duration = Duration::from_secs(30);

/// The waits here end on events (the stub serves, the stub exits), never on a
/// clock, so a stub that did neither would hold its test with no output. This
/// prints what the test is waiting for once per [`STILL_WAITING_NOTE`]. It
/// never ends the wait and never changes a verdict.
fn note_if_still_waiting(started: Instant, notes: &mut u32, what: impl FnOnce() -> String) {
    if started.elapsed() >= STILL_WAITING_NOTE * (*notes + 1) {
        *notes += 1;
        eprintln!(
            "fake_trustd: still waiting after {}s for {}",
            started.elapsed().as_secs(),
            what()
        );
    }
}

/// Names the test process that started a stub. Such a stub lives exactly as
/// long as that process, instead of idling out after 30 s: it is started
/// before the command under test, which may take longer than any idle
/// allowance to reach it, and targo-trust would then spawn a replacement under
/// the very deadline `install` exists to avoid. targo-trust spawns daemons with
/// a cleared environment, so a stub it starts keeps the idle exit.
const OWNER_PID_ENV: &str = "TRUST_FAKE_TRUSTD_OWNER_PID";

/// Install a sibling `trustd` that can never be established, in a PRIVATE
/// memory domain where nothing serves: started on any socket, it reports that
/// another trustd owns that socket and exits, as a live daemon of another
/// build makes the real one do. The command under test spawns it (it is the
/// only daemon it may use), so this is how a test reaches the "the daemon
/// could not run it" refusal without touching the host's endpoint. Nothing it
/// starts outlives the attempt.
#[allow(dead_code)] // each including test binary uses a different subset
pub(crate) fn install_refusing(bin_dir: &Path) -> RefusingTrustd {
    let path = bin_dir.join(format!("trustd{}", std::env::consts::EXE_SUFFIX));
    fs::write(bin_dir.join("trustd.refuse"), "").expect("write fake trustd refusal marker");
    fs::write(&path, script()).expect("write fake trustd");
    let mut permissions = fs::metadata(&path).expect("fake trustd metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("make fake trustd executable");
    // Paid outside the command's 5 s readiness window, as `install` does.
    let warm = Command::new(&path).arg("--version").output().expect("run fake trustd --version");
    assert!(warm.status.success(), "fake trustd --version failed: {warm:?}");
    RefusingTrustd { runtime_dir: private_runtime_dir() }
}

/// The private domain of [`install_refusing`], removed on drop.
#[allow(dead_code)]
pub(crate) struct RefusingTrustd {
    runtime_dir: PathBuf,
}

#[allow(dead_code)]
impl RefusingTrustd {
    /// The private runtime directory the tested command must be given through
    /// [`RUNTIME_DIR_ENV`].
    pub(crate) fn runtime_dir(&self) -> &Path {
        &self.runtime_dir
    }
}

impl Drop for RefusingTrustd {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.runtime_dir);
    }
}

/// Make every stub installed into `bin_dir` from now on sleep `seconds` before
/// it binds: the slowness a loaded host imposes, made deterministic. The stub
/// reads the file itself, so the delay applies whoever starts it.
#[allow(dead_code)] // each including test binary uses a different subset
pub(crate) fn delay_start(bin_dir: &Path, seconds: u32) {
    fs::write(bin_dir.join("trustd.start-delay"), seconds.to_string())
        .expect("write fake trustd start delay");
}

/// A short, private directory under `/tmp`. Short because AF_UNIX paths are
/// limited to ~104 bytes on macOS and the per-session `$TMPDIR` alone uses
/// half of that; `/tmp` is a root-owned sticky ancestor the endpoint rules
/// accept.
fn private_runtime_dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let tmp = fs::canonicalize("/tmp").expect("canonical /tmp");
    for _ in 0..128 {
        let dir = tmp.join(format!(
            "ttd-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match fs::DirBuilder::new().mode(0o700).create(&dir) {
            Ok(()) => {
                fs::set_permissions(&dir, fs::Permissions::from_mode(0o700))
                    .expect("make the per-test runtime directory private");
                return dir;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("create the per-test trustd runtime directory: {error}"),
        }
    }
    panic!("could not allocate a per-test trustd runtime directory")
}

pub(crate) struct FakeTrustd {
    runtime_dir: PathBuf,
    socket: PathBuf,
    /// The stub records the socket it bound here, so a test can prove the
    /// launcher used the private domain rather than the host endpoint.
    served_marker: PathBuf,
    /// The stub `install` started, reaped at teardown.
    stub: Option<Child>,
}

impl FakeTrustd {
    /// The private runtime directory the tested command must be given through
    /// [`RUNTIME_DIR_ENV`].
    pub(crate) fn runtime_dir(&self) -> &Path {
        &self.runtime_dir
    }

    /// Every socket a stub from this toolchain bound, in order: `install`'s
    /// own, then any the command under test spawned.
    #[allow(dead_code)] // each including test binary uses a different subset
    pub(crate) fn served_sockets(&self) -> Vec<PathBuf> {
        fs::read_to_string(&self.served_marker)
            .map(|text| text.lines().map(PathBuf::from).collect())
            .unwrap_or_default()
    }

    /// The endpoint inside [`Self::runtime_dir`].
    #[allow(dead_code)]
    pub(crate) fn socket(&self) -> &Path {
        &self.socket
    }
}

impl Drop for FakeTrustd {
    fn drop(&mut self) {
        // Only this test's private endpoint is ever addressed: nothing here
        // can reach a real daemon, whatever is running on the host.
        if let Ok(mut stream) = UnixStream::connect(&self.socket) {
            let _ = stream.write_all(b"SHUTDOWN\n");
        }
        // Removing the directory is the second way to end a stub: one that
        // missed SHUTDOWN exits when its socket is no longer its own. Then
        // wait for the stub `install` started to exit, rather than for a
        // deadline to pass.
        let _ = fs::remove_dir_all(&self.runtime_dir);
        if let Some(mut stub) = self.stub.take() {
            let started = Instant::now();
            let mut notes = 0;
            // Never panics: this can run while a failed test unwinds.
            while let Ok(None) = stub.try_wait() {
                note_if_still_waiting(started, &mut notes, || {
                    format!("fake trustd pid {} to exit after SHUTDOWN", stub.id())
                });
                thread::sleep(Duration::from_millis(10));
            }
        }
    }
}

fn script() -> String {
    let interpreter_output = Command::new("python3")
        .args(["-c", "import os,sys; print(os.path.realpath(sys.executable))"])
        .output()
        .expect("locate Python 3 for fake trustd");
    assert!(
        interpreter_output.status.success(),
        "Python 3 discovery failed: {}",
        String::from_utf8_lossy(&interpreter_output.stderr)
    );
    let interpreter = String::from_utf8(interpreter_output.stdout)
        .expect("Python 3 path is UTF-8")
        .trim()
        .to_string();
    assert!(
        Path::new(&interpreter).is_absolute()
            && !interpreter.contains('\n')
            && !interpreter.contains('\r'),
        "fake trustd requires an absolute one-line Python path"
    );

    let release =
        serde_json::to_string(option_env!("CFG_RELEASE").unwrap_or(env!("CARGO_PKG_VERSION")))
            .expect("quote fake trustd release");
    let commit = serde_json::to_string(
        option_env!("CFG_VER_HASH").filter(|value| !value.is_empty()).unwrap_or("unbound"),
    )
    .expect("quote fake trustd commit");
    let status_version = serde_json::to_string(trust_router::coordinator::STATUS_VERSION)
        .expect("quote trustd status version");
    let identity_version = serde_json::to_string(trust_router::coordinator::IDENTITY_VERSION)
        .expect("quote trustd identity version");

    r#"#!__PYTHON__
import hashlib
import json
import os
import socket
import sys
import threading
import time

RELEASE = __RELEASE__
COMMIT = __COMMIT__
STATUS_VERSION = __STATUS_VERSION__
IDENTITY_VERSION = __IDENTITY_VERSION__

if sys.argv[1:] == ["--version"]:
    print(f"trustd {RELEASE}")
    print("trust.identity=trustd")
    print(f"trust.protocol={STATUS_VERSION}")
    print(f"commit-hash: {COMMIT}")
    raise SystemExit(0)
if len(sys.argv) != 3 or sys.argv[1] != "--socket" or not sys.argv[2]:
    raise SystemExit(2)

# A test may make this stub refuse every socket (fake_trustd::install_refusing):
# what a live daemon of another build makes a starting trustd say.
refuse_path = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "trustd.refuse")
if os.path.exists(refuse_path):
    sys.stderr.write(f"another trustd owns {sys.argv[2]}\n")
    raise SystemExit(1)

# A test may make this stub slow to start (fake_trustd::delay_start).
delay_path = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "trustd.start-delay")
if os.path.exists(delay_path):
    with open(delay_path) as delay:
        time.sleep(float(delay.read().strip() or "0"))

with open(sys.argv[0], "rb") as executable:
    executable_sha256 = hashlib.sha256(executable.read()).hexdigest()
identity = {
    "version": IDENTITY_VERSION,
    "protocol": STATUS_VERSION,
    "release": RELEASE,
    "commit": COMMIT,
    "executable_sha256": executable_sha256,
}
status = {
    "version": STATUS_VERSION,
    "budget_bytes": 1,
    "reserved_bytes": 0,
    "free_bytes": 1,
    "queue_depth": 0,
    "granted_total": 0,
    "released_total": 0,
    "started_at": 1,
    "active": [],
}
shutdown = threading.Event()
# Live session leases (LEASE), one per connection, as the real daemon keeps
# them: a leased stub takes no idle exit, and a lease ends with its connection.
leases = 0
leases_lock = threading.Lock()

def handle(connection):
    global leases, last_request
    leased = False
    # A client may hang up without reading its reply: `FakeTrustd::drop` writes
    # SHUTDOWN and drops the stream. That ends the conversation, it is not an
    # error. Raising here printed a traceback from a daemon thread while the
    # main loop, just told to shut down, finalized the interpreter, and CPython
    # aborts when a daemon thread holds stderr's lock at shutdown ("could not
    # acquire lock for <_io.BufferedWriter name='<stderr>'> at interpreter
    # shutdown"), which macOS files as a Python crash (measured 2026-09-19).
    with connection:
        stream = connection.makefile("rwb", buffering=0)
        try:
            for raw in stream:
                request = raw.decode("utf-8").rstrip("\r\n")
                if request == "PING":
                    response = "PONG"
                elif request == "LEASE":
                    if leased:
                        response = "ERR outstanding-lease"
                    else:
                        with leases_lock:
                            leases += 1
                        leased = True
                        response = "LEASED"
                elif request == "IDENTITY":
                    response = json.dumps(identity, separators=(",", ":"))
                elif request == "STATUS":
                    response = json.dumps(status, separators=(",", ":"))
                elif request == "SHUTDOWN":
                    response = "OK"
                    shutdown.set()
                else:
                    response = "ERR unsupported"
                stream.write(response.encode("utf-8") + b"\n")
        except (BrokenPipeError, ConnectionResetError):
            return
        finally:
            if leased:
                with leases_lock:
                    leases -= 1
                    # The idle interval restarts when a session ends, as the
                    # real daemon's does.
                    last_request = time.monotonic()

path = sys.argv[2]
executable = sys.argv[0]
# A stub is not the daemon; it must never outlive its test. The real daemon
# idles out after five minutes; thirty seconds is generous for a test. A stub
# the test harness started names its owner instead, and lives exactly as long
# as that process (fake_trustd::install starts it before the command under
# test, which may take longer than any idle allowance to reach it).
IDLE_SECONDS = 30.0
OWNER_PID = int(os.environ.get("TRUST_FAKE_TRUSTD_OWNER_PID", "0") or "0")

def owner_gone():
    if OWNER_PID <= 0:
        return False
    try:
        os.kill(OWNER_PID, 0)
    except ProcessLookupError:
        return True
    except OSError:
        return False
    return False

def live_listener(candidate):
    """True iff something answers at `candidate`. Only the kernel's explicit
    connection-refused result means stale — the same rule the real daemon's
    reclaim uses. Anything ambiguous is treated as live and never touched."""
    probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    probe.settimeout(0.5)
    try:
        probe.connect(candidate)
        return True
    except (ConnectionRefusedError, FileNotFoundError):
        return False
    except OSError:
        return True
    finally:
        probe.close()

# Never unlink a path something else may own. The old stub unlinked
# unconditionally before binding AND on exit, which is how it deleted a live
# production daemon's socket out from under a running gate.
if os.path.lexists(path):
    if live_listener(path):
        sys.stderr.write(f"fake trustd: a live listener already owns {path}; refusing\n")
        raise SystemExit(3)
    os.unlink(path)

listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
listener.settimeout(0.1)
listener.bind(path)
os.chmod(path, 0o600)
listener.listen(8)
with open(os.path.join(os.path.dirname(os.path.abspath(executable)), "trustd.served"), "a") as served:
    served.write(path + "\n")
own = os.stat(path)
own_identity = (own.st_dev, own.st_ino)
last_request = time.monotonic()

def path_is_mine():
    try:
        current = os.stat(path)
    except FileNotFoundError:
        return False
    return (current.st_dev, current.st_ino) == own_identity

try:
    while not shutdown.is_set():
        try:
            connection, _ = listener.accept()
        except socket.timeout:
            # Self-termination, none of which the old stub had: it outlived
            # its test, its temp dir, and its own executable for two days.
            if OWNER_PID > 0:
                if owner_gone():
                    break
            elif time.monotonic() - last_request > IDLE_SECONDS:
                with leases_lock:
                    held = leases > 0
                if not held:
                    break
            if not os.path.exists(executable):
                break
            if not path_is_mine():
                break
            continue
        last_request = time.monotonic()
        threading.Thread(target=handle, args=(connection,), daemon=True).start()
finally:
    listener.close()
    # Unlink only the inode this stub published — never whatever now lives
    # at the path, which may be a real daemon's live socket.
    if path_is_mine():
        try:
            os.unlink(path)
        except FileNotFoundError:
            pass
# Leave without finalizing the interpreter. Handler threads are daemons, so
# one may still be running, and finalization is the one place CPython aborts
# on a stream lock such a thread holds. Nothing is left to flush: stdout is
# unused here and stderr is line-buffered.
os._exit(0)
"#
    .replace("__PYTHON__", &interpreter)
    .replace("__RELEASE__", &release)
    .replace("__COMMIT__", &commit)
    .replace("__STATUS_VERSION__", &status_version)
    .replace("__IDENTITY_VERSION__", &identity_version)
}
