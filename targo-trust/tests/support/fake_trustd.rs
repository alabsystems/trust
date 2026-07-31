#![cfg(unix)]

use std::fs;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, MutexGuard};
use std::thread;
use std::time::Duration;

static TRUSTD_LOCK: Mutex<()> = Mutex::new(());

/// Install a protocol-capable sibling `trustd` and serialize its use of the
/// process-global per-euid endpoint for the lifetime of the returned guard.
///
/// Integration tests use distinct temporary toolchains but the production
/// coordinator intentionally uses one host authority. Keeping this guard alive
/// around the tested command prevents parallel test cases from replacing one
/// another's exact executable identity.
pub(crate) fn install(bin_dir: &Path) -> FakeTrustd {
    let lock = TRUSTD_LOCK.lock().unwrap_or_else(|error| error.into_inner());

    let path = bin_dir.join(format!("trustd{}", std::env::consts::EXE_SUFFIX));
    fs::write(&path, script()).expect("write fake trustd");
    let mut permissions = fs::metadata(&path).expect("fake trustd metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("make fake trustd executable");
    stop_matching_daemon(&path);

    FakeTrustd { _lock: lock, executable: path }
}

pub(crate) struct FakeTrustd {
    _lock: MutexGuard<'static, ()>,
    executable: PathBuf,
}

impl Drop for FakeTrustd {
    fn drop(&mut self) {
        stop_matching_daemon(&self.executable);
    }
}

fn stop_matching_daemon(executable: &Path) {
    let Ok(socket) = trust_router::coordinator::host_socket_path() else {
        return;
    };
    if !trust_router::coordinator::daemon_matches_executable(&socket, executable) {
        return;
    }
    if let Ok(mut stream) = UnixStream::connect(&socket) {
        let _ = stream.write_all(b"SHUTDOWN\n");
    }
    for _ in 0..200 {
        if !socket.exists() {
            return;
        }
        thread::sleep(Duration::from_millis(10));
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

def handle(connection):
    with connection:
        stream = connection.makefile("rwb", buffering=0)
        for raw in stream:
            request = raw.decode("utf-8").rstrip("\r\n")
            if request == "PING":
                response = "PONG"
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

listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
listener.settimeout(0.1)
try:
    os.unlink(sys.argv[2])
except FileNotFoundError:
    pass
listener.bind(sys.argv[2])
os.chmod(sys.argv[2], 0o600)
listener.listen(8)
try:
    while not shutdown.is_set():
        try:
            connection, _ = listener.accept()
        except socket.timeout:
            continue
        threading.Thread(target=handle, args=(connection,), daemon=True).start()
finally:
    listener.close()
    try:
        os.unlink(sys.argv[2])
    except FileNotFoundError:
        pass
"#
    .replace("__PYTHON__", &interpreter)
    .replace("__RELEASE__", &release)
    .replace("__COMMIT__", &commit)
    .replace("__STATUS_VERSION__", &status_version)
    .replace("__IDENTITY_VERSION__", &identity_version)
}
