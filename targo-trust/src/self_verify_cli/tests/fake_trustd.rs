//! The fake stage2 `trustd` endpoint the self-verification identity tests drive.
//!
//! `validate_stage2_toolchain` refuses to accept a stage2 toolchain on a version
//! string alone: it launches `build/host/stage2/bin/trustd --socket <path>`,
//! waits for a closed `IDENTITY`/`STATUS` handshake bound to the exact executable
//! bytes it hashed itself, and then drives the complete
//! `PING`/`IDENTITY`/`STATUS`/`RESERVE`/`RELEASE` release-diagnostic smoke
//! through [`trust_router::coordinator`]'s own client. Nothing short of a live
//! process answering the real protocol satisfies it, so the tests need a real
//! endpoint — not a stub.
//!
//! This module is that endpoint, in Rust:
//!
//! * the installed `trustd` is a five-line `/bin/sh` shim, the same shape the
//!   sibling `targo`/`trustc`/`trustdoc` fakes already use. It answers
//!   `--version`, and for `--socket <path>` it hands that launcher-chosen path to
//!   this process and then blocks, so the launcher observes a live child for the
//!   whole exchange and its process-group kill still reclaims the shim;
//! * every byte on the wire is produced here, by [`serve`], from
//!   `trust_router::coordinator`'s own [`DaemonIdentity`], [`DaemonStatus`] and
//!   [`ActiveReservation`] types and its own [`STATUS_VERSION`],
//!   [`IDENTITY_VERSION`] and [`MAX_REQUEST_BYTES`] constants.
//!
//! That second point is why this module exists. The endpoint used to be a Python
//! script embedded in a Rust string literal: it re-implemented a
//! security-relevant wire protocol in a language the compiler never sees,
//! restated the protocol constants as `__PLACEHOLDER__` text substituted in by
//! `str::replace`, and made a test about stage2 identity depend on an interpreter
//! this toolchain does not own and had to go discover on the host. Here, a
//! renamed or added `DaemonStatus` field is a compile error and a bumped
//! `STATUS_VERSION` moves the fake with the protocol, so the fake cannot silently
//! drift away from what trustd actually speaks.
//!
//! What the endpoint does *not* do is relax anything. It advertises a real
//! admission budget, keeps the reservation ledger internally consistent under the
//! invariants `DaemonStatus::is_semantically_valid` enforces on every reply, and
//! binds its `IDENTITY` to the SHA-256 of the installed file the launcher
//! independently hashes.

use std::path::Path;

#[cfg(unix)]
use std::ffi::CString;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io::{Read as _, Write as _};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt as _;
#[cfg(unix)]
use std::os::unix::fs::{OpenOptionsExt as _, PermissionsExt as _};
#[cfg(unix)]
use std::os::unix::io::AsRawFd as _;
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
#[cfg(unix)]
use std::path::PathBuf;
#[cfg(unix)]
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(unix)]
use std::sync::{Arc, Mutex};
#[cfg(unix)]
use std::thread::{self, JoinHandle};
#[cfg(unix)]
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[cfg(unix)]
use sha2::{Digest as _, Sha256};
use trust_router::coordinator::STATUS_VERSION;
#[cfg(unix)]
use trust_router::coordinator::{
    ActiveReservation, DaemonIdentity, DaemonStatus, IDENTITY_VERSION, MAX_REQUEST_BYTES,
};

/// Admission ceiling this endpoint advertises. `daemon_budget_is_acceptable`
/// requires a nonzero ceiling no larger than the client's own effective-memory
/// budget, and the smoke reserves exactly one byte against it.
#[cfg(unix)]
const BUDGET_BYTES: u64 = 1024;

/// How often the launch watcher looks for a shim hand-off. The launcher polls
/// readiness for five seconds, so this is three orders of magnitude of headroom.
#[cfg(unix)]
const LAUNCH_POLL_INTERVAL: Duration = Duration::from_millis(2);

/// How long an idle `accept` waits before rechecking the stop flag. A connection
/// that arrives during the wait wakes `poll` immediately, so this bounds only
/// shutdown latency, never response latency.
#[cfg(unix)]
const ACCEPT_POLL_TIMEOUT: Duration = Duration::from_millis(20);

/// Bounds a handler parked on a peer that never speaks again: it wakes at this
/// cadence to observe the stop flag. The client's own per-operation deadline is
/// 500ms, so this is not on any answer path.
#[cfg(unix)]
const CONNECTION_READ_TIMEOUT: Duration = Duration::from_millis(50);

/// A peer that stops reading must not pin a handler thread forever.
#[cfg(unix)]
const CONNECTION_WRITE_TIMEOUT: Duration = Duration::from_millis(500);

/// A fake stage2 `trustd` installed at `<repo_root>/build/host/stage2/bin/trustd`
/// and serving for as long as the value is held:
///
/// ```ignore
/// let _trustd = FakeTrustd::install(&root, commit, release);
/// ```
///
/// Dropping it stops the listeners, releases a shim that is still parked, and
/// removes the private rendezvous directory.
pub(super) struct FakeTrustd {
    #[cfg(unix)]
    endpoint: Endpoint,
}

impl FakeTrustd {
    /// Install the endpoint into `repo_root` and start serving.
    ///
    /// `commit` and `release` are the labels it reports from `--version` *and*
    /// binds into its live `IDENTITY`; `validate_stage2_toolchain` rejects the
    /// endpoint outright if the two ever disagree, so they are supplied once.
    pub(super) fn install(repo_root: &Path, commit: &str, release: &str) -> Self {
        assert!(
            is_plain_label(commit) && is_plain_label(release),
            "fake trustd version labels must be plain single-line ASCII: {commit:?} {release:?}"
        );

        #[cfg(unix)]
        {
            let workspace = Workspace::create();
            let executable = super::install_stage2_tool_with_contents(
                repo_root,
                "trustd",
                &shim_script(&workspace, commit, release),
            );
            Self { endpoint: Endpoint::start(workspace, executable, commit, release) }
        }

        #[cfg(not(unix))]
        {
            // trustd's transport is a Unix-domain socket, so there is no live
            // protocol smoke to serve on this host and `live_stage2_trustd_
            // protocol_smoke` records it absent. The `--version` identity the
            // launcher still demands is real.
            let _ = super::install_stage2_tool_with_contents(
                repo_root,
                "trustd",
                &version_only_script(commit, release),
            );
            Self {}
        }
    }
}

/// Version labels are passed to `printf` as shell words, so reject anything that
/// could change a word boundary or the format's meaning.
fn is_plain_label(label: &str) -> bool {
    !label.is_empty()
        && label.len() <= 128
        && label.chars().all(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '_')
        })
}

/// The exact `--version` block `parse_trustd_version_identity` accepts, with the
/// protocol reported from the constant itself rather than a copy of its text.
///
/// The labels are `printf` *arguments*, never part of its format string.
fn version_block(commit: &str, release: &str) -> String {
    format!(
        "printf 'trustd %s\\ntrust.identity=trustd\\ntrust.protocol=%s\\ncommit-hash: %s\\n' \
         '{release}' '{STATUS_VERSION}' '{commit}'\n"
    )
}

#[cfg(not(unix))]
fn version_only_script(commit: &str, release: &str) -> String {
    format!(
        "#!/bin/sh\nif [ \"$#\" -eq 1 ] && [ \"$1\" = \"--version\" ]; then\n    {}    exit 0\nfi\nexit 2\n",
        version_block(commit, release),
    )
}

/// The installed endpoint.
///
/// `--version` is answered here, in the same `printf` shape the sibling stage2
/// fakes use. `--socket <path>` publishes the launcher-chosen path to this
/// process and then parks on a FIFO nothing writes to, using only shell builtins
/// — the launcher clears the environment, so the shim may not depend on `PATH`
/// resolving a single external command.
#[cfg(unix)]
fn shim_script(workspace: &Workspace, commit: &str, release: &str) -> String {
    let root = workspace.quoted_root();
    format!(
        "#!/bin/sh\n\
         if [ \"$#\" -eq 1 ] && [ \"$1\" = \"--version\" ]; then\n    \
             {version}    exit 0\n\
         fi\n\
         if [ \"$#\" -ne 2 ] || [ \"$1\" != \"--socket\" ] || [ -z \"$2\" ]; then\n    \
             exit 2\n\
         fi\n\
         printf '%s\\n' \"$2\" > {root}/launches/\"$$\"\n\
         read parked < {root}/hold\n\
         exit 0\n",
        version = version_block(commit, release),
    )
}

/// Private scratch space shared with the shim: a directory the shim drops
/// launcher-chosen socket paths into, and a FIFO it parks on afterwards.
#[cfg(unix)]
struct Workspace {
    directory: tempfile::TempDir,
}

#[cfg(unix)]
impl Workspace {
    fn create() -> Self {
        let directory = tempfile::Builder::new()
            .prefix("trust-self-verify-fake-trustd-")
            .tempdir()
            .expect("create fake trustd workspace");
        fs::set_permissions(directory.path(), fs::Permissions::from_mode(0o700))
            .expect("make fake trustd workspace owner-private");
        let workspace = Self { directory };
        fs::create_dir(workspace.launches()).expect("create fake trustd launch directory");
        let hold = CString::new(workspace.hold().as_os_str().as_bytes())
            .expect("fake trustd hold FIFO path");
        // SAFETY: `hold` is a live NUL-terminated path in a directory this
        // process just created and owns.
        assert_eq!(
            unsafe { libc::mkfifo(hold.as_ptr(), 0o600) },
            0,
            "create fake trustd hold FIFO: {}",
            std::io::Error::last_os_error()
        );
        workspace
    }

    fn launches(&self) -> PathBuf {
        self.directory.path().join("launches")
    }

    fn hold(&self) -> PathBuf {
        self.directory.path().join("hold")
    }

    /// The workspace root as one single-quoted shell word.
    ///
    /// `tempfile` builds this path from the ambient temporary directory, which is
    /// not this module's to choose, so refuse outright rather than emit a shim
    /// whose meaning depends on how the shell re-splits it.
    fn quoted_root(&self) -> String {
        let root = self.directory.path().to_str().expect("fake trustd workspace path is UTF-8");
        assert!(
            !root.contains(['\'', '\n', '\r']),
            "fake trustd workspace path is not representable as one shell word: {root:?}"
        );
        format!("'{root}'")
    }
}

/// The live endpoint: a watcher thread that turns each shim launch into a bound
/// listener, plus everything those listeners need to answer as exactly the
/// installed stage2 bytes.
#[cfg(unix)]
struct Endpoint {
    control: Arc<Control>,
    watcher: Option<JoinHandle<()>>,
}

#[cfg(unix)]
struct Control {
    stop: AtomicBool,
    workspace: Workspace,
    /// The installed file whose bytes every `IDENTITY` reply must bind.
    executable: PathBuf,
    release: String,
    commit: String,
    listeners: Mutex<Vec<JoinHandle<()>>>,
}

#[cfg(unix)]
impl Control {
    /// The identity a trustd running *these* bytes reports. Hashing the installed
    /// file, rather than asserting a digest, is what makes the smoke a real
    /// byte-binding: the launcher independently hashes the same file and refuses
    /// any endpoint whose reply differs.
    fn identity(&self) -> Option<DaemonIdentity> {
        let bytes = fs::read(&self.executable).ok()?;
        Some(DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: self.release.clone(),
            commit: self.commit.clone(),
            executable_sha256: format!("{:x}", Sha256::digest(&bytes)),
        })
    }

    fn stopped(&self) -> bool {
        self.stop.load(Ordering::SeqCst)
    }
}

#[cfg(unix)]
impl Endpoint {
    fn start(workspace: Workspace, executable: PathBuf, commit: &str, release: &str) -> Self {
        let control = Arc::new(Control {
            stop: AtomicBool::new(false),
            workspace,
            executable,
            release: release.to_string(),
            commit: commit.to_string(),
            listeners: Mutex::new(Vec::new()),
        });
        let watcher = {
            let control = Arc::clone(&control);
            thread::Builder::new()
                .name("fake-trustd-watcher".to_string())
                .spawn(move || watch_for_launches(&control))
                .expect("spawn fake trustd watcher")
        };
        Self { control, watcher: Some(watcher) }
    }
}

#[cfg(unix)]
impl Drop for Endpoint {
    fn drop(&mut self) {
        self.control.stop.store(true, Ordering::SeqCst);
        // Release a shim still parked on the FIFO. Opening the write end without
        // a reader fails with ENXIO, which is exactly the "nothing is parked"
        // case, so the non-blocking open doubles as the probe.
        if let Ok(mut hold) = fs::OpenOptions::new()
            .write(true)
            .custom_flags(libc::O_NONBLOCK)
            .open(self.control.workspace.hold())
        {
            let _ = hold.write_all(b"\n");
        }
        // Join the watcher first: once it is gone no further listener can be
        // pushed, so draining the list below cannot race a spawn.
        if let Some(watcher) = self.watcher.take() {
            let _ = watcher.join();
        }
        let listeners = std::mem::take(
            &mut *self.control.listeners.lock().unwrap_or_else(|poisoned| poisoned.into_inner()),
        );
        for listener in listeners {
            let _ = listener.join();
        }
    }
}

/// Serve every socket path the shim publishes. Each launch is a distinct daemon
/// lifetime and therefore starts from fresh, empty admission state.
#[cfg(unix)]
fn watch_for_launches(control: &Arc<Control>) {
    let launches = control.workspace.launches();
    while !control.stopped() {
        if let Ok(entries) = fs::read_dir(&launches) {
            for entry in entries.flatten() {
                let path = entry.path();
                let Ok(contents) = fs::read_to_string(&path) else { continue };
                // The shim writes one short line with a single `printf`. Anything
                // without the terminator is a torn read of a write still in
                // flight, so leave it for the next tick.
                let Some(socket) = contents.strip_suffix('\n') else { continue };
                // Claim the launch before acting on it, so a failed removal can
                // never start two listeners for one socket.
                if fs::remove_file(&path).is_err() {
                    continue;
                }
                let socket = PathBuf::from(socket);
                let owned = Arc::clone(control);
                let listener = thread::Builder::new()
                    .name("fake-trustd-listener".to_string())
                    .spawn(move || serve(&owned, &socket))
                    .expect("spawn fake trustd listener");
                control
                    .listeners
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner())
                    .push(listener);
            }
        }
        thread::sleep(LAUNCH_POLL_INTERVAL);
    }
}

/// The admission ledger of one daemon lifetime.
///
/// The client revalidates `DaemonStatus`'s own invariants on every single reply —
/// `free == budget - reserved`, `granted_total - released_total == active.len()`,
/// `Σ active.bytes == reserved`, unique nonzero tokens — so this state must stay
/// coherent, not merely well-typed.
#[cfg(unix)]
struct State {
    reserved_bytes: u64,
    granted_total: u64,
    released_total: u64,
    started_at: u64,
    next_token: u64,
    active: Vec<ActiveReservation>,
}

#[cfg(unix)]
impl State {
    fn new() -> Self {
        Self {
            reserved_bytes: 0,
            granted_total: 0,
            released_total: 0,
            started_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|since| since.as_secs())
                .unwrap_or_default()
                .max(1),
            next_token: 1,
            active: Vec::new(),
        }
    }

    fn snapshot(&self) -> DaemonStatus {
        DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: BUDGET_BYTES,
            reserved_bytes: self.reserved_bytes,
            free_bytes: BUDGET_BYTES.saturating_sub(self.reserved_bytes),
            queue_depth: 0,
            granted_total: self.granted_total,
            released_total: self.released_total,
            started_at: self.started_at,
            active: self.active.clone(),
        }
    }

    fn reserve(&mut self, bytes: u64, pid: u32, label: &str) -> String {
        if bytes == 0 || self.reserved_bytes.saturating_add(bytes) > BUDGET_BYTES {
            return "DEGRADED".to_string();
        }
        let token = self.next_token;
        self.next_token += 1;
        self.reserved_bytes += bytes;
        self.granted_total += 1;
        self.active.push(ActiveReservation {
            pid,
            bytes,
            label: label.to_string(),
            // Diagnostic-only in STATUS v1. A fixed value keeps replies
            // deterministic without weakening an invariant the client checks.
            since_secs: 0,
            token,
        });
        format!("GRANTED {token}")
    }

    fn release(&mut self, token: u64) {
        let Some(position) = self.active.iter().position(|active| active.token == token) else {
            return;
        };
        let released = self.active.remove(position);
        self.reserved_bytes -= released.bytes;
        self.released_total += 1;
    }
}

/// Bind, publish and serve one daemon lifetime at `socket`.
#[cfg(unix)]
fn serve(control: &Arc<Control>, socket: &Path) {
    // A daemon that cannot bind its own executable's bytes must not answer at
    // all: an endpoint that skipped the digest is precisely the unbound endpoint
    // the launcher exists to refuse.
    let Some(identity) = control.identity() else { return };
    let Some(listener) = bind_private(socket) else { return };
    if listener.set_nonblocking(true).is_err() {
        return;
    }
    let state = Arc::new(Mutex::new(State::new()));
    let mut connections: Vec<JoinHandle<()>> = Vec::new();
    while !control.stopped() {
        match listener.accept() {
            Ok((stream, _)) => {
                let control = Arc::clone(control);
                let state = Arc::clone(&state);
                let identity = identity.clone();
                match thread::Builder::new()
                    .name("fake-trustd-connection".to_string())
                    .spawn(move || handle(&control, &state, &identity, stream))
                {
                    Ok(connection) => connections.push(connection),
                    Err(_) => break,
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                // The launcher owns the endpoint's private directory and removes
                // it once the smoke is over. That teardown ends this daemon
                // lifetime, exactly as an unlinked rendezvous ends a real one.
                if fs::symlink_metadata(socket).is_err() {
                    break;
                }
                wait_readable(listener.as_raw_fd(), ACCEPT_POLL_TIMEOUT);
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => break,
        }
    }
    for connection in connections {
        let _ = connection.join();
    }
}

/// Block until `descriptor` is readable or `timeout` elapses.
#[cfg(unix)]
fn wait_readable(descriptor: std::os::unix::io::RawFd, timeout: Duration) {
    let mut watched = libc::pollfd { fd: descriptor, events: libc::POLLIN, revents: 0 };
    let milliseconds = i32::try_from(timeout.as_millis()).unwrap_or(i32::MAX);
    // SAFETY: exactly one initialized `pollfd` is passed with a matching count,
    // and the descriptor is owned by the caller for the duration of the call.
    unsafe {
        libc::poll(&mut watched, 1, milliseconds);
    }
}

/// Bind `socket` and publish it owner-private, the way trustd's own
/// `PrivateSocketStage` does: a client must never observe the rendezvous name
/// while the endpoint behind it is still group- or world-reachable.
#[cfg(unix)]
fn bind_private(socket: &Path) -> Option<UnixListener> {
    // `sun_path` is 104 bytes on Darwin and the launcher already spends most of
    // it on its private directory, so stage under the shortest name available in
    // that same directory rather than a longer sibling.
    let staging = socket.parent()?.join(".s");
    let _ = fs::remove_file(&staging);
    let listener = UnixListener::bind(&staging).ok()?;
    fs::set_permissions(&staging, fs::Permissions::from_mode(0o600)).ok()?;
    fs::rename(&staging, socket).ok()?;
    Some(listener)
}

/// One connection: request lines in, one reply line out, until EOF.
#[cfg(unix)]
fn handle(
    control: &Arc<Control>,
    state: &Arc<Mutex<State>>,
    identity: &DaemonIdentity,
    mut stream: UnixStream,
) {
    if stream.set_nonblocking(false).is_err()
        || stream.set_read_timeout(Some(CONNECTION_READ_TIMEOUT)).is_err()
        || stream.set_write_timeout(Some(CONNECTION_WRITE_TIMEOUT)).is_err()
    {
        return;
    }
    let mut pending: Vec<u8> = Vec::new();
    let mut chunk = [0_u8; 512];
    while !control.stopped() {
        if let Some(end) = pending.iter().position(|byte| *byte == b'\n') {
            let line = pending.drain(..=end).collect::<Vec<u8>>();
            let request = String::from_utf8_lossy(&line);
            let response = respond(state, identity, request.trim_end_matches(['\r', '\n']));
            if stream.write_all(response.as_bytes()).is_err() || stream.write_all(b"\n").is_err() {
                return;
            }
            continue;
        }
        // The same request bound the real daemon enforces.
        if pending.len() > MAX_REQUEST_BYTES {
            let _ = stream.write_all(b"ERR line-too-long\n");
            return;
        }
        match stream.read(&mut chunk) {
            Ok(0) => return,
            Ok(read) => pending.extend_from_slice(&chunk[..read]),
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::WouldBlock
                        | std::io::ErrorKind::TimedOut
                        | std::io::ErrorKind::Interrupted
                ) => {}
            Err(_) => return,
        }
    }
}

/// The wire protocol itself.
#[cfg(unix)]
fn respond(state: &Arc<Mutex<State>>, identity: &DaemonIdentity, request: &str) -> String {
    let locked = || state.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if request == "PING" {
        return "PONG".to_string();
    }
    if request == "IDENTITY" {
        return serde_json::to_string(identity).expect("serialize fake trustd IDENTITY");
    }
    if request == "STATUS" {
        return serde_json::to_string(&locked().snapshot()).expect("serialize fake trustd STATUS");
    }
    if let Some(arguments) = request.strip_prefix("RESERVE ") {
        // `RESERVE <bytes> <pid> <label>`; the label is the remainder and may
        // itself contain spaces.
        let mut fields = arguments.splitn(3, ' ');
        let parsed = (|| {
            let bytes: u64 = fields.next()?.parse().ok()?;
            let pid: u32 = fields.next()?.parse().ok()?;
            let label = fields.next()?;
            Some((bytes, pid, label))
        })();
        return match parsed {
            Some((bytes, pid, label)) => locked().reserve(bytes, pid, label),
            None => "ERR malformed".to_string(),
        };
    }
    if let Some(token) = request.strip_prefix("RELEASE ") {
        if let Ok(token) = token.trim().parse::<u64>() {
            locked().release(token);
        }
        return "OK".to_string();
    }
    "ERR unsupported".to_string()
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::time::Instant;

    /// Drive the endpoint with the exact client `validate_stage2_toolchain` uses,
    /// without going through `exec`.
    ///
    /// The two stage2 identity tests are the real users, but they can only reach
    /// this code by launching four freshly written stage2 fakes, so a protocol
    /// regression surfaces there mixed with everything else the launcher checks.
    /// This pins the endpoint on its own: a real socket, real bytes on the wire,
    /// and `trust_router::coordinator`'s own smoke — which recomputes the
    /// executable digest, rejects a contradictory `STATUS`, and validates the
    /// whole reserve/release transition — as the judge.
    #[test]
    fn fake_endpoint_answers_the_real_trustd_release_diagnostic_smoke() {
        let commit = "0123456789abcdef0123456789abcdef01234567";
        let release = "1.99.0-test";
        let repo_root = tempfile::Builder::new()
            .prefix("fake-trustd-unit-")
            .tempdir()
            .expect("fake trustd unit repository root");
        let trustd = FakeTrustd::install(repo_root.path(), commit, release);
        let executable = trustd.endpoint.control.executable.clone();

        // Stand in for the launcher: a private endpoint directory, and the socket
        // path handed to the shim.
        let endpoint_root = tempfile::Builder::new()
            .prefix("fake-trustd-unit-endpoint-")
            .tempdir()
            .expect("fake trustd unit endpoint root");
        fs::set_permissions(endpoint_root.path(), fs::Permissions::from_mode(0o700))
            .expect("private endpoint directory");
        let socket = endpoint_root.path().join("trustd.sock");
        fs::write(
            trustd.endpoint.control.workspace.launches().join("1"),
            format!("{}\n", socket.display()),
        )
        .expect("publish a launch to the fake trustd watcher");

        let expected = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: release.to_string(),
            commit: commit.to_string(),
            executable_sha256: format!(
                "{:x}",
                Sha256::digest(fs::read(&executable).expect("installed fake trustd"))
            ),
        };
        let deadline = Instant::now() + Duration::from_secs(5);
        while !trust_router::coordinator::daemon_matches_bound_identity(
            &socket,
            &executable,
            &expected,
        ) {
            assert!(Instant::now() < deadline, "fake trustd never became IDENTITY/STATUS ready");
            thread::sleep(Duration::from_millis(10));
        }

        let smoke = trust_router::coordinator::exercise_daemon_at_with_identity(
            &socket,
            &executable,
            &expected,
            "fake-trustd-unit-smoke",
        )
        .expect("fake trustd answered the complete release-diagnostic smoke");
        assert_eq!(smoke.identity, expected);
        assert_eq!(smoke.reservation_bytes, 1);
        assert_eq!(smoke.reservation_label, "fake-trustd-unit-smoke");
        assert_eq!(smoke.reservation_pid, std::process::id());
        assert!(smoke.reservation_token > 0);
        assert_eq!(smoke.status_before.version, STATUS_VERSION);
        assert_eq!(smoke.status_before.reserved_bytes, 0);
        assert_eq!(smoke.status_reserved.reserved_bytes, 1);
        assert_eq!(smoke.status_released.reserved_bytes, 0);
        assert_eq!(smoke.status_released.released_total, 1);

        // The `--version` block and the live IDENTITY must agree; the launcher
        // rejects the endpoint when they do not, so pin the parse here too.
        let version = crate::self_verify_cli::parse_trustd_version_identity(&format!(
            "trustd {release}\ntrust.identity=trustd\ntrust.protocol={STATUS_VERSION}\ncommit-hash: {commit}\n"
        ))
        .expect("fake trustd --version block parses as a stage2 trustd identity");
        assert_eq!(version.release, smoke.identity.release);
        assert_eq!(version.commit, smoke.identity.commit);
        assert_eq!(version.protocol, smoke.identity.protocol);
    }
}
