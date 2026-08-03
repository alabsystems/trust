//! Environment names that carry Cargo/Targo process authority.
//!
//! Project configuration and build-script `cargo::rustc-env` output reach
//! compiler processes through different paths.  Keep one portable classifier
//! for both boundaries so a name rejected in `[env]` cannot be reintroduced
//! later by a build script.
//!
//! Trust: this whole module is Trust-authored and has no upstream Cargo
//! counterpart — Cargo treats the child environment as configuration, whereas a
//! verified build treats it as an authority channel. It is a separate module,
//! rather than checks placed where each variable is set, so that every boundary
//! that can reach a compiler process (`[env]` config, build-script output, the
//! `cargo fix` proxy, the dynamic-loader environment) is answered by one
//! classifier. Adding a name in only one of those places is the failure mode
//! this exists to prevent.
//!
//! Nothing here is called from upstream code paths except through the explicit
//! entry points re-exported to `core::compiler`, so a cargo re-align cannot
//! silently drop it — it will fail to compile instead.

use super::tippy_arg_protocol::is_protected_tippy_arg_env;
use anyhow::Context as _;
use cargo_util::{ProcessBuilder, paths};
use std::ffi::{OsStr, OsString};
#[cfg(target_os = "linux")]
use std::io::{Read as _, Write as _};
#[cfg(target_os = "linux")]
use std::mem::size_of;
#[cfg(target_os = "linux")]
use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
#[cfg(target_os = "linux")]
use std::os::unix::fs::OpenOptionsExt as _;
#[cfg(target_os = "linux")]
use std::os::unix::net::{SocketAddr, UnixListener, UnixStream};
use std::path::{Path, PathBuf};
// Trust: the pathname-authority ledgers (pinned launcher digests, scanned
// runtime directories, printed disclosures) are process-wide on every platform.
use std::sync::Mutex;
use std::sync::OnceLock;
#[cfg(target_os = "linux")]
use std::time::Duration;

use crate::CargoResult;
use crate::util::file_identity::metadata_is_plain_directory;

pub(crate) const CARGO_PRIMARY_PACKAGE_ENV: &str = "CARGO_PRIMARY_PACKAGE";
pub(crate) const RUSTC_WORKSPACE_WRAPPER_ENV: &str = "RUSTC_WORKSPACE_WRAPPER";
pub(crate) const TARGO_NESTED_UNVERIFIED_BROKER_ENV: &str = "TRUST_TARGO_NESTED_UNVERIFIED_BROKER";

#[cfg(target_os = "linux")]
const TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA: &[u8] = b"trust-targo-nested-unverified-request-v3";
#[cfg(target_os = "linux")]
const TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA: &[u8] = b"trust-targo-nested-unverified-response-v3";
#[cfg(target_os = "linux")]
const TARGO_NESTED_UNVERIFIED_NONCE_BYTES: usize = 16;
#[cfg(target_os = "linux")]
const TARGO_NESTED_UNVERIFIED_HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(2);

/// Trust: a live authority service created only by the exact
/// `ExplicitUnverified` CLI lane.
///
/// The abstract socket address is deliberately not authority. Each nested Targo must
/// open a fresh connection and authenticate a live response from this process;
/// the broker independently authenticates that requester's PID, executable,
/// and ancestry. The nested client creates an unpredictable one-shot callback;
/// the process actively connecting back is authenticated with `SO_PEERCRED`.
/// A helper retaining a socket prepared before exec is therefore identified as
/// the helper rather than the now-execed Targo ancestor.
///
/// This is a process-boundary capability, not an attestation of an
/// uncompromised process image. Code already injected into the ancestor Targo
/// process can act with that process's PID and opened executable identity; no
/// in-process protocol can distinguish it from Targo itself.
#[cfg(target_os = "linux")]
#[derive(Debug)]
struct NestedUnverifiedTargoBroker {
    endpoint: OsString,
    _thread: std::thread::JoinHandle<()>,
}

#[cfg(target_os = "linux")]
static NESTED_UNVERIFIED_TARGO_BROKER: Mutex<Option<NestedUnverifiedTargoBroker>> =
    Mutex::new(None);
static INHERITED_NESTED_UNVERIFIED_TARGO_BROKER: OnceLock<OsString> = OnceLock::new();

/// Trust: authenticate inherited explicit-unverified authority before Cargo
/// loads project or user configuration.
///
/// An ambient address is never authority. Linux requires a fresh,
/// bidirectionally authenticated exchange with a live Targo ancestor. Other
/// hosts reject attempted propagation until equivalent process-handle and
/// executable-handle authentication is implemented.
#[expect(
    clippy::disallowed_methods,
    reason = "startup authentication must inspect the environment inherited across exec before GlobalContext construction"
)]
pub(crate) fn prepare_nested_unverified_targo_handoff() -> CargoResult<()> {
    if !crate::is_targo_invocation() {
        return Ok(());
    }
    let Some(endpoint) = std::env::var_os(TARGO_NESTED_UNVERIFIED_BROKER_ENV) else {
        return Ok(());
    };

    #[cfg(target_os = "linux")]
    {
        if INHERITED_NESTED_UNVERIFIED_TARGO_BROKER.get().is_some() {
            anyhow::bail!("nested Targo unverified authority was initialized more than once");
        }
        authenticate_nested_unverified_targo_broker(&endpoint)?;
        INHERITED_NESTED_UNVERIFIED_TARGO_BROKER
            .set(endpoint)
            .map_err(|_| {
                anyhow::anyhow!("nested Targo unverified authority was initialized more than once")
            })?;
        Ok(())
    }

    #[cfg(not(target_os = "linux"))]
    {
        let _ = endpoint;
        reject_unsupported_nested_unverified_targo_handoff()
    }
}

#[cfg(not(target_os = "linux"))]
fn reject_unsupported_nested_unverified_targo_handoff() -> CargoResult<()> {
    anyhow::bail!(
        "nested unverified Targo handoff is unavailable on this platform because live process-handle, executable-handle, and ancestry authentication are not implemented"
    )
}

/// Whether startup accepted live explicit-unverified authority from a Targo
/// ancestor.
pub(crate) fn nested_unverified_targo_handoff_active() -> bool {
    INHERITED_NESTED_UNVERIFIED_TARGO_BROKER.get().is_some()
}

/// Whether this process owns the live broker thread and therefore must not
/// replace itself with a `cargo run` target.
///
/// An inherited Targo may still use exec replacement: its broker lives in the
/// original explicit-unverified ancestor. Only the root broker owner must stay
/// alive to preserve the authority service for programs that invoke `$CARGO`.
pub(crate) fn nested_unverified_targo_root_broker_active() -> CargoResult<bool> {
    #[cfg(target_os = "linux")]
    {
        let broker = NESTED_UNVERIFIED_TARGO_BROKER
            .lock()
            .map_err(|_| anyhow::anyhow!("nested-unverified Targo broker lock was poisoned"))?;
        Ok(broker.is_some())
    }

    #[cfg(not(target_os = "linux"))]
    Ok(false)
}

/// Trust: create the broker only after the CLI policy selected the exact
/// `ExplicitUnverified` authorization variant.
///
/// This must not be called from inherited, fix-proxy, bootstrap, verified, or
/// process-local boolean lanes.
pub(crate) fn start_explicit_unverified_targo_broker() -> CargoResult<()> {
    if !crate::is_targo_invocation() {
        anyhow::bail!("ordinary Cargo cannot start Targo unverified authority");
    }
    if nested_unverified_targo_handoff_active() {
        anyhow::bail!("inherited Targo authority cannot mint a replacement root broker");
    }

    #[cfg(target_os = "linux")]
    {
        let mut broker = NESTED_UNVERIFIED_TARGO_BROKER
            .lock()
            .map_err(|_| anyhow::anyhow!("nested-unverified Targo broker lock was poisoned"))?;
        if broker.is_some() {
            anyhow::bail!("explicit-unverified Targo broker was initialized more than once");
        }
        match NestedUnverifiedTargoBroker::start() {
            Ok(started) => *broker = Some(started),
            Err(error) => {
                eprintln!(
                    "warning: nested explicit-unverified Targo propagation is unavailable: {error:#}; the outer explicit command remains authorized, but recursive `$CARGO` invocations must select their own lane"
                );
            }
        }
        Ok(())
    }

    #[cfg(not(target_os = "linux"))]
    {
        eprintln!(
            "warning: nested explicit-unverified Targo propagation is unavailable on this platform; the outer explicit command remains authorized, but recursive `$CARGO` invocations must select their own lane"
        );
        Ok(())
    }
}

/// Attach explicit-unverified authority to one Cargo-owned child command.
///
/// Root invocations expose the broker created by the exact explicit CLI lane.
/// Nested invocations re-expose only an endpoint already authenticated at
/// startup. Every other lane removes the inert address marker.
pub(crate) fn configure_nested_unverified_targo_child(
    command: &mut ProcessBuilder,
) -> CargoResult<()> {
    if !crate::is_targo_invocation() {
        return Ok(());
    }
    command.env_remove(TARGO_NESTED_UNVERIFIED_BROKER_ENV);
    if !crate::trust_no_verify_fast() {
        return Ok(());
    }

    if let Some(endpoint) = INHERITED_NESTED_UNVERIFIED_TARGO_BROKER.get() {
        command.env(TARGO_NESTED_UNVERIFIED_BROKER_ENV, endpoint);
        return Ok(());
    }

    #[cfg(target_os = "linux")]
    {
        let broker = NESTED_UNVERIFIED_TARGO_BROKER
            .lock()
            .map_err(|_| anyhow::anyhow!("nested-unverified Targo broker lock was poisoned"))?;
        if let Some(broker) = broker.as_ref() {
            command.env(TARGO_NESTED_UNVERIFIED_BROKER_ENV, &broker.endpoint);
        }
        return Ok(());
    }

    #[cfg(not(target_os = "linux"))]
    Ok(())
}

#[cfg(target_os = "linux")]
impl NestedUnverifiedTargoBroker {
    fn start() -> CargoResult<Self> {
        use std::os::linux::net::SocketAddrExt as _;

        let nonce = random_nested_unverified_nonce()
            .context("failed to generate nested-unverified Targo broker address")?;
        let endpoint = OsString::from(format!(
            "trust-targo-unverified-{}-{}",
            std::process::id(),
            hex::encode(nonce)
        ));
        let address = SocketAddr::from_abstract_name(endpoint.as_encoded_bytes())
            .context("failed to construct nested-unverified Targo abstract socket address")?;
        let listener = UnixListener::bind_addr(&address)
            .context("failed to bind nested-unverified Targo broker")?;
        let root_pid = std::process::id();
        let root = LinuxProcessGuard::capture(root_pid, ExecutableCapture::Required)?;
        let thread = std::thread::Builder::new()
            .name("targo-unverified-authority".to_owned())
            .spawn(move || serve_nested_unverified_targo_broker(listener, root))
            .context("failed to start nested-unverified Targo broker")?;
        Ok(Self {
            endpoint,
            _thread: thread,
        })
    }
}

#[cfg(target_os = "linux")]
fn serve_nested_unverified_targo_broker(listener: UnixListener, root: LinuxProcessGuard) {
    for connection in listener.incoming() {
        let Ok(mut connection) = connection else {
            break;
        };
        if let Err(error) = handle_nested_unverified_targo_request(&mut connection, &root) {
            tracing::debug!("rejected nested-unverified Targo broker request: {error:#}");
        }
    }
}

#[cfg(target_os = "linux")]
fn handle_nested_unverified_targo_request(
    connection: &mut UnixStream,
    root: &LinuxProcessGuard,
) -> CargoResult<()> {
    configure_nested_unverified_targo_stream(connection)?;
    let peer_pid = nested_unverified_socket_peer_pid(connection.as_raw_fd())?;
    // Bind the kernel-reported numeric peer PID to a pidfd, start time, and
    // opened executable before any attacker-controlled frame read can block.
    let peer = LinuxProcessGuard::capture(peer_pid, ExecutableCapture::Required)?;
    let request = receive_nested_unverified_frame(
        connection,
        TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA.len()
            + size_of::<u32>()
            + TARGO_NESTED_UNVERIFIED_NONCE_BYTES,
        "request",
    )?;
    let (requester_pid, nonce) = parse_nested_unverified_request(&request)?;
    if requester_pid != peer_pid {
        anyhow::bail!(
            "nested-unverified Targo request names pid {requester_pid}, but the kernel peer is pid {peer_pid}"
        );
    }
    let peer = validate_captured_nested_unverified_targo_process(peer, root)?;
    ensure_nested_unverified_ancestor(root, peer_pid)?;
    peer.ensure_live()?;
    ensure_nested_unverified_ancestor(root, peer_pid)?;

    let callback_address = nested_unverified_callback_address(&nonce)?;
    let mut callback = UnixStream::connect_addr(&callback_address)
        .context("failed to connect nested-unverified Targo one-shot callback")?;
    configure_nested_unverified_targo_stream(&callback)?;
    let response = nested_unverified_response(root.pid, requester_pid, &nonce);
    callback
        .write_all(&response)
        .context("failed to write nested-unverified Targo callback response")?;
    callback
        .shutdown(std::net::Shutdown::Write)
        .context("failed to frame nested-unverified Targo callback response")?;
    peer.ensure_parent_unchanged()?;
    root.ensure_live()?;
    ensure_nested_unverified_ancestor(root, peer_pid)?;
    Ok(())
}

#[cfg(target_os = "linux")]
fn authenticate_nested_unverified_targo_broker(endpoint: &OsStr) -> CargoResult<()> {
    use std::os::linux::net::SocketAddrExt as _;

    let nonce = random_nested_unverified_nonce()
        .context("failed to generate nested-unverified Targo callback challenge")?;
    let callback_address = nested_unverified_callback_address(&nonce)?;
    let callback_listener = UnixListener::bind_addr(&callback_address)
        .context("failed to bind nested-unverified Targo one-shot callback")?;
    let current_pid = std::process::id();
    let current = LinuxProcessGuard::capture(current_pid, ExecutableCapture::Required)?;

    let address = SocketAddr::from_abstract_name(endpoint.as_encoded_bytes())
        .context("invalid nested-unverified Targo abstract socket address")?;
    let mut connection = UnixStream::connect_addr(&address).with_context(|| {
        format!(
            "failed to connect to nested-unverified Targo broker `{}`",
            endpoint.to_string_lossy()
        )
    })?;
    configure_nested_unverified_targo_stream(&connection)?;

    let request = nested_unverified_request(current_pid, &nonce);
    connection
        .write_all(&request)
        .context("failed to write nested-unverified Targo broker request")?;
    connection
        .shutdown(std::net::Shutdown::Write)
        .context("failed to frame nested-unverified Targo broker request")?;

    wait_for_nested_unverified_callback(&callback_listener)?;
    let (mut callback, _) = callback_listener
        .accept()
        .context("failed to accept nested-unverified Targo one-shot callback")?;
    configure_nested_unverified_targo_stream(&callback)?;
    let response_sender = nested_unverified_socket_peer_pid(callback.as_raw_fd())?;
    // As on the server side, capture a stable process identity immediately
    // after SO_PEERCRED and before reading attacker-controlled bytes.
    let root = LinuxProcessGuard::capture(response_sender, ExecutableCapture::Required)?;
    let response = receive_nested_unverified_frame(
        &mut callback,
        TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA.len()
            + 2 * size_of::<u32>()
            + TARGO_NESTED_UNVERIFIED_NONCE_BYTES,
        "response",
    )?;
    let (response_root, response_requester, response_nonce) =
        parse_nested_unverified_response(&response)?;
    if response_requester != current_pid {
        anyhow::bail!(
            "nested-unverified Targo broker response is bound to requester {response_requester}, expected {current_pid}"
        );
    }
    if response_sender != response_root {
        anyhow::bail!(
            "nested-unverified Targo callback names root pid {response_root}, but its live callback peer is pid {response_sender}"
        );
    }
    if response_nonce != nonce {
        anyhow::bail!("nested-unverified Targo callback returned the wrong one-shot challenge");
    }
    let root = validate_captured_nested_unverified_targo_process(root, &current)?;
    ensure_nested_unverified_ancestor(&root, current_pid)?;
    current.ensure_parent_unchanged()?;
    root.ensure_live()?;
    ensure_nested_unverified_ancestor(&root, current_pid)?;
    Ok(())
}

#[cfg(target_os = "linux")]
fn configure_nested_unverified_targo_stream(stream: &UnixStream) -> CargoResult<()> {
    stream
        .set_read_timeout(Some(TARGO_NESTED_UNVERIFIED_HANDSHAKE_TIMEOUT))
        .context("failed to bound nested-unverified Targo broker reads")?;
    stream
        .set_write_timeout(Some(TARGO_NESTED_UNVERIFIED_HANDSHAKE_TIMEOUT))
        .context("failed to bound nested-unverified Targo broker writes")?;
    Ok(())
}

#[cfg(target_os = "linux")]
fn random_nested_unverified_nonce() -> CargoResult<[u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES]> {
    let mut nonce = [0_u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut nonce))
        .context("failed to read Linux kernel randomness")?;
    Ok(nonce)
}

#[cfg(target_os = "linux")]
fn nested_unverified_callback_address(
    nonce: &[u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES],
) -> CargoResult<SocketAddr> {
    use std::os::linux::net::SocketAddrExt as _;

    SocketAddr::from_abstract_name(
        format!("trust-targo-callback-{}", hex::encode(nonce)).as_bytes(),
    )
    .context("failed to construct nested-unverified Targo callback address")
}

#[cfg(target_os = "linux")]
fn nested_unverified_request(
    requester: u32,
    nonce: &[u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES],
) -> Vec<u8> {
    let mut frame = Vec::with_capacity(
        TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA.len()
            + size_of::<u32>()
            + TARGO_NESTED_UNVERIFIED_NONCE_BYTES,
    );
    frame.extend_from_slice(TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA);
    frame.extend_from_slice(&requester.to_be_bytes());
    frame.extend_from_slice(nonce);
    frame
}

#[cfg(target_os = "linux")]
fn parse_nested_unverified_request(
    frame: &[u8],
) -> CargoResult<(u32, [u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES])> {
    let expected_len = TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA.len()
        + size_of::<u32>()
        + TARGO_NESTED_UNVERIFIED_NONCE_BYTES;
    if frame.len() != expected_len || !frame.starts_with(TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA) {
        anyhow::bail!("nested-unverified Targo request has an invalid schema or width");
    }
    let pid_offset = TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA.len();
    let requester = u32::from_be_bytes(
        frame[pid_offset..pid_offset + size_of::<u32>()]
            .try_into()
            .expect("validated request PID width"),
    );
    let nonce = frame[pid_offset + size_of::<u32>()..]
        .try_into()
        .expect("validated request nonce width");
    Ok((requester, nonce))
}

#[cfg(target_os = "linux")]
fn nested_unverified_response(
    root: u32,
    requester: u32,
    nonce: &[u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES],
) -> Vec<u8> {
    let mut frame = Vec::with_capacity(
        TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA.len()
            + 2 * size_of::<u32>()
            + TARGO_NESTED_UNVERIFIED_NONCE_BYTES,
    );
    frame.extend_from_slice(TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA);
    frame.extend_from_slice(&root.to_be_bytes());
    frame.extend_from_slice(&requester.to_be_bytes());
    frame.extend_from_slice(nonce);
    frame
}

#[cfg(target_os = "linux")]
fn parse_nested_unverified_response(
    frame: &[u8],
) -> CargoResult<(u32, u32, [u8; TARGO_NESTED_UNVERIFIED_NONCE_BYTES])> {
    let expected_len = TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA.len()
        + 2 * size_of::<u32>()
        + TARGO_NESTED_UNVERIFIED_NONCE_BYTES;
    if frame.len() != expected_len || !frame.starts_with(TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA) {
        anyhow::bail!("nested-unverified Targo response has an invalid schema or width");
    }
    let root_offset = TARGO_NESTED_UNVERIFIED_RESPONSE_SCHEMA.len();
    let requester_offset = root_offset + size_of::<u32>();
    let nonce_offset = requester_offset + size_of::<u32>();
    let root = u32::from_be_bytes(
        frame[root_offset..requester_offset]
            .try_into()
            .expect("validated response root PID width"),
    );
    let requester = u32::from_be_bytes(
        frame[requester_offset..nonce_offset]
            .try_into()
            .expect("validated response requester PID width"),
    );
    let nonce = frame[nonce_offset..]
        .try_into()
        .expect("validated response nonce width");
    Ok((root, requester, nonce))
}

#[cfg(target_os = "linux")]
fn receive_nested_unverified_frame(
    stream: &mut UnixStream,
    expected_len: usize,
    direction: &str,
) -> CargoResult<Vec<u8>> {
    let mut frame = Vec::with_capacity(expected_len + 1);
    stream
        .take((expected_len + 1) as u64)
        .read_to_end(&mut frame)
        .with_context(|| format!("failed to read nested-unverified Targo broker {direction}"))?;
    if frame.len() != expected_len {
        anyhow::bail!(
            "nested-unverified Targo broker {direction} has invalid framing: expected exactly {expected_len} bytes, got {}",
            frame.len()
        );
    }
    Ok(frame)
}

#[cfg(target_os = "linux")]
fn wait_for_nested_unverified_callback(listener: &UnixListener) -> CargoResult<()> {
    let mut descriptor = libc::pollfd {
        fd: listener.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    // SAFETY: descriptor points to one initialized pollfd for the duration of
    // the bounded poll.
    let result = unsafe {
        libc::poll(
            &mut descriptor,
            1,
            TARGO_NESTED_UNVERIFIED_HANDSHAKE_TIMEOUT.as_millis() as libc::c_int,
        )
    };
    if result < 0 {
        return Err(std::io::Error::last_os_error())
            .context("failed to wait for nested-unverified Targo callback");
    }
    if result == 0 {
        anyhow::bail!("timed out waiting for nested-unverified Targo callback");
    }
    if descriptor.revents & libc::POLLIN == 0 {
        anyhow::bail!(
            "nested-unverified Targo callback listener failed with poll events {:#x}",
            descriptor.revents
        );
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn nested_unverified_socket_peer_pid(descriptor: libc::c_int) -> CargoResult<u32> {
    let mut credentials = std::mem::MaybeUninit::<libc::ucred>::uninit();
    let mut length = size_of::<libc::ucred>() as libc::socklen_t;
    // SAFETY: credentials is an adequately sized getsockopt output buffer; it
    // is read only after the kernel reports the exact initialized length.
    let result = unsafe {
        libc::getsockopt(
            descriptor,
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            credentials.as_mut_ptr().cast(),
            &mut length,
        )
    };
    if result != 0 {
        return Err(std::io::Error::last_os_error())
            .context("failed to authenticate nested-unverified Targo socket peer credentials");
    }
    if length as usize != size_of::<libc::ucred>() {
        anyhow::bail!("nested-unverified Targo socket returned malformed peer credentials");
    }
    // SAFETY: the exact-size check above proves the kernel initialized the
    // complete ucred value.
    let credentials = unsafe { credentials.assume_init() };
    if credentials.pid <= 0 {
        anyhow::bail!("nested-unverified Targo socket peer has no positive pid");
    }
    Ok(credentials.pid as u32)
}

#[cfg(target_os = "linux")]
#[derive(Clone, Copy, Debug)]
enum ExecutableCapture {
    Omit,
    Required,
}

#[cfg(target_os = "linux")]
#[derive(Debug)]
struct LinuxProcessGuard {
    pid: u32,
    parent_pid: u32,
    start_time: u64,
    pidfd: OwnedFd,
    executable: Option<crate::util::file_identity::OpenedFileIdentity>,
}

#[cfg(target_os = "linux")]
impl LinuxProcessGuard {
    fn capture(pid: u32, executable: ExecutableCapture) -> CargoResult<Self> {
        let pidfd = open_linux_pidfd(pid)?;
        ensure_linux_pidfd_live(&pidfd, pid)?;
        let before = read_linux_process_stat(pid)?;
        let executable = match executable {
            ExecutableCapture::Omit => None,
            ExecutableCapture::Required => Some(open_linux_process_executable_identity(pid)?),
        };
        let after = read_linux_process_stat(pid)?;
        if before != after {
            anyhow::bail!(
                "process pid {pid} changed parent or start identity during Targo authority authentication"
            );
        }
        ensure_linux_pidfd_live(&pidfd, pid)?;
        Ok(Self {
            pid,
            parent_pid: before.0,
            start_time: before.1,
            pidfd,
            executable,
        })
    }

    fn ensure_live(&self) -> CargoResult<()> {
        ensure_linux_pidfd_live(&self.pidfd, self.pid)?;
        let current = read_linux_process_stat(self.pid)?;
        if current.1 != self.start_time {
            anyhow::bail!(
                "process pid {} changed start identity during Targo authority authentication",
                self.pid
            );
        }
        if let Some(executable) = &self.executable
            && open_linux_process_executable_identity(self.pid)? != *executable
        {
            anyhow::bail!(
                "process pid {} changed executable during Targo authority authentication",
                self.pid
            );
        }
        Ok(())
    }

    fn ensure_parent_unchanged(&self) -> CargoResult<()> {
        self.ensure_live()?;
        if read_linux_process_stat(self.pid)?.0 != self.parent_pid {
            anyhow::bail!(
                "process pid {} changed parent during Targo authority authentication",
                self.pid
            );
        }
        Ok(())
    }
}

#[cfg(all(target_os = "linux", test))]
fn validate_nested_unverified_targo_process(
    process_pid: u32,
    expected_targo: &LinuxProcessGuard,
) -> CargoResult<LinuxProcessGuard> {
    let process = LinuxProcessGuard::capture(process_pid, ExecutableCapture::Required)?;
    validate_captured_nested_unverified_targo_process(process, expected_targo)
}

#[cfg(target_os = "linux")]
fn validate_captured_nested_unverified_targo_process(
    process: LinuxProcessGuard,
    expected_targo: &LinuxProcessGuard,
) -> CargoResult<LinuxProcessGuard> {
    if process.executable != expected_targo.executable {
        anyhow::bail!(
            "nested-unverified Targo process pid {} does not run the expected opened Targo executable identity",
            process.pid
        );
    }
    process.ensure_live()?;
    expected_targo.ensure_live()?;
    Ok(process)
}

#[cfg(target_os = "linux")]
fn ensure_nested_unverified_ancestor(
    root: &LinuxProcessGuard,
    current_pid: u32,
) -> CargoResult<()> {
    if root.pid == current_pid {
        anyhow::bail!("nested-unverified Targo broker is the requester, not an ancestor");
    }

    let mut process = current_pid;
    let mut visited = std::collections::BTreeSet::new();
    let mut guards: Vec<LinuxProcessGuard> = Vec::new();
    for _ in 0..4096 {
        if process == root.pid {
            root.ensure_live()?;
            for guard in &guards {
                guard.ensure_parent_unchanged()?;
            }
            return Ok(());
        }
        if process == 0 || !visited.insert(process) {
            break;
        }
        let guard = LinuxProcessGuard::capture(process, ExecutableCapture::Omit)?;
        process = guard.parent_pid;
        guards.push(guard);
    }
    anyhow::bail!(
        "nested-unverified Targo broker pid {} is not a live ancestor of pid {current_pid}",
        root.pid
    )
}

#[cfg(target_os = "linux")]
fn read_linux_process_stat(pid: u32) -> CargoResult<(u32, u64)> {
    let stat = std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .with_context(|| format!("failed to inspect process identity for pid {pid}"))?;
    let close = stat.rfind(')').ok_or_else(|| {
        anyhow::anyhow!("process identity record for pid {pid} has no command terminator")
    })?;
    let fields: Vec<_> = stat[close + 1..].split_whitespace().collect();
    let parent_pid = fields
        .get(1)
        .ok_or_else(|| anyhow::anyhow!("process identity record for pid {pid} has no parent pid"))?
        .parse::<u32>()
        .with_context(|| format!("process identity record for pid {pid} has invalid parent pid"))?;
    let start_time = fields
        .get(19)
        .ok_or_else(|| anyhow::anyhow!("process identity record for pid {pid} has no start time"))?
        .parse::<u64>()
        .with_context(|| format!("process identity record for pid {pid} has invalid start time"))?;
    Ok((parent_pid, start_time))
}

#[cfg(target_os = "linux")]
fn open_linux_pidfd(pid: u32) -> CargoResult<OwnedFd> {
    let pid = libc::pid_t::try_from(pid)
        .map_err(|_| anyhow::anyhow!("process pid does not fit Linux pid_t"))?;
    // SAFETY: pidfd_open takes only the copied PID and zero flags. The returned
    // descriptor is checked before ownership is constructed.
    let descriptor = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0_u32) };
    if descriptor < 0 {
        return Err(std::io::Error::last_os_error())
            .context("failed to bind nested-unverified authority to a live Linux pidfd");
    }
    let descriptor = libc::c_int::try_from(descriptor)
        .map_err(|_| anyhow::anyhow!("pidfd descriptor does not fit c_int"))?;
    // SAFETY: a successful pidfd_open returns one new owned descriptor, and
    // this is its first owner.
    Ok(unsafe { OwnedFd::from_raw_fd(descriptor) })
}

#[cfg(target_os = "linux")]
fn ensure_linux_pidfd_live(pidfd: &OwnedFd, pid: u32) -> CargoResult<()> {
    let mut descriptor = libc::pollfd {
        fd: pidfd.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    // SAFETY: descriptor points to one initialized pollfd for the duration of
    // the nonblocking poll.
    let result = unsafe { libc::poll(&mut descriptor, 1, 0) };
    if result < 0 {
        return Err(std::io::Error::last_os_error())
            .with_context(|| format!("failed to poll Linux pidfd for pid {pid}"));
    }
    if result != 0 || descriptor.revents != 0 {
        anyhow::bail!("process pid {pid} exited during Targo authority authentication");
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn open_linux_process_executable_identity(
    pid: u32,
) -> CargoResult<crate::util::file_identity::OpenedFileIdentity> {
    let executable = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_PATH | libc::O_CLOEXEC)
        .open(format!("/proc/{pid}/exe"))
        .with_context(|| {
            format!("failed to open executable handle for Targo authority process pid {pid}")
        })?;
    crate::util::file_identity::opened_file_identity(&executable)
        .with_context(|| format!("failed to identify opened executable for process pid {pid}"))
}

#[derive(Debug)]
struct VerifiedRuntimeLibraryClosure {
    bin_dir: PathBuf,
    sysroot: PathBuf,
    build_root: Option<PathBuf>,
    paths: Vec<PathBuf>,
}

/// Process-local runtime directory closure accepted at verified Targo startup.
/// Reusing this snapshot prevents build scripts from creating new matching
/// stage directories and silently expanding later compiler/merge authority.
static VERIFIED_RUNTIME_LIBRARY_CLOSURE: OnceLock<VerifiedRuntimeLibraryClosure> = OnceLock::new();

/// Freeze the pathname-authority mode on first inspection. Even though Rust
/// environment mutation is unsafe, process plugins or foreign code must not be
/// able to change launcher policy between validation edges.
static PATHNAME_AUTHORITY_MODE: OnceLock<PathnameAuthorityMode> = OnceLock::new();

/// Trust: which principals may own a pathname-backed execution object.
///
/// The property being defended is **substitution**: between the moment Targo
/// authorizes a launcher and the moment the kernel resolves that pathname for
/// `exec`, no principal *other than the identity that asked for verification*
/// may be able to swap the object. A group- or world-writable component hands
/// exactly that power to an arbitrary local principal — that is the attack.
/// Ownership by the invoking identity does not, because that identity already
/// chose which toolchain to run and can redirect the build a hundred other ways.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PathnameAuthorityMode {
    /// Default. Every path component must be a plain directory/file owned by
    /// root **or** by the invoking identity and must not be group- or
    /// world-writable; every component the caller does *not* own must
    /// additionally be proven outside this identity's (possibly ACL-granted)
    /// write authority. The leaf is bound to one opened object (`O_NOFOLLOW`
    /// plus dev/ino agreement) and its bytes are pinned at first authorization
    /// and re-checked on every later execution edge.
    ///
    /// This is the mode a real installation runs in: rustup installs to
    /// `~/.rustup`, `rustup toolchain link trust` names a build under `$HOME`,
    /// and an in-tree stage2 lives under the developer's checkout. Demanding
    /// root ownership refuses every one of those and makes the branded verified
    /// lane unusable by construction.
    CallerOwned,
    /// `TRUST_REQUIRE_SEALED_LAUNCHER=1`. Additionally demands a privileged
    /// installation (every component root-owned and outside this identity's
    /// write authority) and the exact runtime-closure enumeration, and then
    /// still demands a sealed handle-bound launcher — which no platform
    /// implements yet, so this mode continues to fail closed at
    /// [`reject_unbound_platform_loader_authority`]. It is kept reachable and
    /// tested so the release predicate cannot rot.
    SealedRelease,
}

impl PathnameAuthorityMode {
    /// Trust: root-only ownership is the *sealed-release provenance* rule, not
    /// the substitution rule. See [`PathnameAuthorityMode`].
    fn requires_privileged_owner(self) -> bool {
        matches!(self, Self::SealedRelease)
    }
}

#[expect(
    clippy::disallowed_methods,
    reason = "this process-wide startup policy is frozen before a GlobalContext is available"
)]
fn authority_env_flag_enabled(name: &str) -> bool {
    std::env::var_os(name).is_some_and(|value| {
        matches!(
            value.to_str().map(str::trim),
            Some("1") | Some("true") | Some("yes") | Some("on")
        )
    })
}

/// Trust: the pathname-authority mode for this process, frozen on first use.
///
/// `TRUST_ALLOW_UNSEALED_DEV_LAUNCHER` used to be the only way *any* toolchain
/// could execute: without it every path component had to be root-owned, and with
/// it the sealed-launcher blocker was skipped wholesale. Since the sealed
/// blocker fires unconditionally, the variable was not a dev convenience — it
/// was the only reachable lane, and `targo-trust` sets it for Targo itself
/// (`trust_added::trustc_native::public_cli_command`). The mode is now named
/// after the property it defends instead of after a developer workaround; the
/// old variable is still recognized and is a no-op, because what it selected is
/// the default. `TRUST_REQUIRE_SEALED_LAUNCHER=1` opts back in to the
/// (still-unimplementable) release predicate.
fn pathname_authority_mode() -> PathnameAuthorityMode {
    *PATHNAME_AUTHORITY_MODE.get_or_init(|| {
        if authority_env_flag_enabled("TRUST_REQUIRE_SEALED_LAUNCHER") {
            PathnameAuthorityMode::SealedRelease
        } else {
            PathnameAuthorityMode::CallerOwned
        }
    })
}

/// A pathname-backed execution closure is authoritative only when **no principal
/// other than the invoking identity** can replace the launcher, mutate an
/// existing library, or add a new loader candidate between authorization and
/// execution.
///
/// Trust: that quantifier is the whole check. A group- or world-writable
/// component is a substitution primitive for an arbitrary local principal and is
/// rejected in every mode; a component owned by a *foreign* uid is rejected in
/// every mode; a component owned by root that this identity can nonetheless
/// write (an ACL) is rejected in every mode. Ownership by the invoking identity
/// is admitted, because that identity is not the modelled adversary.
///
/// The portable process API does not expose handle-bound `exec`, so one residual
/// remains under [`PathnameAuthorityMode::CallerOwned`]: same-identity code
/// running later in the build — a build script, a proc macro — can rewrite a
/// toolchain the invoking user owns. That residual is narrowed rather than
/// ignored: the launcher's bytes are pinned at first authorization and
/// re-checked at every later execution edge (see
/// [`bind_opened_launcher_identity`]), so a persisted substitution is detected
/// instead of silently trusted. It cannot be closed by pathname rules at all —
/// requiring root ownership does not close it either, it only refuses every
/// toolchain a developer can actually install.
#[cfg(unix)]
fn validate_unprivileged_authority_path(
    path: &Path,
    leaf_is_directory: bool,
    authority: &str,
    mode: PathnameAuthorityMode,
) -> CargoResult<()> {
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::MetadataExt as _;
    use std::path::Component;

    let effective_uid = unsafe { libc::geteuid() };
    let real_uid = unsafe { libc::getuid() };
    let effective_gid = unsafe { libc::getegid() };
    let real_gid = unsafe { libc::getgid() };
    if effective_uid == 0 {
        anyhow::bail!(
            "{authority} cannot be authenticated while Targo runs as root: root and root-launched build scripts retain write authority over pathname-backed execution objects"
        );
    }
    if effective_uid != real_uid || effective_gid != real_gid {
        anyhow::bail!(
            "{authority} cannot be authenticated under transformed process credentials (ruid={real_uid}, euid={effective_uid}, rgid={real_gid}, egid={effective_gid})"
        );
    }
    if !path.is_absolute() {
        anyhow::bail!(
            "{authority} path `{}` is not absolute and cannot own verified execution authority",
            path.display()
        );
    }

    let canonical = path.canonicalize().with_context(|| {
        format!(
            "failed to canonicalize {authority} path `{}`",
            path.display()
        )
    })?;
    if canonical != path {
        anyhow::bail!(
            "{authority} path `{}` is not already canonical (`{}`); verified pathname authority forbids aliases and redirection",
            path.display(),
            canonical.display()
        );
    }

    let components = path.components().collect::<Vec<_>>();
    let mut current = PathBuf::new();
    for (index, component) in components.iter().enumerate() {
        match component {
            Component::RootDir => current.push(Path::new("/")),
            Component::Normal(name) => current.push(name),
            Component::CurDir | Component::ParentDir | Component::Prefix(_) => {
                anyhow::bail!(
                    "{authority} path `{}` contains a non-canonical component",
                    path.display()
                );
            }
        }

        let metadata = std::fs::symlink_metadata(&current).with_context(|| {
            format!(
                "failed to inspect {authority} path component `{}`",
                current.display()
            )
        })?;
        let is_leaf = index + 1 == components.len();
        let expected_type = if is_leaf && !leaf_is_directory {
            metadata_is_plain_file_for_authority(&metadata)
        } else {
            metadata_is_plain_directory(&metadata)
        };
        if !expected_type {
            anyhow::bail!(
                "{authority} path component `{}` is not a plain {} (symlink and reparse-style redirection are forbidden)",
                current.display(),
                if is_leaf && !leaf_is_directory {
                    "regular file"
                } else {
                    "directory"
                }
            );
        }
        validate_authority_ownership(&metadata, &current, authority, mode, effective_uid)?;

        // Trust: an ACL can grant write authority that the mode bits do not
        // show, so mode bits alone do not prove a foreign-owned component is
        // closed to us. Prove it for every component this identity does not
        // already own. On a component the caller *does* own the probe is
        // vacuous — `W_OK` succeeds by construction — so running it there would
        // not test anything; it would only convert the normal case into a
        // refusal, which is exactly the defect this module had.
        if metadata.uid() != effective_uid {
            let encoded = std::ffi::CString::new(current.as_os_str().as_bytes()).map_err(|_| {
                anyhow::anyhow!(
                    "{authority} path component `{}` contains an interior NUL",
                    current.display()
                )
            })?;
            if unsafe { libc::access(encoded.as_ptr(), libc::W_OK) } == 0 {
                anyhow::bail!(
                    "{authority} path component `{}` remains writable by Targo's effective identity (uid={effective_uid}); ACL-backed write authority is incompatible with verified pathname execution",
                    current.display()
                );
            }
            let access_error = std::io::Error::last_os_error();
            // Trust: EACCES, EROFS and EPERM are all *denials* — each one is a
            // proof that this identity cannot write the component. EPERM is not
            // an exotic case: on macOS every SIP-protected system path
            // (`/usr`, `/usr/lib`, `/System`) answers `access(W_OK)` with EPERM
            // rather than EACCES, and `/usr/lib` is a directory Targo itself
            // appends to the verified loader closure. Treating EPERM as an
            // inconclusive error made the strictest platform the one that could
            // not be authenticated.
            if access_error.kind() != std::io::ErrorKind::PermissionDenied
                && access_error.raw_os_error() != Some(libc::EROFS)
                && access_error.raw_os_error() != Some(libc::EPERM)
            {
                return Err(access_error).with_context(|| {
                    format!(
                        "failed to prove that {authority} path component `{}` is outside Targo's write authority",
                        current.display()
                    )
                });
            }
        }
    }
    Ok(())
}

/// Trust: the substitution predicate, applied to one already-`lstat`ed object.
///
/// Two independent refusals, reported separately because they mean different
/// things: a foreign owner (no principal but root or the caller may own an
/// execution object) and group/world writability (the actual substitution
/// primitive, refused no matter who owns the object).
#[cfg(unix)]
fn validate_authority_ownership(
    metadata: &std::fs::Metadata,
    current: &Path,
    authority: &str,
    mode: PathnameAuthorityMode,
    effective_uid: u32,
) -> CargoResult<()> {
    use std::os::unix::fs::MetadataExt as _;

    let owner_ok = if mode.requires_privileged_owner() {
        metadata.uid() == 0
    } else {
        metadata.uid() == 0 || metadata.uid() == effective_uid
    };
    if !owner_ok {
        if mode.requires_privileged_owner() {
            anyhow::bail!(
                "{authority} path component `{}` is owned by uid={}, but TRUST_REQUIRE_SEALED_LAUNCHER demands a root-owned installation for a sealed-release provenance claim",
                current.display(),
                metadata.uid(),
            );
        }
        anyhow::bail!(
            "{authority} path component `{}` is owned by uid={}, which is neither root nor the invoking identity (uid={effective_uid}); an execution object a foreign principal owns can be replaced between authorization and execution",
            current.display(),
            metadata.uid(),
        );
    }
    if metadata.mode() & 0o022 != 0 {
        anyhow::bail!(
            "{authority} path component `{}` is group- or world-writable (uid={}, mode={:#o}); any local principal could substitute the executed object between authorization and execution",
            current.display(),
            metadata.uid(),
            metadata.mode() & 0o7777,
        );
    }
    Ok(())
}

#[cfg(not(unix))]
fn validate_unprivileged_authority_path(
    path: &Path,
    _leaf_is_directory: bool,
    authority: &str,
    _mode: PathnameAuthorityMode,
) -> CargoResult<()> {
    anyhow::bail!(
        "{authority} path `{}` cannot own verified execution authority on this platform: Targo has no implemented immutable pathname-owner/ACL proof or handle-bound launcher",
        path.display()
    )
}

#[cfg(unix)]
fn metadata_is_plain_file_for_authority(metadata: &std::fs::Metadata) -> bool {
    metadata.file_type().is_file() && !metadata.file_type().is_symlink()
}

#[cfg(not(unix))]
fn metadata_is_plain_file_for_authority(metadata: &std::fs::Metadata) -> bool {
    crate::util::file_identity::metadata_is_plain_file(metadata)
}

#[cfg(unix)]
fn launcher_mode_is_safe(mode: u32) -> bool {
    mode & 0o111 != 0 && mode & (libc::S_ISUID | libc::S_ISGID | libc::S_ISVTX) as u32 == 0
}

/// Trust: content identity pinned at the first authorization of each launcher
/// pathname and re-checked on every later execution edge in this process.
/// Metadata alone (uid/mode/dev/ino) does not notice an in-place rewrite of an
/// executable the invoking identity owns, which is precisely the residual that
/// admitting a caller-owned toolchain carries.
#[cfg(unix)]
static AUTHENTICATED_LAUNCHER_DIGESTS: OnceLock<
    Mutex<std::collections::BTreeMap<PathBuf, [u8; 32]>>,
> = OnceLock::new();

/// Trust: bind the *opened* object to the content authorized earlier in this
/// process, so pathname authority stops being the only mechanism. The first
/// observation pins a digest of the bytes behind the descriptor; every later
/// edge must present the same bytes through the same dev/ino.
///
/// This is read through the already-opened `O_NOFOLLOW` descriptor, not by
/// re-opening the pathname, so the digest describes the object whose ownership
/// and mode were just checked.
#[cfg(unix)]
fn bind_opened_launcher_identity(tool: &Path, file: &std::fs::File) -> CargoResult<()> {
    use std::io::Read as _;

    let mut reader = std::io::BufReader::new(file);
    let mut hasher = blake3::Hasher::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer).with_context(|| {
            format!(
                "failed to read opened verified tool launcher `{}` for content authentication",
                tool.display()
            )
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let digest = *hasher.finalize().as_bytes();

    let pinned =
        AUTHENTICATED_LAUNCHER_DIGESTS.get_or_init(|| Mutex::new(std::collections::BTreeMap::new()));
    let mut pinned = pinned
        .lock()
        .map_err(|_| anyhow::anyhow!("verified tool launcher digest ledger was poisoned"))?;
    match pinned.entry(tool.to_path_buf()) {
        std::collections::btree_map::Entry::Vacant(slot) => {
            slot.insert(digest);
            Ok(())
        }
        std::collections::btree_map::Entry::Occupied(slot) => {
            if *slot.get() == digest {
                Ok(())
            } else {
                anyhow::bail!(
                    "verified tool launcher `{}` changed content after it was authenticated in this process; the executed object is not the one Targo authorized",
                    tool.display()
                )
            }
        }
    }
}

#[cfg(unix)]
fn validate_opened_tool_launcher(tool: &Path, mode: PathnameAuthorityMode) -> CargoResult<()> {
    use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};

    // The complete parent chain has already been proven to be owned only by root
    // or the invoking identity and to be closed to every other principal.
    // O_NOFOLLOW additionally binds the leaf check to one opened regular-file
    // object rather than pathname metadata.
    let file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
        .open(tool)
        .with_context(|| format!("failed to open verified tool launcher `{}`", tool.display()))?;
    let opened = file.metadata().with_context(|| {
        format!(
            "failed to inspect opened verified tool launcher `{}`",
            tool.display()
        )
    })?;
    let euid = unsafe { libc::geteuid() };
    let owner_ok = if mode.requires_privileged_owner() {
        opened.uid() == 0
    } else {
        opened.uid() == 0 || opened.uid() == euid
    };
    if !metadata_is_plain_file_for_authority(&opened) || !owner_ok || opened.mode() & 0o022 != 0 {
        anyhow::bail!(
            "opened verified tool launcher `{}` is not a regular file owned by root or the invoking identity and closed to group/world writes (uid={}, mode={:#o})",
            tool.display(),
            opened.uid(),
            opened.mode() & 0o7777,
        );
    }
    if !launcher_mode_is_safe(opened.mode()) {
        anyhow::bail!(
            "opened verified tool launcher `{}` must be executable without setuid, setgid, or sticky special mode bits (mode={:#o})",
            tool.display(),
            opened.mode() & 0o7777,
        );
    }
    let path = std::fs::symlink_metadata(tool).with_context(|| {
        format!(
            "failed to re-inspect verified tool launcher path `{}`",
            tool.display()
        )
    })?;
    if !metadata_is_plain_file_for_authority(&path)
        || path.dev() != opened.dev()
        || path.ino() != opened.ino()
    {
        anyhow::bail!(
            "verified tool launcher path `{}` does not name the opened executable object",
            tool.display()
        );
    }
    bind_opened_launcher_identity(tool, &file)
}

#[cfg(not(unix))]
fn validate_opened_tool_launcher(_tool: &Path, _mode: PathnameAuthorityMode) -> CargoResult<()> {
    Ok(())
}

fn validate_immutable_runtime_directories(
    paths: &[PathBuf],
    mode: PathnameAuthorityMode,
) -> CargoResult<()> {
    let mut canonical_paths = std::collections::BTreeSet::new();
    for path in paths {
        validate_unprivileged_authority_path(
            path,
            true,
            "verified runtime-library directory",
            mode,
        )?;
        if !canonical_paths.insert(path.clone()) {
            anyhow::bail!(
                "verified runtime-library closure contains duplicate directory `{}`",
                path.display()
            );
        }
    }

    // Trust: every admitted runtime directory was just proven, on THIS edge, to
    // be a plain directory owned only by root or the invoking identity, closed
    // to group/world writes, and (when foreign-owned) outside this identity's
    // ACL write authority. That is what forbids another principal from adding or
    // replacing a loader candidate mid-run, and it is re-proved at every
    // execution edge.
    //
    // The exact-closure enumeration below is a different, release-only property:
    // it forbids ANY subdirectory of an admitted directory that is not itself a
    // container of another admitted directory — including the toolchain's own
    // `lib/rustlib/<target>/lib/self-contained` — which no real toolchain layout
    // satisfies. Under `CallerOwned` it is replaced by a content scan that still
    // refuses symlinks, special files, and foreign-owned or group/world-writable
    // entries. That is strictly more than the old dev exemption, which skipped
    // enumeration entirely and is what every invocation actually ran.
    if !mode.requires_privileged_owner() {
        return validate_runtime_directory_contents(paths, mode);
    }

    for directory in paths {
        let entries = std::fs::read_dir(directory).with_context(|| {
            format!(
                "failed to inspect verified runtime-library directory `{}`",
                directory.display()
            )
        })?;
        for entry in entries {
            let entry = entry.with_context(|| {
                format!(
                    "failed to inspect an entry in verified runtime-library directory `{}`",
                    directory.display()
                )
            })?;
            let candidate = entry.path();
            let metadata = std::fs::symlink_metadata(&candidate).with_context(|| {
                format!(
                    "failed to inspect verified runtime-library candidate `{}`",
                    candidate.display()
                )
            })?;
            if metadata.file_type().is_file() && !metadata.file_type().is_symlink() {
                validate_unprivileged_authority_path(
                    &candidate,
                    false,
                    "verified runtime-library candidate",
                    mode,
                )?;
                continue;
            }
            if metadata_is_plain_directory(&metadata)
                && paths
                    .iter()
                    .any(|admitted| admitted != &candidate && admitted.starts_with(&candidate))
            {
                // A container such as `lib/rustlib` is not itself a loader
                // search directory. It is safe only because its own path is
                // immutable and the actually admitted descendant is checked
                // independently.
                validate_unprivileged_authority_path(
                    &candidate,
                    true,
                    "verified runtime-library container",
                    mode,
                )?;
                continue;
            }
            anyhow::bail!(
                "verified runtime-library directory `{}` contains unbound candidate `{}`; symlinks, special files, and loader-visible subdirectories outside the exact admitted closure are forbidden",
                directory.display(),
                candidate.display()
            );
        }
    }
    Ok(())
}

/// Trust: the platform default loader directory Targo itself appends to the
/// verified search path (`configure_verified_tool_loader_environment` pushes
/// `/usr/lib` on macOS). Its own ownership, mode and non-writability are still
/// proven like any other component; what is skipped is enumerating its
/// *contents*, which on macOS are root-owned symlinks into the dyld shared
/// cache. Those are exactly the "OS default loader cache/shared libraries" that
/// [`unbound_platform_loader_authority_message`] discloses as outside any
/// pathname closure Targo can authenticate — refusing them here would refuse a
/// directory only root can write, which tests nothing about the modelled
/// adversary while making the platform's own libc unreachable.
#[cfg(unix)]
fn is_platform_default_loader_directory(path: &Path) -> bool {
    cfg!(target_os = "macos") && path == Path::new("/usr/lib")
}

/// Trust: directory content scans already performed in this process, keyed by
/// the directory's observed identity. A directory whose device, inode, size and
/// modification time are all unchanged has had no entry added, removed or
/// renamed, so re-walking 33k compiler build-dependency artifacts on every
/// compiler spawn would re-derive the same answer. Any change to the entry set
/// moves the directory's own mtime and forces a fresh scan.
#[cfg(unix)]
static SCANNED_RUNTIME_DIRECTORIES: OnceLock<Mutex<std::collections::BTreeMap<PathBuf, DirScan>>> =
    OnceLock::new();

#[cfg(unix)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct DirScan {
    dev: u64,
    ino: u64,
    size: u64,
    mtime: i64,
    mtime_nsec: i64,
}

#[cfg(unix)]
fn observed_directory_scan(metadata: &std::fs::Metadata) -> DirScan {
    use std::os::unix::fs::MetadataExt as _;

    DirScan {
        dev: metadata.dev(),
        ino: metadata.ino(),
        size: metadata.size(),
        mtime: metadata.mtime(),
        mtime_nsec: metadata.mtime_nsec(),
    }
}

/// Trust: the `CallerOwned` replacement for the release-only exact-closure
/// enumeration. It keeps the part that defends a real property — nothing in a
/// loader search directory may be a symlink, a special file, foreign-owned or
/// group/world-writable — and drops the part no toolchain layout can satisfy,
/// namely that a plain subdirectory of a search directory is forbidden. A
/// subdirectory is not itself searched by the loader for a leaf name; the
/// toolchain's own `self-contained` directory is the case that made the old rule
/// unsatisfiable.
#[cfg(unix)]
fn validate_runtime_directory_contents(
    paths: &[PathBuf],
    mode: PathnameAuthorityMode,
) -> CargoResult<()> {
    let effective_uid = unsafe { libc::geteuid() };
    for directory in paths {
        if is_platform_default_loader_directory(directory) {
            continue;
        }
        let observed = observed_directory_scan(&std::fs::symlink_metadata(directory).with_context(
            || {
                format!(
                    "failed to inspect verified runtime-library directory `{}`",
                    directory.display()
                )
            },
        )?);
        let ledger = SCANNED_RUNTIME_DIRECTORIES
            .get_or_init(|| Mutex::new(std::collections::BTreeMap::new()));
        {
            let scanned = ledger.lock().map_err(|_| {
                anyhow::anyhow!("verified runtime-directory scan ledger was poisoned")
            })?;
            if scanned.get(directory) == Some(&observed) {
                continue;
            }
        }
        for entry in std::fs::read_dir(directory).with_context(|| {
            format!(
                "failed to inspect verified runtime-library directory `{}`",
                directory.display()
            )
        })? {
            let entry = entry.with_context(|| {
                format!(
                    "failed to inspect an entry in verified runtime-library directory `{}`",
                    directory.display()
                )
            })?;
            let candidate = entry.path();
            let metadata = std::fs::symlink_metadata(&candidate).with_context(|| {
                format!(
                    "failed to inspect verified runtime-library candidate `{}`",
                    candidate.display()
                )
            })?;
            let plain_file = metadata.file_type().is_file() && !metadata.file_type().is_symlink();
            if !plain_file && !metadata_is_plain_directory(&metadata) {
                anyhow::bail!(
                    "verified runtime-library directory `{}` contains unbound candidate `{}`; a symlink or special file in a loader search directory can redirect a loaded object and is forbidden",
                    directory.display(),
                    candidate.display()
                );
            }
            validate_authority_ownership(
                &metadata,
                &candidate,
                "verified runtime-library candidate",
                mode,
                effective_uid,
            )?;
        }
        ledger
            .lock()
            .map_err(|_| anyhow::anyhow!("verified runtime-directory scan ledger was poisoned"))?
            .insert(directory.clone(), observed);
    }
    Ok(())
}

#[cfg(not(unix))]
fn validate_runtime_directory_contents(
    paths: &[PathBuf],
    _mode: PathnameAuthorityMode,
) -> CargoResult<()> {
    if let Some(directory) = paths.first() {
        anyhow::bail!(
            "verified runtime-library directory `{}` cannot own verified execution authority on this platform",
            directory.display()
        );
    }
    Ok(())
}

fn unbound_platform_loader_authority_message(tool: &Path) -> String {
    format!(
        "immutable injected search directories do not bind `{}`'s embedded RPATH/RUNPATH/install-name closure or the OS default loader cache/shared libraries; release authority requires a sealed handle-bound launcher and authenticated runtime image",
        tool.display()
    )
}

fn reject_unbound_platform_loader_authority(tool: &Path) -> CargoResult<()> {
    anyhow::bail!(
        "verified pathname execution remains unavailable for `{}`: {}",
        tool.display(),
        unbound_platform_loader_authority_message(tool),
    )
}

/// Trust: launchers whose unsealed-authority disclosure has already been printed
/// in this process.
static DISCLOSED_UNSEALED_LAUNCHERS: OnceLock<Mutex<std::collections::BTreeSet<PathBuf>>> =
    OnceLock::new();

/// Trust: say exactly once per launcher what pathname authority does and does
/// not establish. The predecessor refused to run at all rather than say this,
/// which is why no developer could reach the verified lane and why the visible
/// failure was a downstream "missing coverage_summary transport" from a compiler
/// that never launched.
#[expect(
    clippy::print_stderr,
    reason = "the pathname-authority disclosure must be visible before a Cargo Shell is available"
)]
fn disclose_unsealed_launcher_authority(tool: &Path) -> CargoResult<()> {
    let disclosed =
        DISCLOSED_UNSEALED_LAUNCHERS.get_or_init(|| Mutex::new(std::collections::BTreeSet::new()));
    let first = {
        let mut disclosed = disclosed
            .lock()
            .map_err(|_| anyhow::anyhow!("verified launcher disclosure ledger was poisoned"))?;
        disclosed.insert(tool.to_path_buf())
    };
    if first {
        eprintln!(
            "warning: verified tool launcher `{}` carries CALLER-OWNED (unsealed) pathname authority: no other principal can substitute it and its content is pinned for this run, but {}. Proof verdicts are unaffected; the toolchain binary's sealed release provenance is not proven. Set TRUST_REQUIRE_SEALED_LAUNCHER=1 to demand the release-grade closure instead.",
            tool.display(),
            unbound_platform_loader_authority_message(tool),
        );
    }
    Ok(())
}

fn validate_verified_tool_execution_closure(tool: &Path, paths: &[PathBuf]) -> CargoResult<()> {
    let mode = pathname_authority_mode();
    validate_unprivileged_authority_path(tool, false, "verified tool launcher", mode)?;
    validate_opened_tool_launcher(tool, mode)?;
    validate_immutable_runtime_directories(paths, mode)?;
    if mode.requires_privileged_owner() {
        // The sealed-release predicate is unchanged and still fails closed: no
        // platform binds the embedded run-path closure yet.
        return reject_unbound_platform_loader_authority(tool);
    }
    disclose_unsealed_launcher_authority(tool)
}

pub(crate) const FIX_ENV_INTERNAL: &str = "__CARGO_FIX_PLZ";
pub(crate) const BROKEN_CODE_ENV_INTERNAL: &str = "__CARGO_FIX_BROKEN_CODE";
pub(crate) const EDITION_ENV_INTERNAL: &str = "__CARGO_FIX_EDITION";
pub(crate) const IDIOMS_ENV_INTERNAL: &str = "__CARGO_FIX_IDIOMS";
pub(crate) const SYSROOT_INTERNAL: &str = "__CARGO_FIX_RUST_SRC";
pub(crate) const DIAGNOSTICS_SERVER_VAR: &str = "__CARGO_FIX_DIAGNOSTICS_SERVER";
pub(crate) const FIX_YOLO_ENV_INTERNAL: &str = "__CARGO_FIX_YOLO";
pub(crate) const FIX_MAX_RETRIES_ENV: &str = "CARGO_FIX_MAX_RETRIES";
pub(crate) const TARGO_FIX_PARENT_PID_ENV: &str = "__CARGO_FIX_TARGO_PARENT_PID";
pub(crate) const TARGO_FIX_EXPECTED_RUSTC_ENV: &str = "__CARGO_FIX_TARGO_EXPECTED_RUSTC";
pub(crate) const TARGO_FIX_EXPECTED_RUSTC_ID_ENV: &str = "__CARGO_FIX_TARGO_EXPECTED_RUSTC_ID";
pub(crate) const TARGO_FIX_LANE_ENV: &str = "__CARGO_FIX_TARGO_LANE_V1";
pub(crate) const TARGO_FIX_CAPABILITY_FD_ENV: &str = "__CARGO_FIX_TARGO_CAPABILITY_FD";

/// Exact fix-proxy controls whose values must survive unchanged between Cargo
/// constructing its primary-unit proxy and that proxy launching the compiler.
pub(crate) const FIX_PROXY_CONTROL_ENVS: &[&str] = &[
    FIX_ENV_INTERNAL,
    BROKEN_CODE_ENV_INTERNAL,
    EDITION_ENV_INTERNAL,
    IDIOMS_ENV_INTERNAL,
    SYSROOT_INTERNAL,
    DIAGNOSTICS_SERVER_VAR,
    FIX_YOLO_ENV_INTERNAL,
    FIX_MAX_RETRIES_ENV,
    TARGO_FIX_PARENT_PID_ENV,
    TARGO_FIX_EXPECTED_RUSTC_ENV,
    TARGO_FIX_EXPECTED_RUSTC_ID_ENV,
    TARGO_FIX_LANE_ENV,
    TARGO_FIX_CAPABILITY_FD_ENV,
];

/// Whether an environment name has one portable representation across the
/// platforms supported by Cargo.
pub(crate) fn is_ascii_environment_name(name: &str) -> bool {
    name.is_ascii()
}

/// Whether an environment name is one of Cargo, rustc, rustdoc, or Bootstrap's
/// compiler-flag channels. Match ASCII case and private/target suffixes.
pub(crate) fn is_compiler_flag_environment(name: &str) -> bool {
    fn contains_ignore_ascii_case(value: &str, needle: &[u8]) -> bool {
        value
            .as_bytes()
            .windows(needle.len())
            .any(|window| window.eq_ignore_ascii_case(needle))
    }

    name.eq_ignore_ascii_case("MAGIC_EXTRA_RUSTFLAGS")
        || contains_ignore_ascii_case(name, b"RUSTFLAGS")
        || contains_ignore_ascii_case(name, b"RUSTDOCFLAGS")
}

/// Environment channels that can change authenticated Targo's compiler,
/// arguments, proof policy, process wrappers, dynamic loader, or fix proxy.
///
/// Environment names are case-insensitive on Windows. Reject every ASCII-case
/// spelling on every host so a configuration has one portable security
/// meaning. Non-ASCII names fail closed because their comparison rules are not
/// portable across supported platforms.
pub(crate) fn is_authenticated_targo_process_authority_env(name: &str) -> bool {
    if !is_ascii_environment_name(name)
        || is_compiler_flag_environment(name)
        || is_protected_tippy_arg_env(name)
    {
        return true;
    }

    let name = name.to_ascii_uppercase();
    name.starts_with("TRUST_")
        || name.starts_with("RUSTC_")
        || name.starts_with("RUSTDOC_")
        || name.starts_with("CARGO_TARGET_")
        || is_dynamic_loader_authority_env(&name)
        || name.starts_with("__CARGO_FIX_")
        || name.starts_with("CARGO_FIX_")
        || matches!(
            name.as_str(),
            "CARGO"
                | "TRUSTC"
                | "TRUSTDOC"
                | "CARGO_TRUST_BIN"
                | "CARGO_HOME"
                | "RUSTUP_HOME"
                | "RUSTUP_TOOLCHAIN"
                | "RUST_TARGET_PATH"
                | "PATH"
                | "PATHEXT"
                | "SYSROOT"
                | "RUSTC"
                | "RUSTDOC"
                | "CARGO_PRIMARY_PACKAGE"
                | "CARGO_BUILD_TARGET"
                | "CARGO_BUILD_TARGET_DIR"
                | "RUSTC_WRAPPER"
                | "RUSTC_WORKSPACE_WRAPPER"
                | "CARGO_BUILD_RUSTC"
                | "CARGO_BUILD_RUSTDOC"
                | "CARGO_BUILD_RUSTC_WRAPPER"
                | "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
        )
}

/// Benign build-script provenance stamps: names that a crate's OWN `build.rs`
/// emits via `cargo::rustc-env` purely so the crate can bake them into its
/// binary through `env!()`/`option_env!()` (version/`--version` strings,
/// staleness-check shims). `cargo::rustc-env` scopes the value to the
/// compilation of the emitting package only; these particular names are never
/// read by trustc/Targo from the process environment as authority signals
/// (unlike `TRUST_NO_VERIFY`, `TRUSTC`, `TRUST_TARGO_BIN`, …), so admitting
/// them cannot subvert the authenticated toolchain, disable verification, or
/// redirect the compiler. This is intentionally an exact-name allowlist, not a
/// prefix, so a new authority channel can never be smuggled in behind it.
///
/// Concretely these are emitted by `trust-mc-driver/build.rs` (git SHA + dirty
/// flag for its `--version` output and the `cargo-trust-mc` staleness shim).
pub(crate) fn is_benign_build_script_provenance_env(name: &str) -> bool {
    matches!(
        name.to_ascii_uppercase().as_str(),
        "TRUST_MC_GIT_SHA" | "TRUST_MC_GIT_DIRTY"
    )
}

/// Whether an environment name gives a platform dynamic loader search,
/// preload, audit, interposition, or diagnostic authority.
pub(crate) fn is_dynamic_loader_authority_env(name: &str) -> bool {
    let name = name.to_ascii_uppercase();
    name.starts_with("LD_")
        || name.starts_with("DYLD_")
        || name.starts_with("LDR_")
        || name.starts_with("_RLD")
        || matches!(name.as_str(), "LIBPATH" | "SHLIB_PATH")
}

fn verified_targo_startup_search_variable() -> Option<&'static str> {
    if cfg!(windows) {
        // PATH is simultaneously the Windows DLL and executable search path.
        // The verified launcher cannot reconstruct it without also breaking
        // rustdoc's downstream tool discovery, so it remains an explicitly
        // reported execution-closure limitation instead of being mistaken for
        // an authenticated value here.
        None
    } else if cfg!(target_os = "macos") {
        // Keep this in lockstep with targo-trust's `apply_native_runtime_env`.
        Some("DYLD_LIBRARY_PATH")
    } else if cfg!(target_os = "aix") {
        Some("LIBPATH")
    } else {
        Some("LD_LIBRARY_PATH")
    }
}

fn validate_plain_toolchain_directory_path(root: &Path, candidate: &Path) -> CargoResult<bool> {
    let root_metadata = match std::fs::symlink_metadata(root) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
        Err(error) => {
            return Err(error).with_context(|| {
                format!(
                    "failed to inspect verified toolchain root `{}`",
                    root.display()
                )
            });
        }
    };
    if !metadata_is_plain_directory(&root_metadata) {
        anyhow::bail!(
            "verified toolchain root `{}` is not a plain directory (symlink and reparse redirection are forbidden)",
            root.display()
        );
    }
    let relative = candidate.strip_prefix(root).with_context(|| {
        format!(
            "verified runtime directory `{}` escaped toolchain root `{}`",
            candidate.display(),
            root.display()
        )
    })?;
    let mut current = root.to_path_buf();
    for component in relative.components() {
        current.push(component);
        let metadata = match std::fs::symlink_metadata(&current) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
            Err(error) => {
                return Err(error).with_context(|| {
                    format!(
                        "failed to inspect verified runtime path component `{}`",
                        current.display()
                    )
                });
            }
        };
        if !metadata_is_plain_directory(&metadata) {
            anyhow::bail!(
                "verified runtime path component `{}` is not a plain directory (symlink and reparse redirection are forbidden)",
                current.display()
            );
        }
    }
    Ok(true)
}

fn push_verified_runtime_directory(
    paths: &mut Vec<PathBuf>,
    root: &Path,
    candidate: PathBuf,
) -> CargoResult<()> {
    if !validate_plain_toolchain_directory_path(root, &candidate)? {
        return Ok(());
    }
    let canonical = candidate.canonicalize().with_context(|| {
        format!(
            "failed to canonicalize verified Targo runtime directory `{}`",
            candidate.display()
        )
    })?;
    paths.push(canonical);
    Ok(())
}

/// Reconstruct the runtime-library path that `targo-trust` installs before it
/// starts verified Targo. The result is sorted because directory iteration
/// order is not an authority boundary; membership, duplicates, and extra
/// entries are checked exactly below.
fn scan_verified_tool_runtime_library_paths(tool: &Path) -> CargoResult<Vec<PathBuf>> {
    let lexical_bin_dir = tool.parent().ok_or_else(|| {
        anyhow::anyhow!(
            "authenticated tool `{}` has no toolchain directory",
            tool.display()
        )
    })?;
    let lexical_sysroot = lexical_bin_dir.parent().ok_or_else(|| {
        anyhow::anyhow!(
            "authenticated Targo toolchain directory `{}` has no sysroot",
            lexical_bin_dir.display()
        )
    })?;

    let mut paths = Vec::new();
    if !validate_plain_toolchain_directory_path(lexical_sysroot, lexical_bin_dir)? {
        anyhow::bail!(
            "authenticated tool directory `{}` disappeared during runtime-path validation",
            lexical_bin_dir.display()
        );
    }
    let bin_dir = lexical_bin_dir.canonicalize().with_context(|| {
        format!(
            "failed to canonicalize authenticated tool directory `{}`",
            lexical_bin_dir.display()
        )
    })?;
    let sysroot = bin_dir.parent().ok_or_else(|| {
        anyhow::anyhow!(
            "canonical authenticated toolchain directory `{}` has no sysroot",
            bin_dir.display()
        )
    })?;
    push_verified_runtime_directory(&mut paths, sysroot, sysroot.join("lib"))?;

    let mut rustlib_paths = Vec::new();
    let rustlib_root = sysroot.join("lib").join("rustlib");
    if validate_plain_toolchain_directory_path(sysroot, &rustlib_root)? {
        for entry in std::fs::read_dir(&rustlib_root).with_context(|| {
            format!(
                "failed to inspect verified Targo rustlib directory `{}`",
                rustlib_root.display()
            )
        })? {
            let entry = entry.with_context(|| {
                format!(
                    "failed to inspect an entry in verified Targo rustlib directory `{}`",
                    rustlib_root.display()
                )
            })?;
            // Trust: rustlib carries installer metadata files (`components`,
            // `rust-installer-version`) beside the per-target directories; a
            // regular file has no `lib` runtime subdir. Skip files for the same
            // reason as the rustc build-deps scan above — the plain-directory
            // check hard-bails on a non-directory component. Symlinks still hit
            // the strict check inside `push_verified_runtime_directory`.
            let entry_type = entry.file_type().with_context(|| {
                format!(
                    "failed to inspect the type of an entry in verified Targo rustlib directory `{}`",
                    rustlib_root.display()
                )
            })?;
            if entry_type.is_file() {
                continue;
            }
            push_verified_runtime_directory(&mut rustlib_paths, sysroot, entry.path().join("lib"))?;
        }
    }
    rustlib_paths.sort();
    rustlib_paths.dedup();
    for path in rustlib_paths {
        if !paths.contains(&path) {
            paths.push(path);
        }
    }

    let mut compiler_dependency_paths = Vec::new();
    if let (Some(build_dir), Some(stage_name)) = (sysroot.parent(), sysroot.file_name()) {
        let rustc_deps_root = build_dir.join(format!("{}-rustc", stage_name.to_string_lossy()));
        if validate_plain_toolchain_directory_path(build_dir, &rustc_deps_root)? {
            for entry in std::fs::read_dir(&rustc_deps_root).with_context(|| {
                format!(
                    "failed to inspect verified Targo compiler runtime directory `{}`",
                    rustc_deps_root.display()
                )
            })? {
                let entry = entry.with_context(|| {
                    format!(
                        "failed to inspect an entry in verified Targo compiler runtime directory `{}`",
                        rustc_deps_root.display()
                    )
                })?;
                // Trust: the rustc build-deps root holds cargo's own cache
                // siblings (`.rustc_info.json`, `CACHEDIR.TAG`) alongside the
                // per-target build directories. A regular file is never a
                // descendable `release/deps` runtime directory, so skip it
                // rather than tripping the plain-directory authority check —
                // which hard-bails on a non-directory path component and would
                // otherwise abort verified `targo` startup whenever cargo has
                // written its rustc-info cache. Symlink entries still fall
                // through to the strict check below, so a reparse point cannot
                // smuggle itself into the verified runtime library path.
                let entry_type = entry.file_type().with_context(|| {
                    format!(
                        "failed to inspect the type of an entry in verified Targo compiler runtime directory `{}`",
                        rustc_deps_root.display()
                    )
                })?;
                if entry_type.is_file() {
                    continue;
                }
                let candidate = entry.path().join("release").join("deps");
                if !validate_plain_toolchain_directory_path(build_dir, &candidate)? {
                    continue;
                }
                let canonical = candidate.canonicalize().with_context(|| {
                    format!(
                        "failed to canonicalize verified Targo runtime directory `{}`",
                        candidate.display()
                    )
                })?;
                compiler_dependency_paths.push(canonical);
            }
        }
    }
    compiler_dependency_paths.sort();
    compiler_dependency_paths.dedup();
    for path in compiler_dependency_paths {
        if !paths.contains(&path) {
            paths.push(path);
        }
    }

    // Loader precedence is semantic: direct sysroot libraries must win over
    // target rustlibs, which in turn must win over compiler-build dependency
    // outputs. Only nondeterministic enumeration *within* a tier is sorted.
    Ok(paths)
}

pub(crate) fn verified_tool_runtime_library_paths(tool: &Path) -> CargoResult<Vec<PathBuf>> {
    if crate::is_targo_invocation() && crate::trust_verified_targo() {
        let closure = VERIFIED_RUNTIME_LIBRARY_CLOSURE.get().ok_or_else(|| {
            anyhow::anyhow!(
                "verified Targo runtime-library closure was not captured at authenticated startup"
            )
        })?;
        let lexical_bin_dir = tool.parent().ok_or_else(|| {
            anyhow::anyhow!(
                "authenticated tool `{}` has no toolchain directory",
                tool.display()
            )
        })?;
        let metadata = std::fs::symlink_metadata(lexical_bin_dir).with_context(|| {
            format!(
                "failed to inspect authenticated tool directory `{}`",
                lexical_bin_dir.display()
            )
        })?;
        if !metadata_is_plain_directory(&metadata) {
            anyhow::bail!(
                "authenticated tool directory `{}` became a symlink or reparse point after startup",
                lexical_bin_dir.display()
            );
        }
        let bin_dir = lexical_bin_dir.canonicalize().with_context(|| {
            format!(
                "failed to canonicalize authenticated tool directory `{}`",
                lexical_bin_dir.display()
            )
        })?;
        if bin_dir != closure.bin_dir {
            anyhow::bail!(
                "authenticated tool `{}` escaped verified Targo's startup toolchain directory `{}`",
                tool.display(),
                closure.bin_dir.display()
            );
        }
        for path in &closure.paths {
            let root = if path.starts_with(&closure.sysroot) {
                &closure.sysroot
            } else if let Some(build_root) = closure
                .build_root
                .as_ref()
                .filter(|build_root| path.starts_with(build_root))
            {
                build_root
            } else {
                anyhow::bail!(
                    "captured verified runtime directory `{}` escaped its authenticated toolchain roots",
                    path.display()
                );
            };
            if !validate_plain_toolchain_directory_path(root, path)? {
                anyhow::bail!(
                    "captured verified runtime directory `{}` disappeared after startup",
                    path.display()
                );
            }
        }
        validate_verified_tool_execution_closure(tool, &closure.paths)?;
        return Ok(closure.paths.clone());
    }
    scan_verified_tool_runtime_library_paths(tool)
}

fn validate_verified_targo_startup_loader_environment_from<I, K, V>(
    frontend: &Path,
    environment: I,
) -> CargoResult<Vec<PathBuf>>
where
    I: IntoIterator<Item = (K, V)>,
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    let expected_search_variable = verified_targo_startup_search_variable();
    let expected_search_paths = scan_verified_tool_runtime_library_paths(frontend)?;
    let mut actual_search_value: Option<OsString> = None;
    let mut forbidden = Vec::new();

    for (name, value) in environment {
        let name = name.as_ref();
        let Some(name_str) = name.to_str() else {
            // Dynamic loaders recognize the portable ASCII spellings. A name
            // containing non-UTF-8 bytes cannot equal one of those spellings.
            continue;
        };
        if !is_dynamic_loader_authority_env(name_str) {
            continue;
        }
        if expected_search_variable == Some(name_str) {
            if actual_search_value
                .replace(value.as_ref().to_owned())
                .is_some()
            {
                anyhow::bail!(
                    "verified Targo startup received duplicate `{name_str}` environment entries"
                );
            }
        } else {
            forbidden.push(name_str.to_owned());
        }
    }

    forbidden.sort();
    forbidden.dedup();
    if !forbidden.is_empty() {
        anyhow::bail!(
            "verified Targo cannot authenticate a process that was started with ambient dynamic-loader authority in {}: {}; the loader may have executed untrusted code before Targo began",
            forbidden.len(),
            forbidden.join(", ")
        );
    }

    match (expected_search_variable, actual_search_value) {
        (None, None) => Ok(expected_search_paths),
        (None, Some(_)) => unreachable!("a search value has no accepted variable"),
        (Some(_), None) if expected_search_paths.is_empty() => Ok(expected_search_paths),
        (Some(variable), None) => anyhow::bail!(
            "verified Targo startup is missing targo-trust's reconstructed `{variable}` runtime path"
        ),
        (Some(variable), Some(_)) if expected_search_paths.is_empty() => anyhow::bail!(
            "verified Targo startup received `{variable}` even though its authenticated sibling toolchain has no runtime-library directories"
        ),
        (Some(variable), Some(value)) => {
            let actual = std::env::split_paths(&value).collect::<Vec<_>>();
            if actual != expected_search_paths {
                anyhow::bail!(
                    "verified Targo startup `{variable}` does not exactly match targo-trust's reconstructed canonical sibling-toolchain runtime path"
                );
            }
            Ok(expected_search_paths)
        }
    }
}

/// Fail closed when verified Targo itself may already have been influenced by
/// ambient loader authority. Child-process scrubbing cannot repair compromise
/// that occurred before `main`, so the one search path required by in-tree
/// toolchains must exactly match the value independently reconstructed from the
/// authenticated sibling toolchain and every other loader channel is rejected.
#[expect(
    clippy::disallowed_methods,
    reason = "startup loader authentication must inspect the environment that influenced the process before GlobalContext construction"
)]
pub(crate) fn validate_verified_targo_startup_loader_environment(
    frontend: &Path,
) -> CargoResult<()> {
    let paths =
        validate_verified_targo_startup_loader_environment_from(frontend, std::env::vars_os())?;
    // This is necessarily checked after the OS loader reached `main`. Requiring
    // every component and candidate to have been outside the invoking user's
    // write authority is what makes that observation meaningful; a mutable
    // user-owned stage directory is rejected rather than retrospectively
    // blessed by an environment/path snapshot.
    validate_verified_tool_execution_closure(frontend, &paths)?;
    let lexical_bin_dir = frontend
        .parent()
        .expect("validated frontend must have a toolchain directory")
        .to_path_buf();
    let bin_dir = lexical_bin_dir.canonicalize().with_context(|| {
        format!(
            "failed to canonicalize verified Targo toolchain directory `{}` after startup validation",
            lexical_bin_dir.display()
        )
    })?;
    let sysroot = bin_dir
        .parent()
        .expect("validated toolchain directory must have a sysroot")
        .to_path_buf();
    let build_root = sysroot.parent().map(Path::to_path_buf);
    VERIFIED_RUNTIME_LIBRARY_CLOSURE
        .set(VerifiedRuntimeLibraryClosure {
            bin_dir,
            sysroot,
            build_root,
            paths,
        })
        .map_err(|_| {
            anyhow::anyhow!("verified Targo runtime-library closure was initialized twice")
        })?;
    Ok(())
}

/// Remove inherited dynamic-loader authority from an authenticated child.
///
/// `retained_search_path` is the one platform search variable whose value the
/// caller has replaced with a Cargo-owned deterministic path list. All other
/// ambient spellings are explicitly removed from the child overlay.
#[expect(
    clippy::disallowed_methods,
    reason = "child scrubbing must enumerate the actual inherited process environment, including platform-specific loader names"
)]
pub(crate) fn scrub_dynamic_loader_authority_env(
    command: &mut ProcessBuilder,
    retained_search_path: Option<&str>,
) {
    let retained = |name: &str| {
        retained_search_path.is_some_and(|retained| {
            if cfg!(windows) {
                name.eq_ignore_ascii_case(retained)
            } else {
                name == retained
            }
        })
    };
    let explicit_loader_names = command
        .get_envs()
        .keys()
        .filter(|name| is_dynamic_loader_authority_env(name) && !retained(name))
        .cloned()
        .collect::<Vec<_>>();
    for name in explicit_loader_names {
        command.env_remove(&name);
    }
    for (name, _) in std::env::vars_os() {
        let Some(name) = name.to_str() else {
            continue;
        };
        if is_dynamic_loader_authority_env(name) && !retained(name) {
            command.env_remove(name);
        }
    }
    // Also remove the portable fixed set even when absent from the parent:
    // another command-construction layer may have installed an explicit value.
    for name in [
        "LD_PRELOAD",
        "LD_AUDIT",
        "DYLD_INSERT_LIBRARIES",
        "LIBPATH",
        "SHLIB_PATH",
        "LDR_PRELOAD",
        "_RLD_LIST",
        "_RLDN32_LIST",
        "_RLD64_LIST",
    ] {
        if !retained(name) {
            command.env_remove(name);
        }
    }
}

/// Give an exact authenticated tool launcher a deterministic runtime search
/// environment without importing ambient loader authority.
///
/// This is suitable for standalone probes and merge/finalization children.
/// Unit rustc/rustdoc commands use `Compilation::fill_env`, which may append
/// dependency/proc-macro directories; the final execution-edge validator
/// rejects those paths unless they satisfy the same immutable authority.
pub(crate) fn configure_verified_tool_loader_environment(
    command: &mut ProcessBuilder,
    tool: &Path,
) -> CargoResult<()> {
    let search_variable = paths::dylib_path_envvar();
    scrub_dynamic_loader_authority_env(command, Some(search_variable));
    let mut search_path = verified_tool_runtime_library_paths(tool)?;

    if search_variable == "PATH" {
        // Windows PATH is simultaneously DLL search and executable/tool
        // discovery. Replacing it with a Unix-style libdir list breaks
        // rustdoc's downstream system tools. The verified startup gate rejects
        // this unbound closure; this branch only preserves ordinary behavior.
        return Ok(());
    }

    if cfg!(target_os = "macos") {
        search_path.push(PathBuf::from("/usr/lib"));
    }
    // Trust: an authenticated toolchain with no runtime-library directories
    // gets the search variable EXPLICITLY REMOVED, not set to the empty string
    // and not merely left alone. The startup gate already states the rule in
    // both directions — it accepts an absent variable when the closure is empty
    // and rejects a present one — and this edge has to agree with it.
    //
    // Both halves matter. Setting it to `join_paths([])` yields "", and
    // `split_paths("")` produces one EMPTY path on Unix, which the immutability
    // check rejects as not absolute: every verified child spawn from such a
    // toolchain fails closed, which is the wrong direction, since nothing is
    // unsafe about a toolchain that needs no search path. But simply skipping
    // the assignment is worse: the scrub above deliberately RETAINS this
    // variable for the caller to overwrite, so an unset entry falls through to
    // the parent's value and the child would inherit exactly the ambient loader
    // authority this module exists to strip.
    if search_path.is_empty() {
        command.env_remove(search_variable);
    } else {
        command.env(
            search_variable,
            paths::join_paths(&search_path, search_variable)?,
        );
    }
    validate_verified_command_runtime_library_authority(command)
}

/// Validate the actual loader search list at an authenticated compiler or
/// rustdoc execution edge. `Compilation::fill_env` can append dependency,
/// proc-macro, and native-library directories after startup; calling this on
/// the final command prevents those later writable paths from escaping the
/// startup closure check under a misleading "Cargo-owned" label.
pub(crate) fn validate_verified_command_runtime_library_authority(
    command: &ProcessBuilder,
) -> CargoResult<()> {
    if !(crate::is_targo_invocation() && crate::trust_verified_targo()) {
        return Ok(());
    }
    let variable = paths::dylib_path_envvar();
    if variable == "PATH" {
        anyhow::bail!(
            "verified Targo cannot authenticate the final process runtime closure on Windows: PATH combines mutable executable and DLL discovery and no handle-bound launcher is implemented"
        );
    }
    let startup_closure = VERIFIED_RUNTIME_LIBRARY_CLOSURE.get().ok_or_else(|| {
        anyhow::anyhow!(
            "verified Targo command reached an execution edge without an authenticated startup runtime-library closure"
        )
    })?;
    // Trust: an empty authenticated closure is carried by an ABSENT variable,
    // matching what the startup gate accepts. Demanding a value here would
    // reject exactly the toolchains that legitimately need no search path.
    let Some(value) = command.get_env(variable) else {
        if startup_closure.paths.is_empty() {
            return Ok(());
        }
        anyhow::bail!(
            "verified Targo command is missing its authenticated `{variable}` runtime-library closure"
        );
    };
    let runtime_paths = std::env::split_paths(&value).collect::<Vec<_>>();
    if !runtime_paths.starts_with(&startup_closure.paths) {
        anyhow::bail!(
            "verified Targo command runtime-library search order no longer begins with the exact authenticated startup closure"
        );
    }
    // Trust: this per-execution-edge runtime-library authority check fires for
    // every verified child spawn and must run under the same pathname-authority
    // mode as the startup launcher closure — otherwise the two edges disagree
    // about which principals may own the toolchain, and a closure admitted at
    // startup bails here on the identical enumeration.
    validate_immutable_runtime_directories(&runtime_paths, pathname_authority_mode())
}

#[cfg(test)]
mod tests {
    use super::{
        configure_verified_tool_loader_environment, is_ascii_environment_name,
        is_authenticated_targo_process_authority_env, is_benign_build_script_provenance_env,
        is_compiler_flag_environment, is_dynamic_loader_authority_env,
        scan_verified_tool_runtime_library_paths, scrub_dynamic_loader_authority_env,
        validate_verified_targo_startup_loader_environment_from,
        validate_verified_tool_execution_closure, verified_targo_startup_search_variable,
    };
    use cargo_util::ProcessBuilder;

    #[cfg(target_os = "linux")]
    const NESTED_BROKER_TEST_ROLE: &str = "__TARGO_NESTED_BROKER_TEST_ROLE";
    #[cfg(target_os = "linux")]
    const NESTED_BROKER_TEST_MARKER: &str = "__TARGO_NESTED_BROKER_TEST_MARKER";
    #[cfg(target_os = "linux")]
    const NESTED_BROKER_TEST_FILTER: &str =
        "nested_unverified_broker_survives_concurrent_process_generations";

    #[cfg(target_os = "linux")]
    fn nested_broker_test_process(role: &str) -> ProcessBuilder {
        let mut command = ProcessBuilder::new(std::env::current_exe().unwrap());
        command
            .arg(NESTED_BROKER_TEST_FILTER)
            .arg("--nocapture")
            .env(NESTED_BROKER_TEST_ROLE, role);
        command
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn nested_unverified_broker_frames_are_exact() {
        let root = std::process::id();
        let requester = root.wrapping_add(1);
        let nonce = [0xa5; super::TARGO_NESTED_UNVERIFIED_NONCE_BYTES];
        let request = super::nested_unverified_request(requester, &nonce);
        assert_eq!(
            super::parse_nested_unverified_request(&request).unwrap(),
            (requester, nonce)
        );

        let response = super::nested_unverified_response(root, requester, &nonce);
        assert_eq!(
            super::parse_nested_unverified_response(&response).unwrap(),
            (root, requester, nonce)
        );

        let mut wrong_schema = response.clone();
        wrong_schema[0] ^= 0xff;
        assert!(
            super::parse_nested_unverified_response(&wrong_schema)
                .unwrap_err()
                .to_string()
                .contains("invalid schema")
        );

        let mut oversized = request;
        oversized.push(0);
        assert!(
            super::parse_nested_unverified_request(&oversized)
                .unwrap_err()
                .to_string()
                .contains("invalid schema")
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the subprocess role is intentionally carried across a real exec boundary"
    )]
    fn nested_unverified_process_guards_reject_self_nonancestor_wrong_executable_and_stale_pid() {
        use std::process::Stdio;

        const SIBLING_ROLE: &str = "nonancestor-sibling";
        if std::env::var_os(NESTED_BROKER_TEST_ROLE).as_deref()
            == Some(std::ffi::OsStr::new(SIBLING_ROLE))
        {
            let mut input = std::io::stdin().lock();
            let mut byte = [0_u8; 1];
            let _ = std::io::Read::read(&mut input, &mut byte);
            return;
        }

        let current = std::process::id();
        let root =
            super::LinuxProcessGuard::capture(current, super::ExecutableCapture::Required).unwrap();
        let self_error = super::ensure_nested_unverified_ancestor(&root, current).unwrap_err();
        assert!(self_error.to_string().contains("not an ancestor"));

        let parent = super::read_linux_process_stat(current).unwrap().0;
        let wrong_executable =
            super::validate_nested_unverified_targo_process(parent, &root).unwrap_err();
        assert!(
            wrong_executable
                .to_string()
                .contains("does not run the expected opened Targo executable identity"),
            "{wrong_executable:#}"
        );

        assert!(
            super::LinuxProcessGuard::capture(u32::MAX, super::ExecutableCapture::Required)
                .unwrap_err()
                .to_string()
                .contains("does not fit Linux pid_t")
        );

        let mut sibling = std::process::Command::new(std::env::current_exe().unwrap())
            .arg(
                "nested_unverified_process_guards_reject_self_nonancestor_wrong_executable_and_stale_pid",
            )
            .arg("--nocapture")
            .env(NESTED_BROKER_TEST_ROLE, SIBLING_ROLE)
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();
        let sibling_root =
            super::LinuxProcessGuard::capture(sibling.id(), super::ExecutableCapture::Required)
                .unwrap();
        let nonancestor =
            super::ensure_nested_unverified_ancestor(&sibling_root, current).unwrap_err();
        assert!(
            nonancestor.to_string().contains("is not a live ancestor"),
            "{nonancestor:#}"
        );
        drop(sibling.stdin.take());
        assert!(sibling.wait().unwrap().success());
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the regression authenticates a live broker across concurrent real exec generations"
    )]
    fn nested_unverified_broker_survives_concurrent_process_generations() {
        let role = std::env::var_os(NESTED_BROKER_TEST_ROLE);
        let endpoint = std::env::var_os(super::TARGO_NESTED_UNVERIFIED_BROKER_ENV);
        if role.as_deref() == Some(std::ffi::OsStr::new("generation-1")) {
            let endpoint = endpoint.unwrap();
            super::authenticate_nested_unverified_targo_broker(&endpoint).unwrap();
            let marker = std::env::var_os(NESTED_BROKER_TEST_MARKER).unwrap();
            let mut child = nested_broker_test_process("generation-2");
            child
                .env(super::TARGO_NESTED_UNVERIFIED_BROKER_ENV, endpoint)
                .env(NESTED_BROKER_TEST_MARKER, marker)
                .exec()
                .unwrap();
            return;
        }
        if role.as_deref() == Some(std::ffi::OsStr::new("generation-2")) {
            super::authenticate_nested_unverified_targo_broker(&endpoint.unwrap()).unwrap();
            std::fs::write(
                std::env::var_os(NESTED_BROKER_TEST_MARKER).unwrap(),
                b"authenticated",
            )
            .unwrap();
            return;
        }

        let broker = super::NestedUnverifiedTargoBroker::start().unwrap();
        let directory = tempfile::TempDir::new().unwrap();
        let mut children = Vec::new();
        for index in 0..2 {
            let marker = directory.path().join(format!("generation-{index}"));
            let mut child = nested_broker_test_process("generation-1");
            child
                .env(super::TARGO_NESTED_UNVERIFIED_BROKER_ENV, &broker.endpoint)
                .env(NESTED_BROKER_TEST_MARKER, &marker);
            children.push((child, marker));
        }
        let mut running = Vec::new();
        for (child, _) in &children {
            running.push(child.build_command().spawn().unwrap());
        }
        for child in &mut running {
            assert!(child.wait().unwrap().success());
        }
        for (_, marker) in children {
            assert_eq!(std::fs::read(marker).unwrap(), b"authenticated");
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the regression models a malicious pre-exec authority server with actual subprocess environment and exec boundaries"
    )]
    fn preexec_inherited_listener_helper_cannot_forge_broker_root() {
        use std::os::linux::net::SocketAddrExt as _;
        use std::os::unix::process::CommandExt as _;
        use std::time::{Duration, Instant};

        const FILTER: &str = "preexec_inherited_listener_helper_cannot_forge_broker_root";
        const ENDPOINT: &str = "__TARGO_PREEXEC_FORGERY_ENDPOINT";
        const LISTENER_FD: &str = "__TARGO_PREEXEC_FORGERY_LISTENER_FD";
        const ROOT_PID: &str = "__TARGO_PREEXEC_FORGERY_ROOT_PID";
        const READY: &str = "__TARGO_PREEXEC_FORGERY_READY";
        const RESULT: &str = "__TARGO_PREEXEC_FORGERY_RESULT";

        let role = std::env::var_os(NESTED_BROKER_TEST_ROLE);
        if role.as_deref() == Some(std::ffi::OsStr::new("forgery-server")) {
            use std::io::Write as _;
            use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};

            let descriptor: libc::c_int = std::env::var(LISTENER_FD).unwrap().parse().unwrap();
            // SAFETY: ProcessBuilder transferred this one live listener
            // descriptor to this helper, which is its first Rust owner here.
            let descriptor = unsafe { OwnedFd::from_raw_fd(descriptor) };
            let listener = std::os::unix::net::UnixListener::from(descriptor);
            let (mut connection, _) = listener.accept().unwrap();
            super::configure_nested_unverified_targo_stream(&connection).unwrap();
            let requester =
                super::nested_unverified_socket_peer_pid(connection.as_raw_fd()).unwrap();
            let request = super::receive_nested_unverified_frame(
                &mut connection,
                super::TARGO_NESTED_UNVERIFIED_REQUEST_SCHEMA.len()
                    + std::mem::size_of::<u32>()
                    + super::TARGO_NESTED_UNVERIFIED_NONCE_BYTES,
                "forged request",
            )
            .unwrap();
            let (framed_requester, nonce) =
                super::parse_nested_unverified_request(&request).unwrap();
            assert_eq!(framed_requester, requester);
            let forged_root: u32 = std::env::var(ROOT_PID).unwrap().parse().unwrap();
            let callback_address = super::nested_unverified_callback_address(&nonce).unwrap();
            let mut callback =
                std::os::unix::net::UnixStream::connect_addr(&callback_address).unwrap();
            super::configure_nested_unverified_targo_stream(&callback).unwrap();
            let response = super::nested_unverified_response(forged_root, requester, &nonce);
            callback.write_all(&response).unwrap();
            callback.shutdown(std::net::Shutdown::Write).unwrap();
            return;
        }
        if role.as_deref() == Some(std::ffi::OsStr::new("preexec-root")) {
            use std::os::fd::{AsRawFd as _, OwnedFd};
            use std::sync::Arc;

            let endpoint = std::env::var_os(ENDPOINT).unwrap();
            let address =
                std::os::unix::net::SocketAddr::from_abstract_name(endpoint.as_encoded_bytes())
                    .unwrap();
            let forged_listener = std::os::unix::net::UnixListener::bind_addr(&address).unwrap();
            let server_listener: OwnedFd = forged_listener.try_clone().unwrap().into();
            let server_listener = Arc::new(server_listener);
            let listener_fd = server_listener.as_raw_fd();
            let mut server = ProcessBuilder::new(std::env::current_exe().unwrap());
            server
                .arg(FILTER)
                .arg("--nocapture")
                .env(NESTED_BROKER_TEST_ROLE, "forgery-server")
                .env(LISTENER_FD, listener_fd.to_string())
                .env(ROOT_PID, std::process::id().to_string())
                .inherit_fd_for_exec(server_listener)
                .unwrap();
            server.build_command().spawn().unwrap();
            std::process::Command::new(std::env::current_exe().unwrap())
                .arg(FILTER)
                .arg("--nocapture")
                .env(NESTED_BROKER_TEST_ROLE, "forgery-client")
                .env(ENDPOINT, &endpoint)
                .env(READY, std::env::var_os(READY).unwrap())
                .env(RESULT, std::env::var_os(RESULT).unwrap())
                .spawn()
                .unwrap();
            let error = std::process::Command::new(std::env::current_exe().unwrap())
                .arg(FILTER)
                .arg("--nocapture")
                .env(NESTED_BROKER_TEST_ROLE, "unauthorized-metadata-root")
                .env(READY, std::env::var_os(READY).unwrap())
                .env(RESULT, std::env::var_os(RESULT).unwrap())
                .exec();
            panic!("failed to exec same-executable unauthorized root: {error}");
        }
        if role.as_deref() == Some(std::ffi::OsStr::new("unauthorized-metadata-root")) {
            let ready = std::env::var_os(READY).unwrap();
            let result = std::env::var_os(RESULT).unwrap();
            std::fs::write(&ready, b"ready").unwrap();
            let deadline = Instant::now() + Duration::from_secs(5);
            while !std::path::Path::new(&result).exists() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            assert_eq!(std::fs::read(result).unwrap(), b"rejected");
            return;
        }
        if role.as_deref() == Some(std::ffi::OsStr::new("forgery-client")) {
            let ready = std::env::var_os(READY).unwrap();
            let deadline = Instant::now() + Duration::from_secs(5);
            while !std::path::Path::new(&ready).exists() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            assert!(std::path::Path::new(&ready).exists());
            let endpoint = std::env::var_os(ENDPOINT).unwrap();
            let error = super::authenticate_nested_unverified_targo_broker(&endpoint).unwrap_err();
            assert!(
                error.to_string().contains("live callback peer"),
                "{error:#}"
            );
            std::fs::write(std::env::var_os(RESULT).unwrap(), b"rejected").unwrap();
            return;
        }

        let directory = tempfile::TempDir::new().unwrap();
        let ready = directory.path().join("root-ready");
        let result = directory.path().join("forgery-result");
        let endpoint = format!("trust-targo-preexec-forgery-{}", std::process::id());
        let mut root = ProcessBuilder::new(std::env::current_exe().unwrap());
        root.arg(FILTER)
            .arg("--nocapture")
            .env(NESTED_BROKER_TEST_ROLE, "preexec-root")
            .env(ENDPOINT, endpoint)
            .env(READY, &ready)
            .env(RESULT, &result)
            .exec()
            .unwrap();
        assert_eq!(std::fs::read(result).unwrap(), b"rejected");
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the regression waits for a real broker ancestor to exit before attempting authentication"
    )]
    fn nested_unverified_broker_fails_closed_after_root_death_and_reparenting() {
        use std::time::{Duration, Instant};

        const FILTER: &str =
            "nested_unverified_broker_fails_closed_after_root_death_and_reparenting";
        const ROOT_PID: &str = "__TARGO_DEAD_BROKER_ROOT_PID";
        const RESULT: &str = "__TARGO_DEAD_BROKER_RESULT";

        let role = std::env::var_os(NESTED_BROKER_TEST_ROLE);
        if role.as_deref() == Some(std::ffi::OsStr::new("broker-root")) {
            let broker = super::NestedUnverifiedTargoBroker::start().unwrap();
            std::process::Command::new(std::env::current_exe().unwrap())
                .arg(FILTER)
                .arg("--nocapture")
                .env(NESTED_BROKER_TEST_ROLE, "orphan-client")
                .env(super::TARGO_NESTED_UNVERIFIED_BROKER_ENV, &broker.endpoint)
                .env(ROOT_PID, std::process::id().to_string())
                .env(RESULT, std::env::var_os(RESULT).unwrap())
                .spawn()
                .unwrap();
            return;
        }
        if role.as_deref() == Some(std::ffi::OsStr::new("orphan-client")) {
            let root_pid: u32 = std::env::var(ROOT_PID).unwrap().parse().unwrap();
            let deadline = Instant::now() + Duration::from_secs(5);
            while std::path::Path::new(&format!("/proc/{root_pid}")).exists()
                && Instant::now() < deadline
            {
                std::thread::sleep(Duration::from_millis(10));
            }
            assert!(!std::path::Path::new(&format!("/proc/{root_pid}")).exists());
            let endpoint = std::env::var_os(super::TARGO_NESTED_UNVERIFIED_BROKER_ENV).unwrap();
            assert!(super::authenticate_nested_unverified_targo_broker(&endpoint).is_err());
            std::fs::write(std::env::var_os(RESULT).unwrap(), b"rejected").unwrap();
            return;
        }

        let directory = tempfile::TempDir::new().unwrap();
        let result = directory.path().join("dead-root-result");
        let mut root = ProcessBuilder::new(std::env::current_exe().unwrap());
        root.arg(FILTER)
            .arg("--nocapture")
            .env(NESTED_BROKER_TEST_ROLE, "broker-root")
            .env(RESULT, &result)
            .exec()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        while !result.exists() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(std::fs::read(result).unwrap(), b"rejected");
    }

    #[cfg(not(target_os = "linux"))]
    #[test]
    fn unsupported_platform_fails_closed_for_nested_unverified_authority() {
        assert!(!super::nested_unverified_targo_handoff_active());
        assert!(
            super::reject_unsupported_nested_unverified_targo_handoff()
                .unwrap_err()
                .to_string()
                .contains("not implemented")
        );
    }

    #[test]
    fn benign_provenance_allowlist_is_exact_and_does_not_admit_authority() {
        // The two provenance stamps are admitted (any ASCII case).
        assert!(is_benign_build_script_provenance_env("TRUST_MC_GIT_SHA"));
        assert!(is_benign_build_script_provenance_env("trust_mc_git_dirty"));
        // No authority channel is admitted by prefix or lookalike.
        for name in [
            "TRUST_NO_VERIFY",
            "TRUST_MC_GIT_SHA_EVIL",
            "TRUST_TARGO_BIN",
            "TRUSTC",
            "TRUST_MC",
        ] {
            assert!(
                !is_benign_build_script_provenance_env(name),
                "{name} must not be treated as a benign provenance stamp"
            );
        }
    }

    #[test]
    fn authority_classifier_is_closed_and_ascii_case_insensitive() {
        for name in [
            "TRUST_NO_VERIFY",
            "TRUST_TARGO_NESTED_UNVERIFIED_BROKER",
            "trust_no_verify",
            "LD_PRELOAD",
            "dyld_insert_libraries",
            "rustflags_not_bootstrap",
            "RUSTC_OVERRIDE_VERSION_STRING",
            "rustc_force_rustc_version",
            "RUST_TARGET_PATH",
            "rust_target_path",
            "__CARGO_FIX_YOLO",
            "__cargo_fix_broken_code",
            "CARGO_FIX_MAX_RETRIES",
            "tippy_encoded_args",
            "ClIpPy_ArGs",
            "CARGO_PRIMARY_PACKAGE",
            "cargo_primary_package",
            "CARGO",
            "cargo",
            "SAFE_λ",
        ] {
            assert!(
                is_authenticated_targo_process_authority_env(name),
                "accepted authority name {name:?}"
            );
        }
        for name in ["SAFE_ENV", "CARGO_NET_OFFLINE", "RUST_LOG"] {
            assert!(
                !is_authenticated_targo_process_authority_env(name),
                "over-reserved ordinary name {name:?}"
            );
        }
    }

    #[test]
    fn compiler_flag_and_ascii_helpers_share_portable_semantics() {
        assert!(is_compiler_flag_environment(
            "cargo_target_x86_64_unknown_linux_gnu_rustflags"
        ));
        assert!(!is_compiler_flag_environment("TRUST_RUSTC_ARG_LOG"));
        assert!(is_ascii_environment_name("PATH"));
        assert!(!is_ascii_environment_name("PÅTH"));
    }

    #[test]
    fn dynamic_loader_authority_is_closed_and_scrubbable() {
        for name in [
            "LD_PRELOAD",
            "ld_audit",
            "DYLD_INSERT_LIBRARIES",
            "dyld_library_path",
            "LIBPATH",
            "SHLIB_PATH",
            "LDR_PRELOAD",
            "LDR_AUDIT",
            "_RLD_CUSTOM_PATH",
            "_RLD64_LIST",
        ] {
            assert!(is_dynamic_loader_authority_env(name), "accepted {name}");
        }
        assert!(!is_dynamic_loader_authority_env("PATH"));

        let mut command = ProcessBuilder::new("trustdoc");
        command
            .env("LD_PRELOAD", "/attacker/preload.so")
            .env("DYLD_EXPLICIT_OVERLAY_NOT_IN_PARENT", "/attacker/overlay")
            .env("LD_LIBRARY_PATH", "/trusted/toolchain/lib");
        scrub_dynamic_loader_authority_env(&mut command, Some("LD_LIBRARY_PATH"));
        assert_eq!(command.get_env("LD_PRELOAD"), None);
        assert_eq!(command.get_env("DYLD_EXPLICIT_OVERLAY_NOT_IN_PARENT"), None);
        assert_eq!(
            command.get_env("LD_LIBRARY_PATH"),
            Some("/trusted/toolchain/lib".into())
        );

        let directory = tempfile::TempDir::new().unwrap();
        let bin = directory.path().join("bin");
        let lib = directory.path().join("lib");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&lib).unwrap();
        let trustdoc = bin.join("trustdoc");
        let mut command = ProcessBuilder::new(&trustdoc);
        command.env("LD_PRELOAD", "/attacker/preload.so");
        if cargo_util::paths::dylib_path_envvar() == "PATH" {
            command.env("PATH", "retained-windows-tool-path");
        }
        configure_verified_tool_loader_environment(&mut command, &trustdoc).unwrap();
        assert_eq!(command.get_env("LD_PRELOAD"), None);
        let search = command
            .get_env(cargo_util::paths::dylib_path_envvar())
            .unwrap();
        if cargo_util::paths::dylib_path_envvar() == "PATH" {
            assert_eq!(search, "retained-windows-tool-path");
        } else {
            let search = std::env::split_paths(&search).collect::<Vec<_>>();
            assert!(
                search
                    .iter()
                    .any(|path| path == &lib.canonicalize().unwrap())
            );
            assert!(
                !search
                    .iter()
                    .any(|path| path == std::path::Path::new("/attacker"))
            );
        }
    }

    #[test]
    fn a_toolchain_with_no_runtime_library_directories_removes_the_search_variable() {
        // A toolchain that needs no library search path is ordinary, not
        // suspicious, and it must reach its child with the variable REMOVED.
        // Setting it to the empty string is what the startup gate refuses, and
        // is not merely cosmetic: `split_paths("")` yields one EMPTY path on
        // Unix, which the immutability check rejects as not absolute, so every
        // verified child spawn from such a toolchain fails closed. Leaving the
        // variable alone is worse still — the scrub retains it for the caller
        // to overwrite, so an untouched entry inherits the parent's value.
        let variable = cargo_util::paths::dylib_path_envvar();
        if variable == "PATH" {
            return; // Windows retains PATH wholesale; the empty case cannot arise.
        }

        let directory = tempfile::TempDir::new().unwrap();
        let bin = directory.path().join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        let trustdoc = bin.join("trustdoc");
        let mut command = ProcessBuilder::new(&trustdoc);

        configure_verified_tool_loader_environment(&mut command, &trustdoc).unwrap();

        if cfg!(target_os = "macos") {
            // macOS always contributes /usr/lib, so the list is never empty.
            assert!(command.get_env(variable).is_some());
        } else {
            // `get_env` reads through to the ambient environment for any
            // variable this builder has no entry for, so it answers None here
            // only because the removal is explicit — which is the property
            // under test, not an artifact of the test environment.
            assert_eq!(
                command.get_env(variable),
                None,
                "an empty runtime-library closure must reach the child as an \
                 explicitly removed variable"
            );
            assert_eq!(
                command.get_envs().get(variable),
                Some(&None),
                "the variable must be recorded as REMOVED, not merely left \
                 unset — an unset entry is inherited from the parent"
            );
        }
    }

    #[test]
    fn verified_targo_startup_accepts_only_reconstructed_runtime_search_path() {
        let directory = tempfile::TempDir::new().unwrap();
        let sysroot = directory.path().join("stage2");
        let bin = sysroot.join("bin");
        let lib = sysroot.join("lib");
        let rustlib = lib.join("rustlib").join("host").join("lib");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&rustlib).unwrap();
        let targo = bin.join("targo");

        let Some(variable) = verified_targo_startup_search_variable() else {
            validate_verified_targo_startup_loader_environment_from(
                &targo,
                [("SAFE_ENV", "value")],
            )
            .unwrap();
            assert!(
                validate_verified_targo_startup_loader_environment_from(
                    &targo,
                    [("LD_PRELOAD", "/attacker/preload")],
                )
                .is_err()
            );
            return;
        };

        let expected =
            std::env::join_paths([lib.canonicalize().unwrap(), rustlib.canonicalize().unwrap()])
                .unwrap();
        validate_verified_targo_startup_loader_environment_from(
            &targo,
            [(std::ffi::OsString::from(variable), expected.clone())],
        )
        .unwrap();

        let reordered =
            std::env::join_paths([rustlib.canonicalize().unwrap(), lib.canonicalize().unwrap()])
                .unwrap();
        assert!(
            validate_verified_targo_startup_loader_environment_from(
                &targo,
                [(std::ffi::OsString::from(variable), reordered)],
            )
            .is_err(),
            "loader search order is part of execution authority"
        );

        let attacker = directory.path().join("attacker");
        std::fs::create_dir_all(&attacker).unwrap();
        let extended = std::env::join_paths([
            lib.canonicalize().unwrap(),
            rustlib.canonicalize().unwrap(),
            attacker,
        ])
        .unwrap();
        let error = validate_verified_targo_startup_loader_environment_from(
            &targo,
            [(std::ffi::OsString::from(variable), extended)],
        )
        .unwrap_err();
        assert!(error.to_string().contains("does not exactly match"));

        let error = validate_verified_targo_startup_loader_environment_from(
            &targo,
            [
                (std::ffi::OsString::from(variable), expected),
                (
                    std::ffi::OsString::from("LD_PRELOAD"),
                    std::ffi::OsString::from("/attacker/preload"),
                ),
            ],
        )
        .unwrap_err();
        assert!(error.to_string().contains("before Targo began"));
    }

    #[test]
    fn runtime_path_scan_preserves_semantic_tier_precedence() {
        let directory = tempfile::TempDir::new().unwrap();
        let sysroot = directory.path().join("stage2");
        let bin = sysroot.join("bin");
        let lib = sysroot.join("lib");
        let rustlib_a = lib.join("rustlib").join("a-target").join("lib");
        let rustlib_z = lib.join("rustlib").join("z-target").join("lib");
        let deps_a = directory
            .path()
            .join("stage2-rustc")
            .join("a-host")
            .join("release")
            .join("deps");
        let deps_z = directory
            .path()
            .join("stage2-rustc")
            .join("z-host")
            .join("release")
            .join("deps");
        for path in [&bin, &lib, &rustlib_z, &rustlib_a, &deps_z, &deps_a] {
            std::fs::create_dir_all(path).unwrap();
        }

        let observed = scan_verified_tool_runtime_library_paths(&bin.join("targo")).unwrap();
        let canonical = |path: &std::path::Path| path.canonicalize().unwrap();
        assert_eq!(
            observed,
            [
                canonical(&lib),
                canonical(&rustlib_a),
                canonical(&rustlib_z),
                canonical(&deps_a),
                canonical(&deps_z),
            ],
            "global lexical sorting must not let stage-rustc deps shadow sysroot libraries"
        );
    }

    /// Trust: the substitution predicate, exercised on one already-`lstat`ed
    /// object so the result does not depend on whatever the ambient temp root
    /// happens to be. This is the decision the whole pathname walk is built out
    /// of: ownership by root or by the invoking identity is admitted, ownership
    /// by any other principal is not, and a group- or world-writable object is
    /// refused no matter who owns it.
    #[cfg(unix)]
    #[test]
    fn pathname_authority_admits_caller_owned_and_refuses_shared_writers() {
        use super::PathnameAuthorityMode;
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let directory = tempfile::TempDir::new().unwrap();
        let object = directory.path().join("trustc");
        std::fs::write(&object, b"fixture").unwrap();
        let effective_uid = unsafe { libc::geteuid() };

        let judge = |mode_bits: u32, authority: PathnameAuthorityMode| {
            std::fs::set_permissions(&object, std::fs::Permissions::from_mode(mode_bits)).unwrap();
            let metadata = std::fs::symlink_metadata(&object).unwrap();
            assert_eq!(
                metadata.uid(),
                effective_uid,
                "fixture must be owned by the invoking identity"
            );
            super::validate_authority_ownership(
                &metadata,
                &object,
                "verified tool launcher",
                authority,
                effective_uid,
            )
        };

        // ACCEPTED: owned by the caller and closed to every other principal.
        // This is what `rustup toolchain link` and every in-tree stage2 produce;
        // refusing it is refusing the only toolchain a developer can install.
        for accepted in [0o755, 0o700, 0o555, 0o750] {
            judge(accepted, PathnameAuthorityMode::CallerOwned).unwrap_or_else(|error| {
                panic!("caller-owned mode {accepted:#o} must be admitted: {error:#}")
            });
        }

        // REJECTED: a writer other than the owner. Group- and world-writable are
        // the actual substitution primitive and stay refused in every mode.
        for refused in [0o775, 0o757, 0o777, 0o707, 0o770] {
            let error = judge(refused, PathnameAuthorityMode::CallerOwned).unwrap_err();
            let rendered = format!("{error:#}");
            assert!(
                rendered.contains("group- or world-writable"),
                "mode {refused:#o} must be refused as a shared-writer object: {rendered}"
            );
        }

        // REJECTED: a foreign owner, even with tight mode bits — that principal
        // can replace the object between authorization and execution.
        std::fs::set_permissions(&object, std::fs::Permissions::from_mode(0o755)).unwrap();
        let metadata = std::fs::symlink_metadata(&object).unwrap();
        let foreign = super::validate_authority_ownership(
            &metadata,
            &object,
            "verified tool launcher",
            PathnameAuthorityMode::CallerOwned,
            effective_uid.wrapping_add(1),
        )
        .unwrap_err();
        assert!(
            format!("{foreign:#}").contains("neither root nor the invoking identity"),
            "a foreign-owned execution object must be refused: {foreign:#}"
        );

        // The opt-in release predicate is unchanged: it still demands root.
        let sealed = super::validate_authority_ownership(
            &metadata,
            &object,
            "verified tool launcher",
            PathnameAuthorityMode::SealedRelease,
            effective_uid,
        )
        .unwrap_err();
        assert!(
            format!("{sealed:#}").contains("TRUST_REQUIRE_SEALED_LAUNCHER"),
            "sealed-release mode must still demand a root-owned installation: {sealed:#}"
        );
    }

    /// A fixture root every one of whose ancestors is already owned by root or
    /// by the invoking identity and closed to group/world writes. `/tmp` is
    /// `1777` on most hosts, so the shared temp root cannot host a test of the
    /// *accepting* direction; this crate's own build-output directory can, and
    /// the per-user macOS `TMPDIR` can too.
    #[cfg(unix)]
    fn caller_clean_fixture_root() -> Option<std::path::PathBuf> {
        use std::os::unix::fs::MetadataExt as _;

        fn is_caller_clean(root: &std::path::Path) -> bool {
            let effective_uid = unsafe { libc::geteuid() };
            let mut current = std::path::PathBuf::from("/");
            for component in root.components() {
                match component {
                    std::path::Component::RootDir => {}
                    std::path::Component::Normal(name) => current.push(name),
                    _ => return false,
                }
                let Ok(metadata) = std::fs::symlink_metadata(&current) else {
                    return false;
                };
                if !(metadata.uid() == 0 || metadata.uid() == effective_uid) {
                    return false;
                }
                if metadata.mode() & 0o022 != 0 {
                    return false;
                }
            }
            true
        }

        [
            std::path::Path::new(env!("OUT_DIR")).canonicalize().ok(),
            std::env::temp_dir().canonicalize().ok(),
        ]
        .into_iter()
        .flatten()
        .find(|root| is_caller_clean(root))
    }

    #[cfg(unix)]
    fn caller_owned_toolchain_fixture(
        root: &std::path::Path,
        name: &str,
    ) -> (std::path::PathBuf, std::path::PathBuf) {
        use std::os::unix::fs::PermissionsExt as _;

        let sysroot = root.join(name);
        let _ = std::fs::remove_dir_all(&sysroot);
        let bin = sysroot.join("bin");
        let lib = sysroot.join("lib");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&lib).unwrap();
        for directory in [&sysroot, &bin, &lib] {
            std::fs::set_permissions(directory, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let targo = bin.join("targo");
        std::fs::write(&targo, b"fixture").unwrap();
        std::fs::set_permissions(&targo, std::fs::Permissions::from_mode(0o755)).unwrap();
        (targo, lib)
    }

    /// Trust: the headline regression. A toolchain under a user-owned `$HOME` —
    /// what `rustup toolchain link` and every in-tree stage2 produce — must
    /// carry verified execution authority. Refusing it made `targo trust check`
    /// unusable for every developer, while the visible failure was the
    /// *downstream* "missing coverage_summary transport" of a compiler that was
    /// never launched.
    #[cfg(unix)]
    #[test]
    fn verified_execution_admits_a_caller_owned_toolchain() {
        let Some(root) = caller_clean_fixture_root() else {
            // Refuse to claim a pass that was not observed: without a
            // caller-clean ancestor chain this host cannot express the case.
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (targo, lib) = caller_owned_toolchain_fixture(&root, "caller-owned-stage2");

        validate_verified_tool_execution_closure(&targo, &[lib.canonicalize().unwrap()])
            .unwrap_or_else(|error| {
                panic!(
                    "a caller-owned, non-group/world-writable toolchain must carry verified execution authority: {error:#}"
                )
            });
    }

    /// The property the old rule really defended, kept: a path component another
    /// principal can write is still refused — on the very fixture the accepting
    /// test above admits, so the two differ in exactly one bit.
    #[cfg(unix)]
    #[test]
    fn verified_execution_rejects_group_or_world_writable_components() {
        use std::os::unix::fs::PermissionsExt as _;

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };

        for (name, shared_mode) in [
            ("group-writable-stage2", 0o775),
            ("world-writable-stage2", 0o757),
        ] {
            let (targo, lib) = caller_owned_toolchain_fixture(&root, name);
            let bin = targo.parent().unwrap().to_path_buf();
            std::fs::set_permissions(&bin, std::fs::Permissions::from_mode(shared_mode)).unwrap();

            let error =
                validate_verified_tool_execution_closure(&targo, &[lib.canonicalize().unwrap()])
                    .unwrap_err();
            let rendered = format!("{error:#}");
            assert!(
                rendered.contains("group- or world-writable"),
                "a {shared_mode:#o} launcher directory must not carry execution authority: {rendered}"
            );
            assert!(
                rendered.contains(&bin.display().to_string()),
                "the refusal must name the shared-writable component `{}`: {rendered}",
                bin.display()
            );
            std::fs::set_permissions(&bin, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
    }

    /// A runtime-library directory another principal can write is still refused:
    /// the loader would consume whatever that principal put there.
    #[cfg(unix)]
    #[test]
    fn verified_runtime_closure_rejects_shared_writable_directory() {
        use super::PathnameAuthorityMode;
        use std::os::unix::fs::PermissionsExt as _;

        for shared_mode in [0o775, 0o777] {
            let directory = tempfile::TempDir::new().unwrap();
            let runtime = directory.path().canonicalize().unwrap();
            std::fs::set_permissions(&runtime, std::fs::Permissions::from_mode(shared_mode))
                .unwrap();
            let error = super::validate_immutable_runtime_directories(
                &[runtime],
                PathnameAuthorityMode::CallerOwned,
            )
            .unwrap_err();
            let rendered = format!("{error:#}");
            assert!(
                rendered.contains("group- or world-writable") || rendered.contains("runs as root"),
                "a {shared_mode:#o} runtime directory lets any local principal add or replace a dylib after the snapshot: {rendered}"
            );
        }
    }

    /// A symlink in a loader search directory can redirect a loaded object to
    /// somewhere outside the authenticated closure, so it is still refused even
    /// though the directory itself is caller-owned.
    #[cfg(unix)]
    #[test]
    fn verified_runtime_closure_rejects_symlinked_candidate() {
        use super::PathnameAuthorityMode;

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (_targo, lib) = caller_owned_toolchain_fixture(&root, "symlinked-candidate-stage2");
        let outside = root.join("symlinked-candidate-outside.dylib");
        std::fs::write(&outside, b"fixture").unwrap();
        std::os::unix::fs::symlink(&outside, lib.join("libstd.dylib")).unwrap();

        let error = super::validate_immutable_runtime_directories(
            &[lib.canonicalize().unwrap()],
            PathnameAuthorityMode::CallerOwned,
        )
        .unwrap_err();
        let rendered = format!("{error:#}");
        assert!(
            rendered.contains("can redirect a loaded object"),
            "a symlinked loader candidate must not be admitted: {rendered}"
        );
    }

    /// Trust: metadata alone does not notice an in-place rewrite of a binary the
    /// invoking identity owns — the residual that admitting a caller-owned
    /// toolchain carries, and the one a root-ownership rule did not close either
    /// (it only refused every real toolchain). The launcher's bytes are pinned
    /// at first authorization and re-checked on every later execution edge, so a
    /// persisted substitution is detected rather than trusted.
    #[cfg(unix)]
    #[test]
    fn opened_launcher_content_is_pinned_across_execution_edges() {
        use super::PathnameAuthorityMode;
        use std::os::unix::fs::PermissionsExt as _;

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (targo, _lib) = caller_owned_toolchain_fixture(&root, "pinned-stage2");

        super::validate_opened_tool_launcher(&targo, PathnameAuthorityMode::CallerOwned)
            .expect("first authorization pins the launcher content");
        super::validate_opened_tool_launcher(&targo, PathnameAuthorityMode::CallerOwned)
            .expect("an unchanged launcher must keep its authority");

        // A same-identity build script rewriting the compiler in place keeps the
        // uid, the mode, the device and the inode.
        std::fs::write(&targo, b"substituted").unwrap();
        std::fs::set_permissions(&targo, std::fs::Permissions::from_mode(0o755)).unwrap();
        let error = super::validate_opened_tool_launcher(&targo, PathnameAuthorityMode::CallerOwned)
            .unwrap_err();
        let rendered = format!("{error:#}");
        assert!(
            rendered.contains("changed content after it was authenticated"),
            "an in-place rewrite must lose execution authority: {rendered}"
        );
    }

    /// The sealed-release predicate is still reachable and still fails closed,
    /// so it cannot rot while the default lane runs.
    #[cfg(unix)]
    #[test]
    fn sealed_release_mode_still_refuses_a_caller_owned_toolchain() {
        use super::PathnameAuthorityMode;

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (targo, _lib) = caller_owned_toolchain_fixture(&root, "sealed-release-stage2");

        let error = super::validate_unprivileged_authority_path(
            &targo,
            false,
            "verified tool launcher",
            PathnameAuthorityMode::SealedRelease,
        )
        .unwrap_err();
        let rendered = format!("{error:#}");
        assert!(
            rendered.contains("TRUST_REQUIRE_SEALED_LAUNCHER"),
            "the opt-in release predicate must still demand a root-owned installation: {rendered}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn verified_launcher_modes_reject_privilege_and_sticky_bits() {
        assert!(super::launcher_mode_is_safe(0o755));
        for mode in [0o644, 0o4755, 0o2755, 0o1755, 0o6755, 0o7755] {
            assert!(
                !super::launcher_mode_is_safe(mode),
                "accepted unsafe launcher mode {mode:#o}"
            );
        }
    }

    #[test]
    fn platform_default_loader_closure_is_an_explicit_release_blocker() {
        let error = super::reject_unbound_platform_loader_authority(std::path::Path::new(
            "/privileged/toolchain/bin/trustdoc",
        ))
        .unwrap_err();
        let rendered = error.to_string();
        assert!(
            rendered.contains("RPATH/RUNPATH/install-name"),
            "{rendered}"
        );
        assert!(rendered.contains("OS default loader"), "{rendered}");
        assert!(rendered.contains("sealed handle-bound"), "{rendered}");
    }

    #[cfg(unix)]
    #[test]
    fn verified_runtime_paths_reject_toolchain_local_symlink_components() {
        let directory = tempfile::TempDir::new().unwrap();
        let sysroot = directory.path().join("stage2");
        let bin = sysroot.join("bin");
        let outside = directory.path().join("outside-lib");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&outside).unwrap();
        std::os::unix::fs::symlink(&outside, sysroot.join("lib")).unwrap();

        let error = validate_verified_targo_startup_loader_environment_from(
            &bin.join("targo"),
            std::iter::empty::<(std::ffi::OsString, std::ffi::OsString)>(),
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("not a plain directory"),
            "unexpected error: {error:#}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn verified_runtime_paths_tolerate_regular_file_siblings() {
        // cargo writes its own cache files (`.rustc_info.json`, `CACHEDIR.TAG`)
        // into the `<stage>-rustc` build-deps root, and rustlib carries
        // installer metadata files (`components`, `rust-installer-version`),
        // both beside the per-target directories. Those regular-file siblings
        // must be skipped during runtime library-path reconstruction — NOT trip
        // the plain-directory authority check, which hard-bails on a
        // non-directory path component and would otherwise abort verified
        // `targo` startup on any warm build tree.
        let directory = tempfile::TempDir::new().unwrap();
        let sysroot = directory.path().join("stage2");
        let bin = sysroot.join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(sysroot.join("lib")).unwrap();
        std::fs::write(bin.join("targo"), b"#!/bin/sh\n").unwrap();

        // rustlib: a real per-target dir plus installer metadata file siblings.
        let rustlib = sysroot.join("lib").join("rustlib");
        let rustlib_target_lib = rustlib.join("aarch64-apple-darwin").join("lib");
        std::fs::create_dir_all(&rustlib_target_lib).unwrap();
        std::fs::write(rustlib.join("components"), b"aarch64-apple-darwin\n").unwrap();
        std::fs::write(rustlib.join("rust-installer-version"), b"3\n").unwrap();

        // `<stage>-rustc` build-deps root: a real per-target `release/deps`
        // dir plus cargo's own cache-file siblings.
        let rustc_deps_root = directory.path().join("stage2-rustc");
        let target_deps = rustc_deps_root
            .join("aarch64-apple-darwin")
            .join("release")
            .join("deps");
        std::fs::create_dir_all(&target_deps).unwrap();
        std::fs::write(rustc_deps_root.join(".rustc_info.json"), b"{}").unwrap();
        std::fs::write(rustc_deps_root.join("CACHEDIR.TAG"), b"Signature: 1\n").unwrap();

        // Reconstruction must succeed (no plain-directory bail) and surface the
        // real per-target runtime directories while skipping the file siblings.
        let paths = scan_verified_tool_runtime_library_paths(&bin.join("targo"))
            .expect("regular-file siblings must not abort runtime-path reconstruction");
        let canonical_rustlib_lib = rustlib_target_lib.canonicalize().unwrap();
        let canonical_target_deps = target_deps.canonicalize().unwrap();
        assert!(
            paths.contains(&canonical_rustlib_lib),
            "the real per-target rustlib lib dir must be discovered: {paths:?}"
        );
        assert!(
            paths.contains(&canonical_target_deps),
            "the real per-target compiler deps dir must be discovered: {paths:?}"
        );
    }
}
