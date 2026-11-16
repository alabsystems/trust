//! Trust (T14c, DECISION_QUEUE T14-EXPORT-1/2): the nested explicit-unverified
//! authority broker on macOS.
//!
//! The Linux broker (`process_authority.rs`) authenticates a nested Targo by
//! `SO_PEERCRED`, a pidfd, the opened `/proc/<pid>/exe` and `/proc/<pid>/stat`
//! start times over abstract sockets. macOS has none of those handles, so this
//! maps each check onto the kernel handle macOS does have:
//!
//! * **Peer identity:** the socket peer's audit token (`LOCAL_PEERTOKEN`): its
//!   pid and pid version. A pid version never names a later process, so a
//!   check made through the token cannot be answered by a process that reused
//!   the pid.
//! * **Executable identity:** the code-directory hash of the running image,
//!   read through that audit token (`csops_audittoken(CS_OPS_CDHASH)`) and
//!   compared with this process's own. A process with no code directory
//!   cannot be authenticated, and propagation is refused.
//! * **Ancestry and lifetime:** `proc_pidinfo` unique ids (`p_uniqueid`,
//!   `p_puniqueid`), never reused for the life of the system, walked from the
//!   requester up to the root and read again after the exchange.
//! * **Endpoint:** a socket in a fresh `0700` directory under the per-user
//!   temporary directory (`confstr(_CS_DARWIN_USER_TEMP_DIR)`), since macOS has
//!   no abstract namespace. The directory is removed when the root exits. The
//!   path authenticates nothing: a stale or forged one has no live, ancestral,
//!   same-image peer behind it.
//! * **Callback:** the requester binds a one-shot callback socket in its own
//!   fresh directory and names it in the request; it accepts the callback only
//!   from the authenticated root's audit token.
//!
//! As on Linux, this is a process-boundary capability, not an attestation of an
//! uncompromised process image: code already injected into the ancestor Targo
//! acts with its pid, token and code-directory hash.

use std::ffi::{OsStr, OsString};
use std::io::{Read as _, Write as _};
use std::mem::size_of;
use std::os::fd::AsRawFd as _;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::os::unix::fs::{DirBuilderExt as _, MetadataExt as _, PermissionsExt as _};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::Duration;

use anyhow::Context as _;

use crate::CargoResult;

const REQUEST_SCHEMA: &[u8] = b"trust-targo-nested-unverified-request-macos-v1";
const RESPONSE_SCHEMA: &[u8] = b"trust-targo-nested-unverified-response-macos-v1";
const NONCE_BYTES: usize = 16;
/// The longest callback path a request may name. `sun_path` is 104 bytes on
/// macOS, so a longer path could never have been bound.
const MAX_CALLBACK_PATH_BYTES: usize = 104;
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(2);
/// Directory-name prefixes of the broker endpoint and of a requester's
/// one-shot callback. Short, because `sun_path` is.
const BROKER_DIR_PREFIX: &str = "ttb-";
const CALLBACK_DIR_PREFIX: &str = "ttc-";
const BROKER_SOCKET_NAME: &str = "b";
const CALLBACK_SOCKET_NAME: &str = "c";

/// `audit_token_t`: eight words; `audit_token_to_pid` is word 5 and
/// `audit_token_to_pidversion` is word 7 (libbsm).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct AuditToken {
    val: [u32; 8],
}

impl AuditToken {
    fn pid(&self) -> u32 {
        self.val[5]
    }

    fn pid_version(&self) -> u32 {
        self.val[7]
    }
}

/// `struct proc_uniqidentifierinfo` (`<sys/proc_info.h>`), 56 bytes.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
struct ProcUniqIdentifierInfo {
    p_uuid: [u8; 16],
    p_uniqueid: u64,
    p_puniqueid: u64,
    p_idversion: i32,
    p_orig_ppidversion: i32,
    p_reserve2: u64,
    p_reserve3: u64,
}

const PROC_PIDUNIQIDENTIFIERINFO: libc::c_int = 17;
const CS_OPS_CDHASH: libc::c_uint = 5;
const CDHASH_BYTES: usize = 20;

unsafe extern "C" {
    fn csops(
        pid: libc::pid_t,
        ops: libc::c_uint,
        useraddr: *mut libc::c_void,
        usersize: libc::size_t,
    ) -> libc::c_int;
    fn csops_audittoken(
        pid: libc::pid_t,
        ops: libc::c_uint,
        useraddr: *mut libc::c_void,
        usersize: libc::size_t,
        token: *mut AuditToken,
    ) -> libc::c_int;
}

/// One process as `proc_pidinfo` names it: the unique id is never reused, and
/// the parent's unique id ties each ancestry step to one process instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct MacProcess {
    pid: u32,
    parent_pid: u32,
    unique_id: u64,
    parent_unique_id: u64,
    pid_version: i32,
}

fn proc_pidinfo_exact<T>(pid: u32, flavor: libc::c_int, what: &str) -> CargoResult<T> {
    let pid = libc::c_int::try_from(pid).map_err(|_| anyhow::anyhow!("pid does not fit c_int"))?;
    let mut value = std::mem::MaybeUninit::<T>::zeroed();
    let size = libc::c_int::try_from(size_of::<T>())
        .map_err(|_| anyhow::anyhow!("proc_pidinfo buffer does not fit c_int"))?;
    // SAFETY: `value` is a zeroed, correctly sized output buffer for this
    // flavor, and it is read only after the kernel reports filling all of it.
    let written = unsafe { libc::proc_pidinfo(pid, flavor, 0, value.as_mut_ptr().cast(), size) };
    if written != size {
        anyhow::bail!("process pid {pid} has no {what} (it may have exited)");
    }
    // SAFETY: zero-initialized plain-old-data, fully written by the kernel.
    Ok(unsafe { value.assume_init() })
}

impl MacProcess {
    fn read(pid: u32) -> CargoResult<Self> {
        let before = proc_pidinfo_exact::<ProcUniqIdentifierInfo>(
            pid,
            PROC_PIDUNIQIDENTIFIERINFO,
            "unique identity",
        )?;
        let bsd =
            proc_pidinfo_exact::<libc::proc_bsdinfo>(pid, libc::PROC_PIDTBSDINFO, "BSD info")?;
        let after = proc_pidinfo_exact::<ProcUniqIdentifierInfo>(
            pid,
            PROC_PIDUNIQIDENTIFIERINFO,
            "unique identity",
        )?;
        if before.p_uniqueid != after.p_uniqueid
            || before.p_puniqueid != after.p_puniqueid
            || bsd.pbi_pid != pid
        {
            anyhow::bail!(
                "process pid {pid} changed identity during Targo authority authentication"
            );
        }
        Ok(Self {
            pid,
            parent_pid: bsd.pbi_ppid,
            unique_id: after.p_uniqueid,
            parent_unique_id: after.p_puniqueid,
            pid_version: after.p_idversion,
        })
    }

    /// The same process instance, still alive, with the same parent.
    fn ensure_unchanged(&self) -> CargoResult<()> {
        if Self::read(self.pid)? != *self {
            anyhow::bail!(
                "process pid {} exited, was replaced or changed parent during Targo authority authentication",
                self.pid
            );
        }
        Ok(())
    }
}

/// A socket peer bound to one process instance: its audit token, the
/// unique identity whose pid version matches the token, and the code-directory
/// hash read through the token.
#[derive(Debug)]
struct MacPeer {
    token: AuditToken,
    process: MacProcess,
    cdhash: [u8; CDHASH_BYTES],
}

impl MacPeer {
    fn capture(descriptor: libc::c_int) -> CargoResult<Self> {
        let token = socket_peer_token(descriptor)?;
        let process = MacProcess::read(token.pid())?;
        if process.pid_version as u32 != token.pid_version() {
            anyhow::bail!(
                "socket peer pid {} is no longer the process that connected",
                token.pid()
            );
        }
        let cdhash = audit_token_cdhash(&token)?;
        Ok(Self {
            token,
            process,
            cdhash,
        })
    }

    fn ensure_live(&self) -> CargoResult<()> {
        self.process.ensure_unchanged()?;
        if audit_token_cdhash(&self.token)? != self.cdhash {
            anyhow::bail!(
                "process pid {} changed executable during Targo authority authentication",
                self.process.pid
            );
        }
        Ok(())
    }
}

/// This process: its identity and the code-directory hash of its own image.
#[derive(Clone, Copy, Debug)]
pub(super) struct MacSelf {
    process: MacProcess,
    cdhash: [u8; CDHASH_BYTES],
}

impl MacSelf {
    fn capture() -> CargoResult<Self> {
        let process = MacProcess::read(std::process::id())?;
        let mut cdhash = [0_u8; CDHASH_BYTES];
        let pid = libc::pid_t::try_from(process.pid)
            .map_err(|_| anyhow::anyhow!("pid does not fit pid_t"))?;
        // SAFETY: `cdhash` is a writable buffer of exactly the requested size.
        if unsafe { csops(pid, CS_OPS_CDHASH, cdhash.as_mut_ptr().cast(), cdhash.len()) } != 0 {
            return Err(std::io::Error::last_os_error()).context(
                "this Targo has no code directory to authenticate nested-unverified authority with",
            );
        }
        Ok(Self { process, cdhash })
    }
}

fn socket_peer_token(descriptor: libc::c_int) -> CargoResult<AuditToken> {
    let mut token = AuditToken::default();
    let mut length = size_of::<AuditToken>() as libc::socklen_t;
    // SAFETY: `token` is a correctly sized output buffer, read only after the
    // kernel reports the exact initialized length.
    let result = unsafe {
        libc::getsockopt(
            descriptor,
            libc::SOL_LOCAL,
            libc::LOCAL_PEERTOKEN,
            (&mut token as *mut AuditToken).cast(),
            &mut length,
        )
    };
    if result != 0 {
        return Err(std::io::Error::last_os_error())
            .context("failed to read the nested-unverified Targo socket peer's audit token");
    }
    if length as usize != size_of::<AuditToken>() || token.pid() == 0 {
        anyhow::bail!("nested-unverified Targo socket returned a malformed peer audit token");
    }
    Ok(token)
}

fn audit_token_cdhash(token: &AuditToken) -> CargoResult<[u8; CDHASH_BYTES]> {
    let mut cdhash = [0_u8; CDHASH_BYTES];
    let mut token = *token;
    let pid = libc::pid_t::try_from(token.pid())
        .map_err(|_| anyhow::anyhow!("pid does not fit pid_t"))?;
    // SAFETY: `cdhash` is a writable buffer of exactly the requested size, and
    // `token` is a valid audit token the kernel checks against `pid`.
    let result = unsafe {
        csops_audittoken(
            pid,
            CS_OPS_CDHASH,
            cdhash.as_mut_ptr().cast(),
            cdhash.len(),
            &mut token,
        )
    };
    if result != 0 {
        return Err(std::io::Error::last_os_error()).with_context(|| {
            format!(
                "process pid {pid} has no code directory bound to its audit token; nested-unverified Targo authority requires one"
            )
        });
    }
    Ok(cdhash)
}

/// The ancestry chain from `current_pid` up to `root`, each step checked by
/// unique id, so a reused pid anywhere on it is refused. Returns the visited
/// processes so the caller can re-read them after the exchange.
fn ensure_ancestor(root: &MacProcess, current_pid: u32) -> CargoResult<Vec<MacProcess>> {
    if root.pid == current_pid {
        anyhow::bail!("nested-unverified Targo broker is the requester, not an ancestor");
    }
    let not_an_ancestor = || {
        anyhow::anyhow!(
            "nested-unverified Targo broker pid {} is not a live ancestor of pid {current_pid}",
            root.pid
        )
    };
    let mut chain = Vec::new();
    let mut process = MacProcess::read(current_pid)?;
    for _ in 0..4096 {
        // launchd (pid 1) and the kernel are no Targo, and another user's
        // process cannot be read: either ends the walk without the root.
        if process.parent_pid <= 1 {
            break;
        }
        let parent = MacProcess::read(process.parent_pid)
            .map_err(|error| not_an_ancestor().context(error))?;
        if parent.unique_id != process.parent_unique_id {
            anyhow::bail!(
                "the parent of pid {} is no longer the process that started it",
                process.pid
            );
        }
        chain.push(process);
        if parent.pid == root.pid {
            if parent.unique_id != root.unique_id {
                anyhow::bail!(
                    "nested-unverified Targo broker pid {} was reused by another process",
                    root.pid
                );
            }
            return Ok(chain);
        }
        process = parent;
    }
    Err(not_an_ancestor())
}

fn ensure_chain_unchanged(chain: &[MacProcess]) -> CargoResult<()> {
    chain.iter().try_for_each(MacProcess::ensure_unchanged)
}

fn random_nonce() -> CargoResult<[u8; NONCE_BYTES]> {
    let mut nonce = [0_u8; NONCE_BYTES];
    // SAFETY: `nonce` is a writable buffer no longer than getentropy's 256-byte
    // limit.
    if unsafe { libc::getentropy(nonce.as_mut_ptr().cast(), nonce.len()) } != 0 {
        return Err(std::io::Error::last_os_error()).context("failed to read kernel randomness");
    }
    Ok(nonce)
}

/// The per-user temporary directory macOS gives this user (`/var/folders/…/T`).
fn user_temp_dir() -> CargoResult<PathBuf> {
    let mut buffer = vec![0_u8; libc::PATH_MAX as usize];
    // SAFETY: `buffer` is writable for its full length, which is passed.
    let length = unsafe {
        libc::confstr(
            libc::_CS_DARWIN_USER_TEMP_DIR,
            buffer.as_mut_ptr().cast(),
            buffer.len(),
        )
    };
    if length == 0 || length > buffer.len() {
        return Err(std::io::Error::last_os_error())
            .context("failed to find the per-user temporary directory");
    }
    buffer.truncate(length - 1);
    let directory = PathBuf::from(OsString::from_vec(buffer));
    if !directory.is_absolute() {
        anyhow::bail!("the per-user temporary directory is not absolute");
    }
    Ok(directory)
}

/// A fresh `0700` directory this user owns, created (never reused) under the
/// per-user temporary directory, removed with its socket on drop.
#[derive(Debug)]
struct PrivateSocketDir {
    directory: PathBuf,
    socket: PathBuf,
}

impl PrivateSocketDir {
    fn create(prefix: &str, socket_name: &str) -> CargoResult<Self> {
        let parent = user_temp_dir()?;
        sweep_dead_socket_dirs(&parent);
        let suffix = hex::encode(&random_nonce()?[..8]);
        let directory = parent.join(format!("{prefix}{}-{suffix}", std::process::id()));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .with_context(|| format!("failed to create `{}`", directory.display()))?;
        let created = Self {
            socket: directory.join(socket_name),
            directory,
        };
        ensure_private_directory(&created.directory)?;
        Ok(created)
    }
}

impl Drop for PrivateSocketDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.socket);
        let _ = std::fs::remove_dir(&self.directory);
    }
}

/// Remove the endpoint and callback directories of this user's processes
/// that are gone. A root ended by a signal (a `targo run` target's SIGTERM is
/// re-raised) or killed outright never runs its exit cleanup; its directory
/// authenticates nothing, and the next one to start removes it. Best effort,
/// and only a private directory whose embedded pid names no live process.
fn sweep_dead_socket_dirs(parent: &Path) {
    let Ok(entries) = std::fs::read_dir(parent) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        let Some((rest, socket)) = name
            .strip_prefix(BROKER_DIR_PREFIX)
            .map(|rest| (rest, BROKER_SOCKET_NAME))
            .or_else(|| {
                name.strip_prefix(CALLBACK_DIR_PREFIX)
                    .map(|rest| (rest, CALLBACK_SOCKET_NAME))
            })
        else {
            continue;
        };
        let Some(pid) = rest
            .split_once('-')
            .and_then(|(pid, _)| pid.parse::<libc::pid_t>().ok())
            .filter(|pid| *pid > 0)
        else {
            continue;
        };
        // SAFETY: signal 0 only asks whether `pid` exists.
        let gone = unsafe { libc::kill(pid, 0) } != 0
            && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH);
        let directory = entry.path();
        if gone && ensure_private_directory(&directory).is_ok() {
            let _ = std::fs::remove_file(directory.join(socket));
            let _ = std::fs::remove_dir(&directory);
        }
    }
}

/// A directory this user owns, no symlink, mode exactly `0700`.
fn ensure_private_directory(directory: &Path) -> CargoResult<()> {
    let metadata = std::fs::symlink_metadata(directory)
        .with_context(|| format!("failed to inspect `{}`", directory.display()))?;
    // SAFETY: geteuid takes no arguments and cannot fail.
    let euid = unsafe { libc::geteuid() };
    if !metadata.is_dir()
        || metadata.uid() != euid
        || metadata.permissions().mode() & 0o7777 != 0o700
    {
        anyhow::bail!(
            "`{}` is not a private directory of this user (mode 0700)",
            directory.display()
        );
    }
    Ok(())
}

/// A callback path a broker may connect to: a socket named
/// `CALLBACK_SOCKET_NAME` directly inside a private `CALLBACK_DIR_PREFIX`
/// directory of this user, under the per-user temporary directory.
fn validate_callback_path(path: &Path) -> CargoResult<()> {
    let directory = path
        .parent()
        .filter(|_| path.file_name() == Some(OsStr::new(CALLBACK_SOCKET_NAME)))
        .ok_or_else(|| anyhow::anyhow!("nested-unverified Targo callback path is malformed"))?;
    if directory.parent() != Some(user_temp_dir()?.as_path())
        || !directory
            .file_name()
            .and_then(OsStr::to_str)
            .is_some_and(|name| name.starts_with(CALLBACK_DIR_PREFIX))
    {
        anyhow::bail!("nested-unverified Targo callback is outside a private callback directory");
    }
    ensure_private_directory(directory)
}

fn configure_stream(stream: &UnixStream) -> CargoResult<()> {
    for (result, direction) in [
        (stream.set_read_timeout(Some(HANDSHAKE_TIMEOUT)), "reads"),
        (stream.set_write_timeout(Some(HANDSHAKE_TIMEOUT)), "writes"),
    ] {
        match result {
            Ok(()) => {}
            // macOS refuses socket options (EINVAL) once both directions of
            // the socket are shut, which is how an accepted callback looks when
            // its peer already wrote and closed: reads then return the buffered
            // bytes and EOF without blocking, so there is nothing to bound.
            Err(error) if error.raw_os_error() == Some(libc::EINVAL) => {}
            Err(error) => {
                return Err(error).with_context(|| {
                    format!("failed to bound nested-unverified Targo broker {direction}")
                });
            }
        }
    }
    Ok(())
}

fn request_frame(
    requester: u32,
    nonce: &[u8; NONCE_BYTES],
    callback: &Path,
) -> CargoResult<Vec<u8>> {
    let callback = callback.as_os_str().as_bytes();
    let length = u16::try_from(callback.len())
        .ok()
        .filter(|length| usize::from(*length) <= MAX_CALLBACK_PATH_BYTES)
        .ok_or_else(|| anyhow::anyhow!("nested-unverified Targo callback path is too long"))?;
    let mut frame = Vec::with_capacity(REQUEST_SCHEMA.len() + 4 + NONCE_BYTES + 2 + callback.len());
    frame.extend_from_slice(REQUEST_SCHEMA);
    frame.extend_from_slice(&requester.to_be_bytes());
    frame.extend_from_slice(nonce);
    frame.extend_from_slice(&length.to_be_bytes());
    frame.extend_from_slice(callback);
    Ok(frame)
}

fn parse_request(frame: &[u8]) -> CargoResult<(u32, [u8; NONCE_BYTES], PathBuf)> {
    let fixed = REQUEST_SCHEMA.len() + 4 + NONCE_BYTES + 2;
    if frame.len() < fixed || !frame.starts_with(REQUEST_SCHEMA) {
        anyhow::bail!("nested-unverified Targo request has an invalid schema or width");
    }
    let mut offset = REQUEST_SCHEMA.len();
    let requester = u32::from_be_bytes(frame[offset..offset + 4].try_into().expect("width"));
    offset += 4;
    let nonce: [u8; NONCE_BYTES] = frame[offset..offset + NONCE_BYTES]
        .try_into()
        .expect("width");
    offset += NONCE_BYTES;
    let length = usize::from(u16::from_be_bytes(
        frame[offset..offset + 2].try_into().expect("width"),
    ));
    offset += 2;
    if length > MAX_CALLBACK_PATH_BYTES || frame.len() != offset + length {
        anyhow::bail!("nested-unverified Targo request has an invalid callback width");
    }
    let callback = PathBuf::from(OsStr::from_bytes(&frame[offset..]));
    Ok((requester, nonce, callback))
}

fn response_frame(root: u32, requester: u32, nonce: &[u8; NONCE_BYTES]) -> Vec<u8> {
    let mut frame = Vec::with_capacity(RESPONSE_SCHEMA.len() + 8 + NONCE_BYTES);
    frame.extend_from_slice(RESPONSE_SCHEMA);
    frame.extend_from_slice(&root.to_be_bytes());
    frame.extend_from_slice(&requester.to_be_bytes());
    frame.extend_from_slice(nonce);
    frame
}

fn parse_response(frame: &[u8]) -> CargoResult<(u32, u32, [u8; NONCE_BYTES])> {
    if frame.len() != RESPONSE_SCHEMA.len() + 8 + NONCE_BYTES || !frame.starts_with(RESPONSE_SCHEMA)
    {
        anyhow::bail!("nested-unverified Targo response has an invalid schema or width");
    }
    let offset = RESPONSE_SCHEMA.len();
    let root = u32::from_be_bytes(frame[offset..offset + 4].try_into().expect("width"));
    let requester = u32::from_be_bytes(frame[offset + 4..offset + 8].try_into().expect("width"));
    let nonce = frame[offset + 8..].try_into().expect("width");
    Ok((root, requester, nonce))
}

/// Read one frame of at most `max_len` bytes, up to the peer's write shutdown.
fn receive_frame(stream: &mut UnixStream, max_len: usize, direction: &str) -> CargoResult<Vec<u8>> {
    let mut frame = Vec::with_capacity(max_len + 1);
    stream
        .take((max_len + 1) as u64)
        .read_to_end(&mut frame)
        .with_context(|| format!("failed to read nested-unverified Targo broker {direction}"))?;
    if frame.len() > max_len {
        anyhow::bail!("nested-unverified Targo broker {direction} is too long");
    }
    Ok(frame)
}

/// Wait for the root's callback, or for the broker to end the exchange
/// without one. The broker never writes on the request connection: it only
/// lets go of it, and it connects the callback first, so a request connection
/// that has ended with no callback queued was refused. That ends the wait at
/// once, rather than at the handshake bound (a requester of another build, or
/// one that is not a descendant of the root, learns it immediately).
fn wait_for_callback(listener: &UnixListener, request: &UnixStream) -> CargoResult<()> {
    let deadline = std::time::Instant::now() + HANDSHAKE_TIMEOUT;
    loop {
        let remaining = deadline.saturating_duration_since(std::time::Instant::now());
        if remaining.is_zero() {
            anyhow::bail!("timed out waiting for nested-unverified Targo callback");
        }
        let mut descriptors = [
            libc::pollfd {
                fd: listener.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: request.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        // SAFETY: two initialized pollfds for the duration of the bounded poll.
        let result = unsafe {
            libc::poll(
                descriptors.as_mut_ptr(),
                descriptors.len() as libc::nfds_t,
                remaining.as_millis().clamp(1, i32::MAX as u128) as libc::c_int,
            )
        };
        if result < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error).context("failed to wait for nested-unverified Targo callback");
        }
        let [callback, request] = descriptors;
        if callback.revents & libc::POLLIN != 0 {
            return Ok(());
        }
        if callback.revents != 0 {
            anyhow::bail!(
                "nested-unverified Targo callback listener failed with poll events {:#x}",
                callback.revents
            );
        }
        if request.revents != 0 {
            // The callback, had there been one, was queued before the request
            // ended; look once more without waiting.
            let mut callback = libc::pollfd {
                fd: listener.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            // SAFETY: one initialized pollfd, polled without waiting.
            if unsafe { libc::poll(&mut callback, 1, 0) } == 1
                && callback.revents & libc::POLLIN != 0
            {
                return Ok(());
            }
            anyhow::bail!(
                "the nested-unverified Targo broker refused this process: it ended the exchange \
                 without a callback (another Targo build, or not a descendant of its root)"
            );
        }
    }
}

/// The broker endpoint's directory, removed when this (root) process exits.
static BROKER_DIR: OnceLock<PrivateSocketDir> = OnceLock::new();

extern "C" fn remove_broker_dir_at_exit() {
    if let Some(directory) = BROKER_DIR.get() {
        let _ = std::fs::remove_file(&directory.socket);
        let _ = std::fs::remove_dir(&directory.directory);
    }
}

/// The live authority service of an exact `ExplicitUnverified` root.
#[derive(Debug)]
pub(super) struct NestedUnverifiedTargoBroker {
    pub(super) endpoint: OsString,
    _thread: std::thread::JoinHandle<()>,
}

impl NestedUnverifiedTargoBroker {
    pub(super) fn start() -> CargoResult<Self> {
        let root = MacSelf::capture()?;
        let directory = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME)?;
        let listener = UnixListener::bind(&directory.socket)
            .context("failed to bind nested-unverified Targo broker")?;
        let endpoint = directory.socket.clone().into_os_string();
        if BROKER_DIR.set(directory).is_err() {
            anyhow::bail!("explicit-unverified Targo broker was initialized more than once");
        }
        // SAFETY: registers a plain `extern "C"` function with no arguments.
        if unsafe { libc::atexit(remove_broker_dir_at_exit) } != 0 {
            tracing::debug!("could not register nested-unverified broker cleanup at exit");
        }
        let thread = std::thread::Builder::new()
            .name("targo-unverified-authority".to_owned())
            .spawn(move || serve(listener, root))
            .context("failed to start nested-unverified Targo broker")?;
        Ok(Self {
            endpoint,
            _thread: thread,
        })
    }
}

fn serve(listener: UnixListener, root: MacSelf) {
    for connection in listener.incoming() {
        let Ok(mut connection) = connection else {
            break;
        };
        // Each request on its own thread: a request holds its callback open
        // until the requester has read this root's token, so serving them in
        // turn would queue concurrent `$CARGO` invocations (build scripts and
        // tests run in parallel) behind each other's handshake bound. A
        // request that gets no thread is dropped, which its requester reads as
        // a refusal at once.
        let spawned = std::thread::Builder::new()
            .name("targo-unverified-request".to_owned())
            .spawn(move || {
                if let Err(error) = handle_request(&mut connection, &root) {
                    tracing::debug!("rejected nested-unverified Targo broker request: {error:#}");
                }
            });
        if let Err(error) = spawned {
            tracing::debug!("could not serve a nested-unverified Targo broker request: {error}");
        }
    }
}

fn handle_request(connection: &mut UnixStream, root: &MacSelf) -> CargoResult<()> {
    configure_stream(connection)?;
    // Bind the peer to one process instance and its image before reading any
    // byte it controls.
    let peer = MacPeer::capture(connection.as_raw_fd())?;
    let request = receive_frame(
        connection,
        REQUEST_SCHEMA.len() + 4 + NONCE_BYTES + 2 + MAX_CALLBACK_PATH_BYTES,
        "request",
    )?;
    let (requester, nonce, callback) = parse_request(&request)?;
    if requester != peer.process.pid {
        anyhow::bail!(
            "nested-unverified Targo request names pid {requester}, but the kernel peer is pid {}",
            peer.process.pid
        );
    }
    if peer.cdhash != root.cdhash {
        anyhow::bail!(
            "nested-unverified Targo process pid {requester} does not run this Targo's image"
        );
    }
    let chain = ensure_ancestor(&root.process, requester)?;
    peer.ensure_live()?;
    validate_callback_path(&callback)?;

    let mut stream = UnixStream::connect(&callback)
        .context("failed to connect nested-unverified Targo one-shot callback")?;
    configure_stream(&stream)?;
    stream
        .write_all(&response_frame(root.process.pid, requester, &nonce))
        .context("failed to write nested-unverified Targo callback response")?;
    stream
        .shutdown(std::net::Shutdown::Write)
        .context("failed to frame nested-unverified Targo callback response")?;
    // Hold the callback open until the requester closes it: macOS answers
    // `LOCAL_PEERTOKEN` only while the connection lives, and the requester
    // reads this process's audit token from it.
    wait_for_close(&mut stream);
    peer.ensure_live()?;
    root.process.ensure_unchanged()?;
    ensure_chain_unchanged(&chain)?;
    Ok(())
}

/// Read until the peer closes, the handshake timeout ends, or a byte arrives.
fn wait_for_close(stream: &mut UnixStream) {
    let mut byte = [0_u8; 1];
    let _ = stream.read(&mut byte);
}

/// Authenticate inherited explicit-unverified authority: a live, ancestral
/// Targo running this image must answer on a fresh callback.
pub(super) fn authenticate_nested_unverified_targo_broker(endpoint: &OsStr) -> CargoResult<()> {
    let endpoint = Path::new(endpoint);
    if !endpoint.is_absolute() {
        anyhow::bail!("nested-unverified Targo broker endpoint is not an absolute socket path");
    }
    let current = MacSelf::capture()?;
    let nonce = random_nonce()?;
    let callback = PrivateSocketDir::create(CALLBACK_DIR_PREFIX, CALLBACK_SOCKET_NAME)?;
    let callback_listener = UnixListener::bind(&callback.socket)
        .context("failed to bind nested-unverified Targo one-shot callback")?;

    let mut connection = UnixStream::connect(endpoint).with_context(|| {
        format!(
            "failed to connect to nested-unverified Targo broker `{}`",
            endpoint.display()
        )
    })?;
    configure_stream(&connection)?;
    connection
        .write_all(&request_frame(
            current.process.pid,
            &nonce,
            &callback.socket,
        )?)
        .context("failed to write nested-unverified Targo broker request")?;
    connection
        .shutdown(std::net::Shutdown::Write)
        .context("failed to frame nested-unverified Targo broker request")?;

    wait_for_callback(&callback_listener, &connection)?;
    let (mut reply, _) = callback_listener
        .accept()
        .context("failed to accept nested-unverified Targo one-shot callback")?;
    configure_stream(&reply)?;
    // As on the broker side, bind the callback peer to one process instance
    // and its image before reading any byte it controls.
    let root = MacPeer::capture(reply.as_raw_fd())?;
    let response = receive_frame(
        &mut reply,
        RESPONSE_SCHEMA.len() + 8 + NONCE_BYTES,
        "response",
    )?;
    // Release the root, which holds the callback open for the token read.
    drop(reply);
    let (response_root, response_requester, response_nonce) = parse_response(&response)?;
    if response_requester != current.process.pid {
        anyhow::bail!(
            "nested-unverified Targo broker response is bound to requester {response_requester}, expected {}",
            current.process.pid
        );
    }
    if response_root != root.process.pid {
        anyhow::bail!(
            "nested-unverified Targo callback names root pid {response_root}, but its live callback peer is pid {}",
            root.process.pid
        );
    }
    if response_nonce != nonce {
        anyhow::bail!("nested-unverified Targo callback returned the wrong one-shot challenge");
    }
    if root.cdhash != current.cdhash {
        anyhow::bail!(
            "nested-unverified Targo callback peer pid {response_root} does not run this Targo's image"
        );
    }
    let chain = ensure_ancestor(&root.process, current.process.pid)?;
    current.process.ensure_unchanged()?;
    root.ensure_live()?;
    ensure_chain_unchanged(&chain)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn this_process_has_a_unique_identity_and_a_code_directory() {
        let me = MacSelf::capture().expect("a linker-signed test binary has a code directory");
        assert_eq!(me.process.pid, std::process::id());
        assert_ne!(me.process.unique_id, 0);
        assert_ne!(me.cdhash, [0_u8; CDHASH_BYTES]);
        // SAFETY: getppid takes no arguments and cannot fail.
        assert_eq!(me.process.parent_pid, unsafe { libc::getppid() } as u32);
        let parent = MacProcess::read(me.process.parent_pid).unwrap();
        assert_eq!(parent.unique_id, me.process.parent_unique_id);
        me.process.ensure_unchanged().unwrap();
    }

    #[test]
    fn a_socket_peer_is_bound_to_its_audit_token_and_image() {
        let (left, right) = UnixStream::pair().unwrap();
        let peer = MacPeer::capture(left.as_raw_fd()).unwrap();
        let me = MacSelf::capture().unwrap();
        assert_eq!(peer.process, me.process);
        assert_eq!(peer.cdhash, me.cdhash);
        assert_eq!(peer.token.pid(), std::process::id());
        peer.ensure_live().unwrap();
        drop(right);
    }

    #[test]
    fn ancestry_is_walked_by_unique_id_and_refuses_a_non_ancestor() {
        let me = MacProcess::read(std::process::id()).unwrap();
        let parent = MacProcess::read(me.parent_pid).unwrap();
        let chain = ensure_ancestor(&parent, me.pid).unwrap();
        assert_eq!(chain, [me]);
        // The requester is never its own ancestor.
        assert!(ensure_ancestor(&me, me.pid).is_err());
        // A live process that is not an ancestor: a child of this process.
        let mut child = std::process::Command::new("/bin/sleep")
            .arg("5")
            .spawn()
            .unwrap();
        let child_process = MacProcess::read(child.id()).unwrap();
        let error = ensure_ancestor(&child_process, me.pid).unwrap_err();
        assert!(
            error.to_string().contains("not a live ancestor"),
            "{error:#}"
        );
        // A root whose pid now names another process (a reused pid).
        let reused = MacProcess {
            unique_id: parent.unique_id.wrapping_add(1),
            ..parent
        };
        let error = ensure_ancestor(&reused, me.pid).unwrap_err();
        assert!(error.to_string().contains("reused"), "{error:#}");
        let _ = child.kill();
        let _ = child.wait();
    }

    #[test]
    fn private_socket_directories_are_fresh_owned_and_removed() {
        let directory =
            PrivateSocketDir::create(CALLBACK_DIR_PREFIX, CALLBACK_SOCKET_NAME).unwrap();
        ensure_private_directory(&directory.directory).unwrap();
        validate_callback_path(&directory.socket).unwrap();
        let listener = UnixListener::bind(&directory.socket).unwrap();
        let path = directory.directory.clone();
        drop(listener);
        drop(directory);
        assert!(!path.exists(), "the private directory outlived its owner");

        // A callback outside a private callback directory is refused.
        assert!(validate_callback_path(Path::new("/tmp/c")).is_err());
        let broker = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        assert!(validate_callback_path(&broker.directory.join(CALLBACK_SOCKET_NAME)).is_err());
        // A directory another mode makes public is not private.
        std::fs::set_permissions(&broker.directory, std::fs::Permissions::from_mode(0o755))
            .unwrap();
        assert!(ensure_private_directory(&broker.directory).is_err());
    }

    #[test]
    fn a_dead_roots_directory_is_swept_by_the_next_one() {
        let parent = user_temp_dir().unwrap();
        // A pid that names no live process: a reaped child's.
        let mut child = std::process::Command::new("/usr/bin/true").spawn().unwrap();
        let dead = child.id();
        child.wait().unwrap();
        let stale = parent.join(format!("{BROKER_DIR_PREFIX}{dead}-0011223344556677"));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&stale)
            .unwrap();
        drop(UnixListener::bind(stale.join(BROKER_SOCKET_NAME)).unwrap());
        // A live one (this process) is kept.
        let live = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        sweep_dead_socket_dirs(&parent);
        assert!(!stale.exists(), "a dead root's directory was left");
        assert!(live.directory.exists(), "a live root's directory was swept");
    }

    #[test]
    fn frames_round_trip_and_refuse_malformed_widths() {
        let nonce = [7_u8; NONCE_BYTES];
        let callback = Path::new("/var/folders/x/T/ttc-1-0011223344556677/c");
        let frame = request_frame(42, &nonce, callback).unwrap();
        assert_eq!(
            parse_request(&frame).unwrap(),
            (42, nonce, callback.to_path_buf())
        );
        assert!(parse_request(&frame[..frame.len() - 1]).is_err());
        let mut extended = frame.clone();
        extended.push(b'x');
        assert!(parse_request(&extended).is_err());
        assert!(request_frame(1, &nonce, &PathBuf::from("/".repeat(200))).is_err());

        let response = response_frame(1, 2, &nonce);
        assert_eq!(parse_response(&response).unwrap(), (1, 2, nonce));
        assert!(parse_response(&response[1..]).is_err());
    }

    const CHILD_ENDPOINT_ENV: &str = "TARGO_TEST_MACOS_BROKER_ENDPOINT";

    /// The positive control: children running this image authenticate the
    /// broker this process started, end to end (request, peer token and image
    /// check, ancestry, callback, response, and the re-reads after it). Four
    /// at once: each request is served on its own thread, so one requester's
    /// held callback never holds up another.
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the descendant must use the actual inherited broker endpoint rather than a Cargo configuration overlay"
    )]
    fn a_descendant_running_this_image_authenticates_through_the_broker() {
        if let Some(endpoint) = std::env::var_os(CHILD_ENDPOINT_ENV) {
            authenticate_nested_unverified_targo_broker(&endpoint)
                .expect("a child of the root, running its image, authenticates");
            return;
        }
        let broker = NestedUnverifiedTargoBroker::start().expect("start the root broker");
        let children = (0..4)
            .map(|_| {
                std::process::Command::new(std::env::current_exe().unwrap())
                    .args([
                        "--exact",
                        "util::process_authority::macos_broker::tests::a_descendant_running_this_image_authenticates_through_the_broker",
                        "--nocapture",
                        "--test-threads=1",
                    ])
                    .env(CHILD_ENDPOINT_ENV, &broker.endpoint)
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::piped())
                    .spawn()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        for child in children {
            let output = child.wait_with_output().unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(output.status.success(), "{stdout}\n{stderr}");
            assert!(
                stdout.contains("1 passed"),
                "the child ran no authentication: {stdout}"
            );
        }
    }

    /// A requester running another image (here `/usr/bin/nc`, which sends a
    /// well-formed request naming its own pid) is refused by its
    /// code-directory hash, before any callback.
    #[test]
    fn a_requester_running_another_image_is_refused() {
        let root = MacSelf::capture().unwrap();
        let endpoint = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        let listener = UnixListener::bind(&endpoint.socket).unwrap();
        let mut requester = std::process::Command::new("/usr/bin/nc")
            .arg("-U")
            .arg(&endpoint.socket)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::null())
            .spawn()
            .expect("spawn /usr/bin/nc as a foreign requester");
        let callback = Path::new("/nonexistent/ttc-0-0000000000000000/c");
        let frame = request_frame(requester.id(), &[1_u8; NONCE_BYTES], callback).unwrap();
        requester.stdin.take().unwrap().write_all(&frame).unwrap();
        let (mut connection, _) = listener.accept().unwrap();
        let error = handle_request(&mut connection, &root).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("does not run this Targo's image"),
            "{error:#}"
        );
        let _ = requester.kill();
        let _ = requester.wait();
    }

    /// A broker that ends the exchange without a callback (what a real root
    /// does for a requester of another build, or one that is not its
    /// descendant) is read as a refusal at once, never as a wait for the
    /// handshake bound.
    #[test]
    fn a_refusal_ends_the_wait_without_the_handshake_bound() {
        let endpoint = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        let listener = UnixListener::bind(&endpoint.socket).unwrap();
        let broker = std::thread::spawn(move || {
            let (mut connection, _) = listener.accept().unwrap();
            let request = receive_frame(&mut connection, 512, "request").unwrap();
            parse_request(&request).unwrap();
            // Refuse: let go of the request with no callback.
        });
        let error =
            authenticate_nested_unverified_targo_broker(endpoint.socket.as_os_str()).unwrap_err();
        assert!(
            format!("{error:#}").contains("refused this process"),
            "{error:#}"
        );
        broker.join().unwrap();
    }

    /// A stale endpoint (no live listener) and a forged one (served by a
    /// process that is not an ancestor running this image) authenticate
    /// nothing.
    #[test]
    fn stale_and_forged_endpoints_authenticate_nothing() {
        let stale = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        drop(UnixListener::bind(&stale.socket).unwrap());
        let error =
            authenticate_nested_unverified_targo_broker(stale.socket.as_os_str()).unwrap_err();
        assert!(
            format!("{error:#}").contains("failed to connect"),
            "{error:#}"
        );

        // This process serves the endpoint and answers every callback
        // faithfully, but it is the requester itself, never its own ancestor.
        let forged = PrivateSocketDir::create(BROKER_DIR_PREFIX, BROKER_SOCKET_NAME).unwrap();
        let listener = UnixListener::bind(&forged.socket).unwrap();
        let server = std::thread::spawn(move || {
            let (mut connection, _) = listener.accept().unwrap();
            let request = receive_frame(&mut connection, 512, "request").unwrap();
            let (requester, nonce, callback) = parse_request(&request).unwrap();
            let mut reply = UnixStream::connect(callback).unwrap();
            reply
                .write_all(&response_frame(std::process::id(), requester, &nonce))
                .unwrap();
            reply.shutdown(std::net::Shutdown::Write).unwrap();
            wait_for_close(&mut reply);
        });
        let error =
            authenticate_nested_unverified_targo_broker(forged.socket.as_os_str()).unwrap_err();
        assert!(
            format!("{error:#}").contains("is the requester, not an ancestor"),
            "{error:#}"
        );
        server.join().unwrap();
        assert!(authenticate_nested_unverified_targo_broker(OsStr::new("relative")).is_err());
    }
}
