//! Owned transport for a compiling child retained across frontend qualification.
//!
//! An endpoint directs the existing authority validator; it supplies no proof,
//! CPU grant, or reconstructed scheduler. Callers must authenticate the frontend,
//! require the original private CLI route, and exclude stdin fix/proxy/control
//! modes before capture. A saved frame cannot recreate an endpoint owner.

use std::fmt;
use std::io::{self, Write};
use std::net::Shutdown;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::{PreparedTestsReceipt, RECEIPT_SCHEMA};

mod transport;
use transport::Channel;

pub const RETAINED_SESSION_ARG: &str = "--__retained-test-session";
const VERSION: u32 = 1;
const MAX_FRAME_BYTES: usize = 16 * 1024;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Frame {
    version: u32,
    message: Message,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum Message {
    Init {
        session: String,
        connection: String,
        roles: [OutputRole; 2],
        expires_monotonic_ns: u64,
    },
    CompileReady {
        session: String,
        connection: String,
        receipt: PreparedTestsReceipt,
    },
    CompileFailed {
        session: String,
        connection: String,
        diagnostic: String,
    },
    Grant {
        session: String,
        connection: String,
        receipt: PreparedTestsReceipt,
        authority_path: PathBuf,
        authority_sha256: String,
    },
    DrainComplete {
        session: String,
        connection: String,
        receipt: PreparedTestsReceipt,
    },
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum OutputRole {
    RuntimeStdout,
    RuntimeStderr,
}

/// Untrusted runtime streams. They never enter compiler evidence parsing.
pub struct RuntimeOutput {
    pub stdout: UnixStream,
    pub stderr: UnixStream,
}

/// The original controller endpoint, tied to the child this owner spawned.
/// This type is deliberately neither Clone nor Deserialize.
pub struct SessionOwner {
    channel: Channel,
    session: String,
    connection: String,
    child_id: u32,
    ready: Option<CompileReady>,
}

/// One finite compile checkpoint, not a child exit or proof qualification.
#[derive(Debug)]
pub struct CompileReady {
    receipt: Option<PreparedTestsReceipt>,
    failure: Option<String>,
}

impl CompileReady {
    pub fn receipt(&self) -> Option<&PreparedTestsReceipt> {
        self.receipt.as_ref()
    }
    pub fn failure(&self) -> Option<&str> {
        self.failure.as_deref()
    }
    pub fn is_success(&self) -> bool {
        self.receipt.is_some()
    }
}

/// Retain through actual child reaping. Dropping it closes the controller.
pub struct GrantedSession {
    channel: Channel,
    child_id: u32,
    session: String,
    connection: String,
    receipt: PreparedTestsReceipt,
    drained: bool,
}

impl GrantedSession {
    pub fn child_id(&self) -> u32 {
        self.child_id
    }

    /// Observe the original queue's one-use drained event, including after the
    /// child becomes waitable. EOF before that event refuses; EOF afterwards
    /// permits teardown but is never an exit status. Extra bytes always refuse.
    pub fn check_connected(&mut self, deadline: Instant) -> io::Result<()> {
        self.channel.limit_deadline(deadline);
        if !self.drained {
            let Some((message, rights)) = self.channel.poll(false)? else { return Ok(()) };
            debug_assert!(rights.is_empty());
            match message {
                Message::DrainComplete { session, connection, receipt }
                    if session == self.session
                        && connection == self.connection
                        && same_receipt(&receipt, &self.receipt) =>
                {
                    self.drained = true;
                }
                _ => return self.channel.reject("invalid retained queue-drained event"),
            }
        }
        self.channel.ensure_finished()
    }

    /// Queue-drained is neither successful execution nor an observed child exit.
    /// A caller accepting exit0 must require this and still reap the actual child.
    pub fn drained(&self) -> bool {
        self.drained
    }
}

impl SessionOwner {
    /// Spawn the actual configured compiler child with one original endpoint.
    /// Existing stdout/stderr and process-group configuration are preserved.
    /// The same absolute deadline bounds startup, readiness and granting.
    pub fn spawn(
        command: &mut Command,
        session: &str,
        deadline: Instant,
    ) -> io::Result<(Child, Self, RuntimeOutput)> {
        validate_session(session)?;
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).map_err(|error| {
            io::Error::other(format!("retained connection randomness failed: {error}"))
        })?;
        let connection: String = nonce.iter().map(|byte| format!("{byte:02x}")).collect();
        if command
            .get_args()
            .take_while(|arg| *arg != "--")
            .any(|arg| arg == "--__resource-root-control")
        {
            return Err(invalid("retained test sessions cannot share root-control stdin"));
        }
        let (controller, child_control) = UnixStream::pair()?;
        let (stdout, child_stdout) = UnixStream::pair()?;
        let (stderr, child_stderr) = UnixStream::pair()?;
        for stream in [&controller, &child_control, &stdout, &child_stdout, &stderr, &child_stderr]
        {
            transport::cloexec(stream.as_raw_fd())?;
        }
        let mut channel = Channel::new(controller, deadline)?;
        channel.send(
            Message::Init {
                session: session.into(),
                connection: connection.clone(),
                roles: [OutputRole::RuntimeStdout, OutputRole::RuntimeStderr],
                expires_monotonic_ns: transport::monotonic_expiry(deadline)?,
            },
            &[child_stdout.as_raw_fd(), child_stderr.as_raw_fd()],
        )?;
        // The queued SCM_RIGHTS message now owns its copies. No command or
        // controller keeps an additional runtime writer that could hide EOF.
        drop(child_stdout);
        drop(child_stderr);
        command.stdin(Stdio::from(OwnedFd::from(child_control)));
        let spawned = command.spawn();
        // Command::spawn borrows its configured stdin. Retire that parent copy
        // on both outcomes, so command reuse cannot duplicate this conversation.
        command.stdin(Stdio::null());
        // No fallible operation may follow a successful spawn: the actual
        // Child must always return to the caller's lifecycle guard.
        let child = spawned?;
        let owner = Self {
            channel,
            session: session.into(),
            connection,
            child_id: child.id(),
            ready: None,
        };
        Ok((child, owner, RuntimeOutput { stdout, stderr }))
    }

    pub fn child_id(&self) -> u32 {
        self.child_id
    }

    /// Nonblocking polling lets the caller retain its actual process guard.
    /// Readiness authenticates no favorable proof result.
    pub fn poll_ready(&mut self, deadline: Instant) -> io::Result<Option<&CompileReady>> {
        self.channel.limit_deadline(deadline);
        if self.ready.is_some() {
            if self.ready.as_ref().is_some_and(CompileReady::is_success) {
                self.channel.ensure_quiet()?;
            }
            return Ok(self.ready.as_ref());
        }
        let Some((message, rights)) = self.channel.poll(false)? else { return Ok(None) };
        debug_assert!(rights.is_empty());
        match message {
            Message::CompileReady { session, connection, receipt }
                if session == self.session
                    && connection == self.connection
                    && validate_receipt(&receipt, &self.session).is_ok() =>
            {
                self.channel.ensure_quiet()?;
                self.ready = Some(CompileReady { receipt: Some(receipt), failure: None });
            }
            Message::CompileFailed { session, connection, diagnostic }
                if session == self.session
                    && connection == self.connection
                    && !diagnostic.is_empty()
                    && diagnostic.len() <= 4096 =>
            {
                self.ready = Some(CompileReady { receipt: None, failure: Some(diagnostic) });
            }
            _ => {
                return self
                    .channel
                    .reject("compile checkpoint does not match the retained session");
            }
        }
        Ok(self.ready.as_ref())
    }

    /// Consume this endpoint once, only from the frontend's current sealed
    /// qualification path. The frame itself does not authorize execution.
    pub fn grant(
        mut self,
        authority_path: &Path,
        authority_sha256: &str,
        deadline: Instant,
    ) -> io::Result<GrantedSession> {
        self.channel.limit_deadline(deadline);
        validate_path(authority_path)?;
        validate_digest(authority_sha256)?;
        let receipt = self
            .ready
            .take()
            .and_then(|ready| ready.receipt)
            .ok_or_else(|| invalid("successful compile-ready has not been observed"))?;
        self.channel.ensure_quiet()?;
        self.channel.send(
            Message::Grant {
                session: self.session.clone(),
                connection: self.connection.clone(),
                receipt: receipt.clone(),
                authority_path: authority_path.into(),
                authority_sha256: authority_sha256.into(),
            },
            &[],
        )?;
        Ok(GrantedSession {
            channel: self.channel,
            child_id: self.child_id,
            session: self.session,
            connection: self.connection,
            receipt,
            drained: false,
        })
    }
}

/// A captured original child endpoint. Install only after native verified-lane
/// authentication; receiving Init is not execution authority.
pub struct RetainedChild {
    channel: Channel,
    session: String,
    connection: String,
    output: Option<[OwnedFd; 2]>,
    receipt: Option<PreparedTestsReceipt>,
    granted: bool,
    drained: bool,
    compile_failed: bool,
}

impl fmt::Debug for RetainedChild {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RetainedChild")
            .field("ready", &self.receipt.is_some())
            .field("granted", &self.granted)
            .field("drained", &self.drained)
            .field("compile_failed", &self.compile_failed)
            .finish_non_exhaustive()
    }
}

impl fmt::Debug for SessionOwner {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SessionOwner")
            .field("child_id", &self.child_id)
            .field("ready", &self.ready.is_some())
            .finish_non_exhaustive()
    }
}

impl fmt::Debug for GrantedSession {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("GrantedSession")
            .field("child_id", &self.child_id)
            .field("drained", &self.drained)
            .finish_non_exhaustive()
    }
}

impl RetainedChild {
    /// Capture before configuration or any configured child launch. The
    /// endpoint and received writers become CLOEXEC before returning, and
    /// stdin becomes /dev/null. This argument bounds only startup receipt;
    /// Init carries the original controller's absolute monotonic expiry.
    pub fn capture_stdin(deadline: Instant) -> io::Result<Self> {
        transport::validate_stream(libc::STDIN_FILENO)?;
        // SAFETY: fcntl validates stdin and returns a uniquely owned CLOEXEC
        // duplicate. No environment-selected descriptor is adopted.
        let copy = unsafe { libc::fcntl(libc::STDIN_FILENO, libc::F_DUPFD_CLOEXEC, 3) };
        if copy < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the successful duplication above returned unique ownership.
        let stream = UnixStream::from(unsafe { OwnedFd::from_raw_fd(copy) });
        let null = std::fs::File::open("/dev/null")?;
        // SAFETY: replace only this original startup stdin, retaining its
        // private endpoint in the owned CLOEXEC stream.
        if unsafe { libc::dup2(null.as_raw_fd(), libc::STDIN_FILENO) } != libc::STDIN_FILENO {
            return Err(io::Error::last_os_error());
        }
        let mut channel = Channel::new(stream, deadline)?;
        let (message, rights) = loop {
            if let Some(frame) = channel.poll(true)? {
                break frame;
            }
            channel.pause()?;
        };
        let Message::Init { session, connection, roles, expires_monotonic_ns } = message else {
            return channel.reject("retained startup requires an init frame");
        };
        if validate_session(&session).is_err()
            || validate_digest(&connection).is_err()
            || roles != [OutputRole::RuntimeStdout, OutputRole::RuntimeStderr]
            || rights.len() != 2
        {
            return channel.reject("invalid retained startup binding or runtime roles");
        }
        let output: [OwnedFd; 2] =
            rights.try_into().map_err(|_| invalid("invalid runtime writers"))?;
        for writer in &output {
            if let Err(error) = transport::validate_stream(writer.as_raw_fd()) {
                return channel.reject_error(error);
            }
        }
        channel.adopt_parent_expiry(expires_monotonic_ns)?;
        channel.ensure_quiet()?;
        Ok(Self {
            channel,
            session,
            connection,
            output: Some(output),
            receipt: None,
            granted: false,
            drained: false,
            compile_failed: false,
        })
    }

    pub fn session(&self) -> &str {
        &self.session
    }

    /// Original controller lifetime, independent of the startup receive bound.
    /// Pass this same absolute deadline through every later child phase.
    pub fn deadline(&self) -> Instant {
        self.channel.deadline()
    }

    /// Whether this endpoint consumed its original execution direction.
    /// This does not report queue completion or execution success.
    pub fn was_granted(&self) -> bool {
        self.granted
    }

    /// Flush caller-owned shell buffers first. Then this switches the actual
    /// stdio descriptors, closing compiler evidence while retaining runtime
    /// writers, and publishes one exact prepared-plan checkpoint.
    pub fn publish_ready(
        &mut self,
        receipt: &PreparedTestsReceipt,
        deadline: Instant,
    ) -> io::Result<()> {
        self.channel.limit_deadline(deadline);
        self.channel.check()?;
        if self.receipt.is_some() || self.granted || self.compile_failed || self.output.is_none() {
            return self.channel.reject("compile-ready is one-use");
        }
        if validate_receipt(receipt, &self.session).is_err() {
            return self.channel.reject("prepared receipt differs from the retained session");
        }
        self.channel.ensure_quiet()?;
        self.switch_stdio()?;
        self.channel.send(
            Message::CompileReady {
                session: self.session.clone(),
                connection: self.connection.clone(),
                receipt: receipt.clone(),
            },
            &[],
        )?;
        self.receipt = Some(receipt.clone());
        Ok(())
    }

    /// Publish a finite failed milestone, then let the queue return its real
    /// error and the parent reap its actual exit. No grant can follow it.
    pub fn publish_compile_failed(
        &mut self,
        diagnostic: &str,
        deadline: Instant,
    ) -> io::Result<()> {
        self.channel.limit_deadline(deadline);
        self.channel.check()?;
        if self.receipt.is_some()
            || self.granted
            || self.compile_failed
            || self.output.is_none()
            || diagnostic.is_empty()
            || diagnostic.len() > 4096
        {
            return self.channel.reject("invalid or repeated failed compile checkpoint");
        }
        self.channel.ensure_quiet()?;
        self.switch_stdio()?;
        self.channel.send(
            Message::CompileFailed {
                session: self.session.clone(),
                connection: self.connection.clone(),
                diagnostic: diagnostic.into(),
            },
            &[],
        )?;
        self.compile_failed = true;
        Ok(())
    }

    fn switch_stdio(&mut self) -> io::Result<()> {
        if let Err(error) = io::stdout().flush().and_then(|()| io::stderr().flush()) {
            return self.channel.reject_error(error);
        }
        let output = self.output.take().expect("checked runtime writers");
        for (writer, target) in output.iter().zip([libc::STDOUT_FILENO, libc::STDERR_FILENO]) {
            // SAFETY: each writer is an owned, validated Unix stream, kept
            // CLOEXEC throughout compilation. dup2 replaces only test stdio.
            if unsafe { libc::dup2(writer.as_raw_fd(), target) } != target {
                return self.channel.reject_error(io::Error::last_os_error());
            }
        }
        drop(output);
        Ok(())
    }

    /// Return one matching direction to the existing manifest validator. No
    /// favorable proof grade or executable authority is created here.
    pub fn poll_grant(&mut self, deadline: Instant) -> io::Result<Option<ExecutionGrant>> {
        self.channel.limit_deadline(deadline);
        if self.granted || self.receipt.is_none() {
            return self.channel.reject("grant is unavailable or already consumed");
        }
        let Some((message, rights)) = self.channel.poll(false)? else { return Ok(None) };
        debug_assert!(rights.is_empty());
        let Message::Grant { session, connection, receipt, authority_path, authority_sha256 } =
            message
        else {
            return self.channel.reject("expected exactly one retained grant frame");
        };
        if session != self.session
            || connection != self.connection
            || !same_receipt(&receipt, self.receipt.as_ref().expect("prepared checkpoint"))
            || validate_path(&authority_path).is_err()
            || validate_digest(&authority_sha256).is_err()
        {
            return self.channel.reject("grant does not match the retained prepared checkpoint");
        }
        self.channel.ensure_quiet()?;
        self.granted = true;
        Ok(Some(ExecutionGrant {
            session,
            plan_sha256: receipt.sha256,
            authority_path,
            authority_sha256,
        }))
    }

    /// Publish once, after the granted queue and its command-result reporting
    /// have drained. This event carries no exit status, test success, or proof
    /// claim. The caller must still terminate and the parent must observe that
    /// actual exit under the original watchdog.
    pub fn publish_drained(&mut self, deadline: Instant) -> io::Result<()> {
        self.channel.limit_deadline(deadline);
        if !self.granted || self.drained {
            return self.channel.reject("queue-drained requires one unused execution grant");
        }
        self.channel.ensure_quiet()?;
        self.channel.send(
            Message::DrainComplete {
                session: self.session.clone(),
                connection: self.connection.clone(),
                receipt: self.receipt.as_ref().expect("granted prepared checkpoint").clone(),
            },
            &[],
        )?;
        self.drained = true;
        Ok(())
    }

    /// A controller disappearing or writing further frames stops execution.
    /// The queue must make this observation sticky before dispatching again.
    pub fn poll_cancelled(&mut self) -> io::Result<bool> {
        if !self.granted {
            return self.channel.reject("execution has not consumed a grant");
        }
        self.poll_parent_closed()
    }

    /// Observe controller loss while compilation or qualification is active.
    /// Before Ready, bytes are an illegal early grant. After Ready, leave a
    /// queued grant untouched for poll_grant; after granting, refuse all bytes.
    pub fn poll_parent_closed(&mut self) -> io::Result<bool> {
        if self.channel.failed() {
            return Ok(true);
        }
        if self.receipt.is_some() && !self.granted {
            return self.channel.peer_closed();
        }
        match self.channel.ensure_quiet() {
            Ok(()) => Ok(false),
            Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => Ok(true),
            Err(error) => Err(error),
        }
    }
}

/// One checked wire direction, never a deserializable execution credential.
#[derive(Debug)]
pub struct ExecutionGrant {
    session: String,
    plan_sha256: String,
    authority_path: PathBuf,
    authority_sha256: String,
}

impl ExecutionGrant {
    pub fn session(&self) -> &str {
        &self.session
    }
    pub fn plan_sha256(&self) -> &str {
        &self.plan_sha256
    }
    pub fn authority_path(&self) -> &Path {
        &self.authority_path
    }
    pub fn authority_sha256(&self) -> &str {
        &self.authority_sha256
    }
}

fn same_receipt(left: &PreparedTestsReceipt, right: &PreparedTestsReceipt) -> bool {
    left.schema == right.schema
        && left.session == right.session
        && left.path == right.path
        && left.sha256 == right.sha256
}

fn validate_receipt(receipt: &PreparedTestsReceipt, session: &str) -> io::Result<()> {
    if receipt.schema != RECEIPT_SCHEMA || receipt.session != session {
        return Err(invalid("invalid retained prepared receipt"));
    }
    validate_path(Path::new(&receipt.path))?;
    validate_digest(&receipt.sha256)
}

fn validate_session(session: &str) -> io::Result<()> {
    validate_digest(session)
}

fn validate_digest(digest: &str) -> io::Result<()> {
    if digest.len() == 64
        && digest.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        Ok(())
    } else {
        Err(invalid("retained session/digest is not canonical SHA-256 text"))
    }
}

fn validate_path(path: &Path) -> io::Result<()> {
    if path.is_absolute() && path.to_str().is_some_and(|p| !p.contains('\0')) {
        Ok(())
    } else {
        Err(invalid("retained authority/receipt path must be absolute UTF-8 without NUL"))
    }
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

#[cfg(test)]
mod tests;
