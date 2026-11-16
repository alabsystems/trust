//! One original output-bound object operation, without a local compiler fallback.
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd as _, BorrowedFd};
use std::os::unix::fs::MetadataExt as _;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_provenance::{Host, PinnedHelper};

use super::{OutputBoundBootstrapGraph, bounded, finish, time};
use crate::bootstrap_graph::{object, transport};
use crate::client::{Client, Delivery};
use crate::{Channel, MetadataCompletion, MetadataFile, Started};

/// Actual captured DATA; missing accounting remains absent. It grants neither
/// protected graph completion nor CPU, GNU, SDK or manager release authority.
#[derive(Debug)]
pub struct ObjectObservation {
    pub prepared: object::Prepared,
    pub started: Started,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub completion: MetadataCompletion,
    pub accounting: crate::accounting::Observation,
    pub artifact: Option<MetadataFile>,
    pub event_prefix: Vec<u8>,
    pub event_bytes_seen: u64,
    pub event_frames_seen: u64,
}

struct Transcript {
    prepared: Option<object::Prepared>,
    started: Option<Started>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    eof: [bool; 2],
    failed: bool,
    raw: Vec<u8>,
    bytes_seen: u64,
    frames_seen: u64,
}
impl Transcript {
    fn new() -> Self {
        Self {
            prepared: None,
            started: None,
            stdout: vec![],
            stderr: vec![],
            eof: [false; 2],
            failed: false,
            raw: vec![],
            bytes_seen: 0,
            frames_seen: 0,
        }
    }
    fn observe(&mut self, bytes: &[u8]) {
        match self.bytes_seen.checked_add(bytes.len() as u64) {
            Some(count) => self.bytes_seen = count,
            None => self.failed = true,
        }
        let capacity = crate::METADATA_EVENT_PREFIX_MAX_BYTES.saturating_sub(self.raw.len());
        self.raw.extend_from_slice(&bytes[..bytes.len().min(capacity)]);
    }
    fn event(&mut self, event: object::Event) -> io::Result<()> {
        if self.failed {
            return Err(crate::wire::invalid());
        }
        let result = (|| {
            match event {
                object::Event::Prepared(prepared)
                    if self.prepared.is_none() && self.started.is_none() =>
                {
                    self.prepared = Some(*prepared)
                }
                object::Event::Started(started)
                    if self.prepared.is_some() && self.started.is_none() =>
                {
                    self.started = Some(started)
                }
                object::Event::Output { stream, offset, bytes } if self.started.is_some() => {
                    let index = match stream {
                        object::Stream::Stdout => 0,
                        object::Stream::Stderr => 1,
                    };
                    let output = if index == 0 { &mut self.stdout } else { &mut self.stderr };
                    if self.eof[index]
                        || offset != output.len() as u64
                        || output
                            .len()
                            .checked_add(bytes.len())
                            .is_none_or(|len| len as u64 > object::MAX_OUTPUT)
                    {
                        return Err(crate::wire::invalid());
                    }
                    output.extend(bytes);
                }
                object::Event::Eof { stream, bytes } if self.started.is_some() => {
                    let index = match stream {
                        object::Stream::Stdout => 0,
                        object::Stream::Stderr => 1,
                    };
                    let observed = if index == 0 { self.stdout.len() } else { self.stderr.len() };
                    if self.eof[index] || bytes != observed as u64 {
                        return Err(crate::wire::invalid());
                    }
                    self.eof[index] = true;
                }
                _ => return Err(crate::wire::invalid()),
            }
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    fn complete(&self) -> io::Result<()> {
        if self.failed || self.prepared.is_none() || self.started.is_none() || self.eof != [true; 2]
        {
            return Err(crate::wire::invalid());
        }
        Ok(())
    }
    fn observation(
        self,
        completion: MetadataCompletion,
        accounting: crate::accounting::Observation,
        artifact: Option<MetadataFile>,
    ) -> ObjectObservation {
        ObjectObservation {
            prepared: self.prepared.expect("checked original preparation"),
            started: self.started.expect("checked actual start"),
            stdout: self.stdout,
            stderr: self.stderr,
            completion,
            accounting,
            artifact,
            event_prefix: self.raw,
            event_bytes_seen: self.bytes_seen,
            event_frames_seen: self.frames_seen,
        }
    }
}

struct ExpectedPreparation<'a> {
    request: &'a object::Request,
    digest: [u8; 32],
    host: &'a str,
    boot: &'a str,
}

fn receive_operation(
    channel: &mut Channel,
    expected: ExpectedPreparation<'_>,
    deadline: Instant,
    transcript: &mut Transcript,
    source: &[BorrowedFd<'_>; 2],
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<(MetadataCompletion, crate::accounting::Observation, Option<MetadataFile>)> {
    let ExpectedPreparation { request, digest, host, boot } = expected;
    let result = (|| {
        loop {
            let bytes = channel.receive_observed(deadline, |bytes| transcript.observe(bytes))?;
            transcript.frames_seen =
                transcript.frames_seen.checked_add(1).ok_or_else(crate::wire::invalid)?;
            if crate::wire::header(&bytes, 79).is_ok() {
                let event = object::Event::decode(&bytes, request, digest)?;
                if let object::Event::Prepared(prepared) = &event
                    && (prepared.inventory.host != host || prepared.inventory.boot != boot)
                {
                    return Err(crate::wire::invalid());
                }
                let prepared = matches!(event, object::Event::Prepared(_));
                transcript.event(event)?;
                if prepared {
                    object::transport::send_source(
                        channel,
                        request,
                        source,
                        deadline,
                        &mut revalidate,
                    )?;
                }
            } else {
                return match object::Terminal::decode(&bytes, request, digest)? {
                    object::Terminal::Completed { completion, observation, artifact } => {
                        transcript.complete()?;
                        Ok((*completion, observation, artifact))
                    }
                    object::Terminal::Refused { reason } => {
                        Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                    }
                    object::Terminal::Unknown { reason } => Err(io::Error::other(reason)),
                };
            }
        }
    })();
    if result.is_err() {
        transcript.failed = true;
        channel.poison();
    }
    result
}
fn require_final_eof(
    channel: &mut Channel,
    deadline: Instant,
    transcript: &mut Transcript,
) -> io::Result<()> {
    let result = (|| {
        loop {
            time(deadline)?;
            if channel.at_eof()? {
                return time(deadline);
            }
            if channel.ready_to_receive()? {
                // Retain actually read trailing/partial bytes before refusal.
                let _ = channel.receive_observed(deadline, |bytes| transcript.observe(bytes))?;
                return Err(crate::wire::invalid());
            }
            std::thread::sleep(Duration::from_millis(2));
        }
    })();
    if result.is_err() {
        transcript.failed = true;
        channel.poison();
    }
    result
}

struct OriginalObject {
    host: Option<Host>,
    channel: Option<Channel>,
    pin: Arc<PinnedHelper>,
    request: object::Request,
    deadline: Instant,
    transcript: Transcript,
}
impl Drop for OriginalObject {
    fn drop(&mut self) {
        // Unknown abandonment cannot release the accepted operation boundary.
        // Actual Host independently retains its original Job/borrower until
        // native retirement. This is no cancellation/closure or replay path.
        if let Some(original) = self.host.take() {
            std::mem::forget(original);
        }
        if let Some(original) = self.channel.take() {
            std::mem::forget(original);
        }
    }
}

pub struct ObjectFailure {
    delivery: Delivery,
    error: io::Error,
    original: Option<Box<OriginalObject>>,
    completed: Option<Box<CompletedObjectCompile>>,
}
impl ObjectFailure {
    pub fn delivery(&self) -> Delivery {
        self.delivery
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    /// Exact received prefixes survive malformed/trailing frames and late
    /// native failures; neither prefix length nor status supplies completion.
    pub fn prefixes(&self) -> (&[u8], &[u8]) {
        if let Some(original) = &self.original {
            return (&original.transcript.stdout, &original.transcript.stderr);
        }
        if let Some(completed) = &self.completed {
            return (&completed.observation.stdout, &completed.observation.stderr);
        }
        (&[], &[])
    }
    pub fn event_prefix(&self) -> (&[u8], u64) {
        if let Some(original) = &self.original {
            return (&original.transcript.raw, original.transcript.bytes_seen);
        }
        if let Some(completed) = &self.completed {
            return (&completed.observation.event_prefix, completed.observation.event_bytes_seen);
        }
        (&[], 0)
    }
    fn before(error: io::Error) -> Self {
        Self { delivery: Delivery::BeforeRequest, error, original: None, completed: None }
    }
    fn unknown(mut original: OriginalObject, error: io::Error) -> Self {
        if let Some(channel) = &mut original.channel {
            channel.poison();
        }
        Self {
            delivery: Delivery::Unknown,
            error,
            original: Some(Box::new(original)),
            completed: None,
        }
    }
}
impl Drop for ObjectFailure {
    fn drop(&mut self) {
        // Preserve the actual opaque boundary and raw observations even if a
        // caller abandons the error, including a failure after compaction.
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
        if let Some(completed) = self.completed.take() {
            std::mem::forget(completed);
        }
    }
}
impl std::fmt::Debug for ObjectFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BootstrapObjectCompileFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for ObjectFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original Bootstrap object compile {:?}: {}", self.delivery, self.error)
    }
}
impl std::error::Error for ObjectFailure {}

/// Minted only by consuming the SAME accepted Host after its distinct actual
/// terminal, both captured-stream EOFs, native control EOF and pin/root checks.
/// There is no public constructor/serde from observation or a saved terminal.
/// It closes only this contained object operation; it cannot close the Bootstrap graph.
pub struct CompletedObjectCompile {
    accepted: PinnedHelper,
    pin: Arc<PinnedHelper>,
    request: object::Request,
    deadline: Instant,
    observation: ObjectObservation,
}
impl CompletedObjectCompile {
    pub fn request(&self) -> &object::Request {
        &self.request
    }
    pub fn observation(&self) -> &ObjectObservation {
        &self.observation
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        bounded(self.deadline, deadline)?;
        finish(deadline, || {
            self.accepted.validate(deadline)?;
            self.pin.validate(deadline)
        })
    }

    /// Reobserve access/identity of this operation's actual published File.
    /// The caller must retain the SAME output guard and independently check
    /// its current name, full bytes/hash and native object format. This method
    /// creates no File, artifact owner, SDK, graph closure or release grant.
    pub fn require_sealed_artifact(&self, file: &File, deadline: Instant) -> io::Result<()> {
        finish(deadline, || {
            self.revalidate(deadline)?;
            let expected =
                self.observation.artifact.as_ref().ok_or_else(|| {
                    io::Error::other("original operation has no published artifact")
                })?;
            require_sealed_file(expected, file, deadline)
        })
    }
}

type FileStamp = (u64, u64, u64, u32, u32, u32, u64, i64, i64, i64, i64);
fn file_stamp(meta: &std::fs::Metadata) -> FileStamp {
    (
        meta.dev(),
        meta.ino(),
        meta.len(),
        meta.mode(),
        meta.uid(),
        meta.gid(),
        meta.nlink(),
        meta.mtime(),
        meta.mtime_nsec(),
        meta.ctime(),
        meta.ctime_nsec(),
    )
}
fn require_sealed_file(expected: &MetadataFile, file: &File, deadline: Instant) -> io::Result<()> {
    finish(deadline, || {
        let before = file.metadata()?;
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        let local = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
        if flags < 0 || local < 0 {
            return Err(io::Error::last_os_error());
        }
        if !before.is_file()
            || before.nlink() != 1
            || before.uid() != unsafe { libc::geteuid() }
            || before.mode() & 0o7777 != 0o400
            || before.dev() != expected.device
            || before.ino() != expected.inode
            || before.len() != expected.bytes
            || flags & libc::O_ACCMODE != libc::O_RDONLY
            || local & libc::FD_CLOEXEC == 0
        {
            return Err(io::Error::other("original object is not the same sealed read-only File"));
        }
        trust_resource_provenance::require_no_acl_grants(file)?;
        if file_stamp(&file.metadata()?) != file_stamp(&before) {
            return Err(io::Error::other("original object changed during access observation"));
        }
        Ok(())
    })
}

impl OutputBoundBootstrapGraph {
    /// # Safety
    /// The original trusted coordinator must lend the SAME source-root
    /// description owned by this enrolled graph's OriginalSourceRoot and a
    /// read-only file opened beneath that owner. It must retain both actual
    /// source/output owners and this selected file through any success,
    /// failure, unwind or Unknown delivery. Paths, hashes, context data or
    /// arbitrary opened files cannot establish that ownership lineage.
    /// The SAME original GNU epoch must remain retained; this method never
    /// consumes or replaces the coordinator's implicit CPU or any GNU byte.
    pub unsafe fn compile_object(
        &mut self,
        client: &Client,
        request: object::Request,
        gnu: &[BorrowedFd<'_>; 2],
        source: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedObjectCompile, ObjectFailure> {
        let started = Instant::now();
        let root = self.original.as_mut().expect("same original output-bound graph");
        let preflight = (|| {
            bounded(root.deadline, deadline)?;
            request.validate()?;
            root.queries.check(request.key.sequence)?;
            if request.key.graph != root.request.key
                || request.source_root != root.request.source
                || request.source_directory != self.source.source_directory
                || request.output_root != root.request.output
                || request.gnu != root.request.gnu
                || request.output_directory != self.output.root
                || request.output_lock != self.output.lock
                || !Arc::ptr_eq(&root.pin, &client.host)
            {
                return Err(crate::wire::invalid());
            }
            validate_original_sdk(root.context.context.sdk.as_ref(), &request)?;
            transport::check_gnu_identity(&request.gnu, gnu)?;
            object::transport::check_source(&request, source, deadline)?;
            root.check(deadline)
        })();
        preflight.map_err(ObjectFailure::before)?;
        let payload = request.encode().map_err(ObjectFailure::before)?;
        let hello = request.hello().map_err(ObjectFailure::before)?;
        let digest =
            Sha256::digest(request.binding_preimage().map_err(ObjectFailure::before)?).into();
        let compile_bound = started
            .checked_add(Duration::from_nanos(request.timeout_ns))
            .ok_or_else(|| ObjectFailure::before(io::ErrorKind::TimedOut.into()))?;
        let deadline = deadline.min(compile_bound);
        root.queries.begin().map_err(ObjectFailure::before)?;
        // The restrictive state precedes connect/hello and is never cleared on
        // failure or unwind, including failure before any rights are offered.
        let host = client.host.connect(deadline).map_err(ObjectFailure::before)?;
        let channel = Channel::new(host.stream().try_clone().map_err(ObjectFailure::before)?)
            .map_err(ObjectFailure::before)?;
        let mut original = OriginalObject {
            host: Some(host),
            channel: Some(channel),
            pin: Arc::clone(&client.host),
            request,
            deadline,
            transcript: Transcript::new(),
        };
        let result = finish(deadline, || {
            let host = original.host.as_ref().expect("same original accepted operation");
            host.revalidate(deadline)?;
            original.channel.as_mut().unwrap().send(&hello, deadline)?;
            original.channel.as_mut().unwrap().send(&payload, deadline)?;
            let (completion, accounting, artifact) = receive_operation(
                original.channel.as_mut().unwrap(),
                ExpectedPreparation {
                    request: &original.request,
                    digest,
                    host: &root.context.context.host,
                    boot: &root.context.context.boot,
                },
                deadline,
                &mut original.transcript,
                source,
                || {
                    host.revalidate(deadline)?;
                    root.check(deadline)
                },
            )?;
            require_final_eof(
                original.channel.as_mut().unwrap(),
                deadline,
                &mut original.transcript,
            )?;
            host.revalidate(deadline)?;
            original.pin.validate(deadline)?;
            root.check(deadline)?;
            transport::check_gnu_identity(&original.request.gnu, gnu)?;
            object::transport::check_source(&original.request, source, deadline)?;
            original.channel.as_mut().unwrap().send(&[1], deadline)?;
            host.revalidate(deadline)?;
            Ok((completion, accounting, artifact))
        });
        let (completion, accounting, artifact) = match result {
            Ok(value) => value,
            Err(error) => return Err(ObjectFailure::unknown(original, error)),
        };
        let accepted = match original
            .host
            .take()
            .expect("same accepted Host")
            .into_helper_preserving(deadline)
        {
            Ok(accepted) => accepted,
            Err(failure) => {
                let (host, error) = *failure;
                original.host = Some(host);
                return Err(ObjectFailure::unknown(original, error));
            }
        };
        drop(original.channel.take());
        let transcript = std::mem::replace(&mut original.transcript, Transcript::new());
        let completed = CompletedObjectCompile {
            accepted,
            pin: Arc::clone(&original.pin),
            request: original.request.clone(),
            deadline: original.deadline,
            observation: transcript.observation(completion, accounting, artifact),
        };
        if let Err(error) = finish(deadline, || {
            completed.revalidate(deadline)?;
            root.check(deadline)?;
            transport::check_gnu_identity(&completed.request.gnu, gnu)?;
            object::transport::check_source(&completed.request, source, deadline)
        })
        .and_then(|()| root.queries.completed_object(&completed))
        .and_then(|()| {
            time(deadline).inspect_err(|_| {
                // A late final clock sample must not reopen graph dispatch.
                root.queries.active = Some(completed.request.key.sequence);
            })
        }) {
            return Err(ObjectFailure {
                delivery: Delivery::Unknown,
                error,
                original: None,
                completed: Some(Box::new(completed)),
            });
        }
        Ok(completed)
    }
}

fn validate_original_sdk(
    sdk: Option<&crate::SdkCustody>,
    request: &object::Request,
) -> io::Result<()> {
    // Keeper::context and the original inherited SDK capture describe the
    // execution ROOT here. Request::validate separately binds the selected
    // exact driver and sibling compiler images and the complete operation.
    if sdk.is_none_or(|sdk| sdk.execution != request.sdk_root) {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
