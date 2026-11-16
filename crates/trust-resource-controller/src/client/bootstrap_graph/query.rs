//! Original accepted native SDK query, with no local process or fallback.
use std::io;
use std::os::fd::BorrowedFd;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_provenance::{Host, PinnedHelper};

use super::{
    BootstrapGraphSupport, Connection, EnrolledBootstrapGraph, OutputBoundBootstrapGraph,
    QueryState, SourceBoundBootstrapGraph, bounded, finish, live, time,
};
use crate::bootstrap_graph::{query, transport};
use crate::client::{Client, Delivery};
use crate::{Channel, MetadataCompletion, MetadataPrepared, Started};

/// Actual captured DATA; missing accounting remains absent. It grants neither
/// protected graph completion nor CPU, GNU, SDK or manager release authority.
#[derive(Debug)]
pub struct QueryObservation {
    pub prepared: MetadataPrepared,
    pub started: Started,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub completion: MetadataCompletion,
    pub accounting: crate::accounting::Observation,
    pub event_prefix: Vec<u8>,
    pub event_bytes_seen: u64,
    pub event_frames_seen: u64,
}

struct Transcript {
    prepared: Option<MetadataPrepared>,
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
    fn event(&mut self, event: query::Event) -> io::Result<()> {
        if self.failed {
            return Err(crate::wire::invalid());
        }
        let result = (|| {
            match event {
                query::Event::Prepared(prepared)
                    if self.prepared.is_none() && self.started.is_none() =>
                {
                    self.prepared = Some(*prepared)
                }
                query::Event::Started(started)
                    if self.prepared.is_some() && self.started.is_none() =>
                {
                    self.started = Some(started)
                }
                query::Event::Output { stream, offset, bytes } if self.started.is_some() => {
                    let index = match stream {
                        query::Stream::Stdout => 0,
                        query::Stream::Stderr => 1,
                    };
                    let output = if index == 0 { &mut self.stdout } else { &mut self.stderr };
                    if self.eof[index]
                        || offset != output.len() as u64
                        || output
                            .len()
                            .checked_add(bytes.len())
                            .is_none_or(|len| len as u64 > query::MAX_OUTPUT)
                    {
                        return Err(crate::wire::invalid());
                    }
                    output.extend(bytes);
                }
                query::Event::Eof { stream, bytes } if self.started.is_some() => {
                    let index = match stream {
                        query::Stream::Stdout => 0,
                        query::Stream::Stderr => 1,
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
    ) -> QueryObservation {
        QueryObservation {
            prepared: self.prepared.expect("checked original preparation"),
            started: self.started.expect("checked actual start"),
            stdout: self.stdout,
            stderr: self.stderr,
            completion,
            accounting,
            event_prefix: self.raw,
            event_bytes_seen: self.bytes_seen,
            event_frames_seen: self.frames_seen,
        }
    }
}

fn receive_operation(
    channel: &mut Channel,
    request: &query::Request,
    digest: [u8; 32],
    host: &str,
    boot: &str,
    deadline: Instant,
    transcript: &mut Transcript,
) -> io::Result<(MetadataCompletion, crate::accounting::Observation)> {
    let result = (|| {
        loop {
            let bytes = channel.receive_observed(deadline, |bytes| transcript.observe(bytes))?;
            transcript.frames_seen =
                transcript.frames_seen.checked_add(1).ok_or_else(crate::wire::invalid)?;
            if crate::wire::header(&bytes, 76).is_ok() {
                let event = query::Event::decode(&bytes, request, digest)?;
                if let query::Event::Prepared(prepared) = &event
                    && (prepared.host != host || prepared.boot != boot)
                {
                    return Err(crate::wire::invalid());
                }
                transcript.event(event)?;
            } else {
                return match query::Terminal::decode(&bytes, request, digest)? {
                    query::Terminal::Completed { completion, observation } => {
                        transcript.complete()?;
                        Ok((completion, observation))
                    }
                    query::Terminal::Refused { reason } => {
                        Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                    }
                    query::Terminal::Unknown { reason } => Err(io::Error::other(reason)),
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

/// Receive and acknowledge bounded query observations on an already-created
/// resident channel using the same production reducer and physical EOF checks.
/// This creates no Client/SDK, original child, GNU loan, owning completion or
/// seed qualification. The resident executor must separately consume its actual
/// native wait/retirement owners; returned statuses and bytes are DATA only.
pub fn observe_resident_query_channel(
    mut channel: Channel,
    request: &query::Request,
    host: &str,
    boot: &str,
    deadline: Instant,
) -> io::Result<QueryObservation> {
    request.validate()?;
    let digest = Sha256::digest(request.binding_preimage()?).into();
    let mut transcript = Transcript::new();
    let (completion, accounting) =
        receive_operation(&mut channel, request, digest, host, boot, deadline, &mut transcript)?;
    require_final_eof(&mut channel, deadline, &mut transcript)?;
    time(deadline)?;
    channel.send(&[1], deadline)?;
    time(deadline)?;
    // Closing this SAME actual channel supplies its physical control EOF, not
    // a replacement stream, saved ACK, request replay or native closure claim.
    drop(channel);
    Ok(transcript.observation(completion, accounting))
}

struct OriginalQuery {
    host: Option<Host>,
    channel: Option<Channel>,
    pin: Arc<PinnedHelper>,
    request: query::Request,
    deadline: Instant,
    transcript: Transcript,
}
impl Drop for OriginalQuery {
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

pub struct QueryFailure {
    delivery: Delivery,
    error: io::Error,
    original: Option<Box<OriginalQuery>>,
    completed: Option<Box<CompletedSdkQuery>>,
}
impl QueryFailure {
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
    fn unknown(mut original: OriginalQuery, error: io::Error) -> Self {
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
impl Drop for QueryFailure {
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
impl std::fmt::Debug for QueryFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BootstrapSdkQueryFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for QueryFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original Bootstrap SDK query {:?}: {}", self.delivery, self.error)
    }
}
impl std::error::Error for QueryFailure {}

/// Minted only by consuming the SAME accepted Host after its distinct actual
/// terminal, both captured-stream EOFs, native control EOF and pin/root checks.
/// There is no public constructor/serde from observation or a saved terminal.
/// It closes only this contained query; it cannot close the Bootstrap graph.
pub struct CompletedSdkQuery {
    accepted: PinnedHelper,
    pin: Arc<PinnedHelper>,
    request: query::Request,
    deadline: Instant,
    observation: QueryObservation,
}
impl CompletedSdkQuery {
    pub fn request(&self) -> &query::Request {
        &self.request
    }
    pub fn observation(&self) -> &QueryObservation {
        &self.observation
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        bounded(self.deadline, deadline)?;
        finish(deadline, || {
            self.accepted.validate(deadline)?;
            self.pin.validate(deadline)
        })
    }
}

struct QueryRoot<'a> {
    key: &'a crate::bootstrap_graph::Key,
    context: &'a crate::ContextReply,
    deadline: Instant,
    pin: &'a Arc<PinnedHelper>,
    queries: &'a mut QueryState,
}
impl<'a> QueryRoot<'a> {
    fn support(support: &'a mut BootstrapGraphSupport) -> Self {
        Self {
            key: &support.key,
            context: &support.context,
            deadline: support.deadline,
            pin: &support.pin,
            queries: &mut support.queries,
        }
    }
    fn connection(original: &'a mut Connection) -> Self {
        Self {
            key: &original.request.key,
            context: &original.context,
            deadline: original.deadline,
            pin: &original.pin,
            queries: &mut original.queries,
        }
    }
}
impl EnrolledBootstrapGraph {
    pub fn sdk_query(
        &mut self,
        client: &Client,
        request: query::Request,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        let original = self.original.as_mut().expect("same original enrolled graph");
        original.check(deadline).map_err(QueryFailure::before)?;
        client.query_with_original(QueryRoot::connection(original), request, gnu, deadline)
    }
}
impl OutputBoundBootstrapGraph {
    pub fn sdk_query(
        &mut self,
        client: &Client,
        request: query::Request,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        let original = self.original.as_mut().expect("same original output graph");
        original.check(deadline).map_err(QueryFailure::before)?;
        client.query_with_original(QueryRoot::connection(original), request, gnu, deadline)
    }
}
impl SourceBoundBootstrapGraph {
    pub fn sdk_query(
        &mut self,
        client: &Client,
        request: query::Request,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        let original = self.original.as_mut().expect("same original source graph");
        original.check(deadline).map_err(QueryFailure::before)?;
        client.query_with_original(QueryRoot::connection(original), request, gnu, deadline)
    }
}
impl Client {
    pub fn bootstrap_sdk_query(
        &self,
        support: &mut BootstrapGraphSupport,
        request: query::Request,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        self.query_with_original(QueryRoot::support(support), request, gnu, deadline)
    }
    /// The original coordinator retains its implicit unit and actual scheduler.
    /// The Host must fund the query with an actual supplementary loan from that
    /// same paid epoch. A synchronous client wait supplies no quiescence proof,
    /// CPU grant or authority to construct a replacement GNU server.
    fn query_with_original(
        &self,
        root: QueryRoot<'_>,
        request: query::Request,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        let started = Instant::now();
        let preflight = (|| {
            bounded(root.deadline, deadline)?;
            request.validate()?;
            root.queries.check(request.key.sequence)?;
            if &request.key.graph != root.key || !Arc::ptr_eq(root.pin, &self.host) {
                return Err(crate::wire::invalid());
            }
            validate_original_sdk(root.context.context.sdk.as_ref(), &request)?;
            transport::check_gnu_identity(&request.gnu, gnu)?;
            live(root.context, deadline)
        })();
        preflight.map_err(QueryFailure::before)?;
        let payload = request.encode().map_err(QueryFailure::before)?;
        let hello = request.hello().map_err(QueryFailure::before)?;
        let digest =
            Sha256::digest(request.binding_preimage().map_err(QueryFailure::before)?).into();
        let query_bound = started
            .checked_add(Duration::from_nanos(request.timeout_ns))
            .ok_or_else(|| QueryFailure::before(io::ErrorKind::TimedOut.into()))?;
        let deadline = deadline.min(query_bound);
        // One-use before actual connect. No previous attempted sequence is
        // replayed, even if delivery later becomes Unknown.
        root.queries.begin().map_err(QueryFailure::before)?;
        let host = self.host.connect(deadline).map_err(QueryFailure::before)?;
        let channel = Channel::new(host.stream().try_clone().map_err(QueryFailure::before)?)
            .map_err(QueryFailure::before)?;
        let mut original = OriginalQuery {
            host: Some(host),
            channel: Some(channel),
            pin: Arc::clone(&self.host),
            request,
            deadline,
            transcript: Transcript::new(),
        };
        let result = finish(deadline, || {
            original.host.as_ref().expect("actual accepted query").revalidate(deadline)?;
            original.channel.as_mut().expect("same original channel").send(&hello, deadline)?;
            original.channel.as_mut().expect("same original channel").send(&payload, deadline)?;
            let (completion, accounting) = receive_operation(
                original.channel.as_mut().expect("same original channel"),
                &original.request,
                digest,
                &root.context.context.host,
                &root.context.context.boot,
                deadline,
                &mut original.transcript,
            )?;
            require_final_eof(
                original.channel.as_mut().expect("same original channel"),
                deadline,
                &mut original.transcript,
            )?;
            original.host.as_ref().expect("same accepted query").revalidate(deadline)?;
            original.pin.validate(deadline)?;
            live(root.context, deadline)?;
            transport::check_gnu_identity(&original.request.gnu, gnu)?;
            original.channel.as_mut().expect("same original channel").send(&[1], deadline)?;
            original.host.as_ref().expect("same accepted query").revalidate(deadline)?;
            Ok((completion, accounting))
        });
        let (completion, accounting) = match result {
            Ok(actual) => actual,
            Err(error) => {
                return Err(QueryFailure::unknown(original, error));
            }
        };
        let accepted = match original
            .host
            .take()
            .expect("same original accepted Host")
            .into_helper_preserving(deadline)
        {
            Ok(accepted) => accepted,
            Err(failure) => {
                let (host, error) = *failure;
                original.host = Some(host);
                return Err(QueryFailure::unknown(original, error));
            }
        };
        // Actual typed terminal and physical EOF precede closing this channel.
        // Graph/SDK/GNU owners live separately in their original coordinator.
        drop(original.channel.take());
        let transcript = std::mem::replace(&mut original.transcript, Transcript::new());
        let completed = CompletedSdkQuery {
            accepted,
            pin: Arc::clone(&original.pin),
            request: original.request.clone(),
            deadline: original.deadline,
            observation: transcript.observation(completion, accounting),
        };
        if let Err(error) = finish(deadline, || {
            completed.revalidate(deadline)?;
            transport::check_gnu_identity(&completed.request.gnu, gnu)
        }) {
            return Err(QueryFailure {
                delivery: Delivery::Unknown,
                error,
                original: None,
                completed: Some(Box::new(completed)),
            });
        }
        if let Err(error) = time(deadline) {
            return Err(QueryFailure {
                delivery: Delivery::Unknown,
                error,
                original: None,
                completed: Some(Box::new(completed)),
            });
        }
        if let Err(error) = root.queries.completed(&completed) {
            return Err(QueryFailure {
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
    request: &query::Request,
) -> io::Result<()> {
    // Keeper::context and the original inherited SDK capture describe the
    // execution ROOT here. Request::validate separately binds the selected
    // exact bin/trustc or bin/targo image and the complete query operation.
    if sdk.is_none_or(|sdk| sdk.execution != request.sdk_root) {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
