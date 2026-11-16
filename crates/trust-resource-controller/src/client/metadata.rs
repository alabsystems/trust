// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Direct authenticated metadata members. This holds actual original borrowed
//! descriptions; it never creates a pool, GNU credit, memory grant or Child.

use std::fs::File;
use std::io::{self, Read};
use std::os::fd::{AsFd, AsRawFd, OwnedFd};
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

use trust_resource_provenance::{Host, process, program};

use super::Client;
pub use crate::MetadataResult;
use crate::{
    Cancel, Channel, GnuTransport, METADATA_EVENT_PREFIX_MAX_BYTES, METADATA_MAX_OUTPUT,
    MetadataCompletion, MetadataEvent, MetadataFailureObservation, MetadataPrepared,
    SealedMetadataRequest, Started, Status, StatusFrame,
};

/// Actual held CPU/GNU descriptions, whose source labels must exactly match
/// the request. The caller retains the original logical dispatch owner until
/// positive retirement. Duplicating a descriptor does not acquire a grant.
pub struct MetadataIo {
    pub descriptions: Vec<OwnedFd>,
}

/// The actual pipe read by an incremental workload observer. Chunks are raw
/// bytes, including bytes received beyond the retained member-prefix bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetadataOutputStream {
    Stdout,
    Stderr,
}
type OutputObserver<'a> = dyn FnMut(MetadataOutputStream, &[u8]) -> io::Result<()> + 'a;
mod contained;
mod produced;
pub use contained::{
    CompletedProducedOperation, ContainedProducedError, ContainedProducedMember,
    SuccessfulProducedCompletion,
};
mod refusal;
pub use produced::{ProducedError, ProducedFailureObservation, ProducedMember, ProducedResult};
mod linker;
pub use linker::{LinkerError, LinkerMember, LinkerOutcome, LinkerResult};

pub enum MetadataError {
    BeforeRequest(io::Error),
    /// The host positively declined before descriptor attachment or launch.
    Refused,
    /// Delivery may have happened. Retain/cancel this member, fail its original
    /// execution unit, and never replay the request or mint replacement credit.
    Unknown {
        member: Box<MetadataMember>,
        error: io::Error,
    },
}
impl std::fmt::Debug for MetadataError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BeforeRequest(error) => f.debug_tuple("BeforeRequest").field(error).finish(),
            Self::Refused => f.write_str("Refused"),
            Self::Unknown { error, .. } => {
                f.debug_struct("Unknown").field("error", error).finish_non_exhaustive()
            }
        }
    }
}
impl std::fmt::Display for MetadataError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native metadata member {self:?}")
    }
}
impl std::error::Error for MetadataError {}

// Closed internal sum: both purposes retain exactly the same transport and
// lifecycle owner, while each validates its own mandatory request envelope.
#[derive(Clone)]
enum NativeQueryRequest {
    Linker(crate::linker::Request),
    Metadata(SealedMetadataRequest),
    Resolver(crate::resolver::SealedResolverQueryRequest),
    Workload(crate::workload::host::CompilerQuery),
    Paired(crate::paired_qualification::query::CompilerQuery),
    NativeJob(crate::native_job::query::CompilerQuery),
    Produced(
        crate::workload::host::produced::ProducedRequest,
        crate::workload::host::produced::RegistrationAck,
    ),
    ContainedProduced(
        crate::workload::host::contained::Request,
        crate::workload::host::produced::RegistrationAck,
    ),
    Coordinator(
        crate::workload::host::coordinator::Request,
        crate::workload::host::produced::RegistrationAck,
    ),
}
impl NativeQueryRequest {
    fn produced_parts(
        &self,
    ) -> Option<(
        &crate::workload::host::produced::ProducedRequest,
        &crate::workload::host::produced::RegistrationAck,
    )> {
        match self {
            Self::Produced(request, ack) => Some((request, ack)),
            Self::ContainedProduced(request, ack) => Some((&request.produced, ack)),
            Self::Coordinator(request, ack) => Some((&request.contained.produced, ack)),
            _ => None,
        }
    }
}
trait NativeQuery {
    fn contained(&self) -> Option<&crate::workload::host::contained::Request> {
        None
    }
    fn coordinator(&self) -> Option<&crate::workload::host::coordinator::Request> {
        None
    }
    fn linker(&self) -> Option<&crate::linker::Request> {
        None
    }
    fn member(&self) -> &crate::Request;
    fn validate_request(&self) -> io::Result<()>;
    fn payload(&self) -> io::Result<Vec<u8>>;
    fn purpose_hello(&self) -> io::Result<Vec<u8>>;
    fn validate_prepared(&self, prepared: &MetadataPrepared) -> io::Result<()>;
    fn produced_prepared(
        &self,
        _bytes: &[u8],
    ) -> io::Result<Option<crate::workload::host::produced::ProducedPrepared>> {
        Ok(None)
    }
    fn workload_completion(&self) -> Option<(u64, crate::workload::host::MemberKind)> {
        None
    }
    fn paired_query(&self) -> Option<&crate::paired_qualification::query::CompilerQuery> {
        None
    }
    fn native_job_query(&self) -> Option<&crate::native_job::query::CompilerQuery> {
        None
    }
    fn output_limit(&self) -> usize {
        METADATA_MAX_OUTPUT
    }
}
impl NativeQuery for SealedMetadataRequest {
    fn member(&self) -> &crate::Request {
        &self.member
    }
    fn validate_request(&self) -> io::Result<()> {
        self.validate()
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        self.encode()
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        self.hello()
    }
    fn validate_prepared(&self, p: &MetadataPrepared) -> io::Result<()> {
        p.validate_for(self)
    }
}
impl NativeQuery for crate::resolver::SealedResolverQueryRequest {
    fn member(&self) -> &crate::Request {
        &self.member
    }
    fn validate_request(&self) -> io::Result<()> {
        self.validate()
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        self.encode()
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        self.hello()
    }
    fn validate_prepared(&self, p: &MetadataPrepared) -> io::Result<()> {
        p.validate_for_resolver(self)
    }
}
impl NativeQuery for crate::workload::host::CompilerQuery {
    fn member(&self) -> &crate::Request {
        &self.member
    }
    fn validate_request(&self) -> io::Result<()> {
        self.validate()
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        self.encode()
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        self.hello()
    }
    fn validate_prepared(&self, prepared: &MetadataPrepared) -> io::Result<()> {
        self.validate_prepared(prepared)
    }
    fn workload_completion(&self) -> Option<(u64, crate::workload::host::MemberKind)> {
        Some((0, crate::workload::host::MemberKind::CompilerQuery))
    }
}
impl NativeQuery for crate::paired_qualification::query::CompilerQuery {
    fn member(&self) -> &crate::Request {
        &self.member
    }
    fn validate_request(&self) -> io::Result<()> {
        self.validate()
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        self.encode()
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        self.hello()
    }
    fn validate_prepared(&self, p: &MetadataPrepared) -> io::Result<()> {
        self.validate_prepared(p)
    }
    fn paired_query(&self) -> Option<&crate::paired_qualification::query::CompilerQuery> {
        Some(self)
    }
}
impl NativeQuery for crate::native_job::query::CompilerQuery {
    fn member(&self) -> &crate::Request {
        &self.member
    }
    fn validate_request(&self) -> io::Result<()> {
        self.validate()
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        self.encode()
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        self.hello()
    }
    fn validate_prepared(&self, p: &MetadataPrepared) -> io::Result<()> {
        self.validate_prepared(p)
    }
    fn native_job_query(&self) -> Option<&crate::native_job::query::CompilerQuery> {
        Some(self)
    }
}
impl NativeQuery for NativeQueryRequest {
    fn contained(&self) -> Option<&crate::workload::host::contained::Request> {
        match self {
            Self::ContainedProduced(request, _) => Some(request),
            Self::Coordinator(request, _) => Some(&request.contained),
            _ => None,
        }
    }
    fn coordinator(&self) -> Option<&crate::workload::host::coordinator::Request> {
        match self {
            Self::Coordinator(request, _) => Some(request),
            _ => None,
        }
    }
    fn linker(&self) -> Option<&crate::linker::Request> {
        match self {
            Self::Linker(request) => Some(request),
            _ => None,
        }
    }
    fn member(&self) -> &crate::Request {
        match self {
            Self::Linker(r) => &r.member,
            Self::Metadata(r) => r.member(),
            Self::Resolver(r) => r.member(),
            Self::Workload(r) => r.member(),
            Self::Paired(r) => r.member(),
            Self::NativeJob(r) => r.member(),
            Self::Produced(r, _) => &r.member,
            Self::ContainedProduced(r, _) => &r.produced.member,
            Self::Coordinator(r, _) => &r.contained.produced.member,
        }
    }
    fn validate_request(&self) -> io::Result<()> {
        match self {
            Self::Linker(r) => r.validate(),
            Self::Metadata(r) => r.validate_request(),
            Self::Resolver(r) => r.validate_request(),
            Self::Workload(r) => r.validate_request(),
            Self::Paired(r) => r.validate_request(),
            Self::NativeJob(r) => r.validate_request(),
            Self::Produced(r, _) => r.validate(),
            Self::ContainedProduced(r, _) => r.validate(),
            Self::Coordinator(r, _) => r.validate(),
        }
    }
    fn payload(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Linker(r) => r.encode(),
            Self::Metadata(r) => r.payload(),
            Self::Resolver(r) => r.payload(),
            Self::Workload(r) => r.payload(),
            Self::Paired(r) => r.payload(),
            Self::NativeJob(r) => r.payload(),
            Self::Produced(r, _) => r.encode(),
            Self::ContainedProduced(r, _) => r.encode(),
            Self::Coordinator(r, _) => r.encode(),
        }
    }
    fn purpose_hello(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Linker(r) => r.hello(),
            Self::Metadata(r) => r.purpose_hello(),
            Self::Resolver(r) => r.purpose_hello(),
            Self::Workload(r) => r.purpose_hello(),
            Self::Paired(r) => r.purpose_hello(),
            Self::NativeJob(r) => r.purpose_hello(),
            Self::Produced(r, _) => r.hello(),
            Self::ContainedProduced(r, _) => r.hello(),
            Self::Coordinator(r, _) => r.hello(),
        }
    }
    fn validate_prepared(&self, p: &MetadataPrepared) -> io::Result<()> {
        match self {
            Self::Linker(_) => Err(invalid("linker loan requires its distinct preparation 57")),
            Self::Metadata(r) => r.validate_prepared(p),
            Self::Resolver(r) => r.validate_prepared(p),
            Self::Workload(r) => r.validate_prepared(p),
            Self::Paired(r) => r.validate_prepared(p),
            Self::NativeJob(r) => r.validate_prepared(p),
            Self::Produced(..) | Self::ContainedProduced(..) | Self::Coordinator(..) => {
                Err(invalid("produced output requires its separate mixed-root preparation"))
            }
        }
    }
    fn produced_prepared(
        &self,
        bytes: &[u8],
    ) -> io::Result<Option<crate::workload::host::produced::ProducedPrepared>> {
        let Some((request, ack)) = self.produced_parts() else {
            return Ok(None);
        };
        if crate::wire::header(bytes, 54).is_err() {
            return Ok(None);
        }
        let prepared = crate::workload::host::produced::ProducedPrepared::decode(bytes, request)?;
        if prepared.executable != ack.executable || prepared.key != ack.key {
            return Err(invalid("produced preparation differs from original live registration"));
        }
        Ok(Some(prepared))
    }
    fn workload_completion(&self) -> Option<(u64, crate::workload::host::MemberKind)> {
        match self {
            Self::Workload(r) => r.workload_completion(),
            Self::Produced(r, _) => Some((r.key.ordinal, r.kind)),
            _ => None,
        }
    }
    fn paired_query(&self) -> Option<&crate::paired_qualification::query::CompilerQuery> {
        match self {
            Self::Paired(query) => Some(query),
            _ => None,
        }
    }
    fn native_job_query(&self) -> Option<&crate::native_job::query::CompilerQuery> {
        match self {
            Self::NativeJob(query) => Some(query),
            _ => None,
        }
    }
    fn output_limit(&self) -> usize {
        match self {
            Self::Produced(..) | Self::ContainedProduced(..) | Self::Coordinator(..) => {
                crate::workload::host::produced::MAX_OUTPUT_BYTES
            }
            Self::Linker(_) => crate::linker::MAX_OUTPUT,
            _ => METADATA_MAX_OUTPUT,
        }
    }
}

pub struct MetadataMember {
    host: Host,
    pin: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
    control: Channel,
    streams: MetadataStreams,
    request: NativeQueryRequest,
    _descriptions: Vec<OwnedFd>,
    poisoned: bool,
    result_delivered: bool,
    failure_observed: bool,
    // Positive only after StreamReady::Refused AND actual original-pin
    // validation. A poll io error or cached frame cannot set this predicate.
    refusal_finalized: bool,
}

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn ordered(request: &impl NativeQuery, descriptions: Vec<OwnedFd>) -> io::Result<Vec<OwnedFd>> {
    request.validate_request()?;
    let mut descriptors = std::collections::BTreeMap::new();
    for fd in descriptions {
        let source = u32::try_from(fd.as_raw_fd()).map_err(|_| invalid("negative descriptor"))?;
        // SAFETY: observe only this owned live descriptor's flags.
        let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
        if flags < 0 || flags & libc::FD_CLOEXEC == 0 || descriptors.insert(source, fd).is_some() {
            return Err(invalid("metadata descriptions must be distinct owned CLOEXEC handles"));
        }
    }
    let mut result = Vec::new();
    if let Some(cpu) = request.member().delegations.cpu {
        result
            .push(descriptors.remove(&cpu.source).ok_or_else(|| invalid("missing original CPU"))?);
    }
    let gnu = match &request.member().delegations.gnu {
        GnuTransport::NumericPipe { read, write } | GnuTransport::NamedFifo { read, write, .. } => {
            Some((read, write))
        }
        GnuTransport::None
            if request.linker().is_some()
                || matches!(
                    request.member().role,
                    crate::Role::WorkloadQuery | crate::Role::WorkloadProduced
                ) =>
        {
            None
        }
        GnuTransport::None => return Err(invalid("missing original GNU transport")),
    };
    for descriptor in gnu.into_iter().flat_map(|(read, write)| [read, write]) {
        result.push(
            descriptors
                .remove(&descriptor.source)
                .ok_or_else(|| invalid("missing original GNU handle"))?,
        );
    }
    if let Some(coordinator) = request.coordinator() {
        result.push(
            descriptors
                .remove(&coordinator.primary.source)
                .ok_or_else(|| invalid("missing original coordinator primary"))?,
        );
        result.push(
            descriptors
                .remove(&coordinator.broker.source)
                .ok_or_else(|| invalid("missing original parent broker endpoint"))?,
        );
        use std::os::unix::fs::MetadataExt as _;
        for lock in &coordinator.outputs.locks {
            let mut selected = None;
            for (number, fd) in &descriptors {
                let meta = File::from(fd.try_clone()?).metadata()?;
                if (meta.dev(), meta.ino()) == (lock.backing.device, lock.backing.inode)
                    && selected.replace(*number).is_some()
                {
                    return Err(invalid("duplicate original output description"));
                }
            }
            result.push(
                descriptors
                    .remove(
                        &selected
                            .ok_or_else(|| invalid("missing original coordinator output guard"))?,
                    )
                    .expect("selected held description"),
            );
        }
    }
    if !descriptors.is_empty() {
        return Err(invalid("unrequested metadata descriptions"));
    }
    Ok(result)
}

impl Client {
    /// One direct request on a freshly authenticated connection to the SAME
    /// pinned native ancestor. Only that host can admit CPU/memory and launch.
    /// After request delivery, errors retain the original connection/handles.
    pub fn metadata(
        &self,
        request: &SealedMetadataRequest,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        self.native_query(&NativeQueryRequest::Metadata(request.clone()), io, deadline)
    }

    /// NEW resolver-query purpose; never reinterprets a role3 metadata request.
    pub fn resolver_query(
        &self,
        request: &crate::resolver::SealedResolverQueryRequest,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        self.native_query(&NativeQueryRequest::Resolver(request.clone()), io, deadline)
    }
    /// Distinct cooperative workload purpose. It borrows the original actual
    /// CPU description without a GNU token or a resolver-role substitution.
    pub fn workload_query(
        &self,
        request: &crate::workload::host::CompilerQuery,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        self.native_query(&NativeQueryRequest::Workload(request.clone()), io, deadline)
    }
    /// Distinct50/v2 query under the authenticated paired root. Actual normal
    /// config environment stays in the bound command; no role6/v1 fallback.
    pub fn paired_qualification_query(
        &self,
        request: &crate::paired_qualification::query::CompilerQuery,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        self.native_query(&NativeQueryRequest::Paired(request.clone()), io, deadline)
    }
    pub fn native_job_query(
        &self,
        request: &crate::native_job::query::CompilerQuery,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        self.native_query(&NativeQueryRequest::NativeJob(request.clone()), io, deadline)
    }
    fn native_query(
        &self,
        request: &NativeQueryRequest,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        let prepare = || -> io::Result<_> {
            let payload = request.payload()?;
            let hello = request.purpose_hello()?;
            let descriptions = ordered(request, io.descriptions)?;
            let host = self.host.connect(deadline)?;
            let mut control = Channel::new(host.stream().try_clone()?)?;
            let (events, target_events) = UnixStream::pair()?;
            let (output, stdout, stderr) = Capture::with_limit(request.output_limit())?;
            let stdin = File::open("/dev/null")?;
            control.send(&hello, deadline)?;
            if control.receive(deadline)? != [0x50] {
                return Err(invalid("metadata host did not prepare the negotiated purpose"));
            }
            host.revalidate(deadline)?;
            Ok((
                payload,
                MetadataMember {
                    host,
                    pin: self.host.clone(),
                    control,
                    streams: MetadataStreams {
                        events: Channel::new(events)?,
                        output,
                        state: Lifecycle::default(),
                        observed: ObservedEvents::default(),
                        cancel_sent: false,
                        failed: false,
                    },
                    request: request.clone(),
                    _descriptions: descriptions,
                    poisoned: false,
                    result_delivered: false,
                    failure_observed: false,
                    refusal_finalized: false,
                },
                stdin,
                stdout,
                stderr,
                target_events,
            ))
        };
        let (payload, mut member, stdin, stdout, stderr, target_events) =
            prepare().map_err(MetadataError::BeforeRequest)?;
        let attach = (|| -> io::Result<bool> {
            member.control.send(&payload, deadline)?;
            let ready = member.control.receive(deadline)?;
            match ready.as_slice() {
                [0] => {
                    member.pin.validate(deadline)?;
                    return Ok(false);
                }
                [0x41] => {}
                _ => return Err(invalid("metadata host readiness was malformed")),
            }
            member.host.revalidate(deadline)?;
            let mut rights =
                vec![stdin.as_fd(), stdout.as_fd(), stderr.as_fd(), target_events.as_fd()];
            rights.extend(member._descriptions.iter().map(AsFd::as_fd));
            jobserver_utils::descriptor_transfer::send(
                member.host.stream(),
                &rights,
                0x46,
                deadline,
            )?;
            if member.control.receive(deadline)? != [1] {
                return Err(invalid("metadata host did not acknowledge descriptor attachment"));
            }
            member.pin.validate(deadline)?;
            Ok(true)
        })();
        // Only the host retains target-side output/events endpoints from here.
        drop((stdin, stdout, stderr, target_events));
        match attach {
            Ok(true) => Ok(member),
            Ok(false) => Err(MetadataError::Refused),
            Err(error) => Err(MetadataError::Unknown { member: Box::new(member), error }),
        }
    }
}

impl MetadataMember {
    /// Present only after the negotiated workload terminal, actual output/event
    /// EOF and original host validation. Missing components remain unobserved;
    /// no malformed/unknown execution can yield a measured zero.
    pub fn accounting(&self) -> Option<crate::accounting::Observation> {
        self.result_delivered.then_some(self.streams.state.accounting).flatten()
    }
    /// Available only after actual output/event EOF and original host recheck.
    pub fn paired_completion(&self) -> Option<&crate::paired_qualification::query::Completion> {
        self.result_delivered.then_some(self.streams.state.paired.as_ref()).flatten()
    }
    pub fn native_job_completion(&self) -> Option<&crate::native_job::query::Completion> {
        self.result_delivered.then_some(self.streams.state.native_job.as_ref()).flatten()
    }
    /// The old workload completion remains a separate v1 observation.
    pub fn workload_completion(&self) -> Option<&crate::workload::host::Completion> {
        self.result_delivered.then_some(self.streams.state.workload.as_ref()).flatten()
    }
    pub fn started(&self) -> Option<Started> {
        self.streams.state.started
    }

    /// Cancellation is best effort and never a release receipt. Continue
    /// polling the SAME member until Completed/Refused or conservative failure.
    pub fn cancel(&mut self, deadline: Instant) -> io::Result<()> {
        self.streams.cancel(&self.request, deadline)
    }

    /// Abandon this client unit and retain its available original bounded
    /// stream bytes once. This never reports Completed, exit or retirement;
    /// the caller must still cancel/fail and retire the original native scope.
    pub fn take_failure_observation(&mut self) -> Option<MetadataFailureObservation> {
        self.take_failure_observation_inner(&mut None)
    }

    /// Workload-only final bounded drain into the SAME original observer. A
    /// failed observer is never retried; its already-read prefix remains in
    /// the returned incomplete observation. This grants no retirement fact.
    pub fn take_failure_observation_with_observer(
        &mut self,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<MetadataFailureObservation>> {
        self.require_workload_observer()?;
        Ok(self.take_failure_observation_inner(&mut Some(observer)))
    }

    fn take_failure_observation_inner(
        &mut self,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> Option<MetadataFailureObservation> {
        if self.result_delivered || self.failure_observed {
            return None;
        }
        self.failure_observed = true;
        self.poisoned = true;
        Some(self.streams.take_failure_observation_inner(&self.request, observer))
    }

    /// Bounded nonblocking work except a ready partial event frame, whose
    /// original absolute deadline is capped at250ms. A lost/malformed lifecycle
    /// poisons this execution unit; it never produces a fabricated exit.
    pub fn poll(&mut self, deadline: Instant) -> io::Result<Option<MetadataResult>> {
        self.poll_observed(deadline, &mut None)
    }

    /// Observe each actual workload-query stdout/stderr read incrementally,
    /// after retaining its bounded prefix and overflow fact, before reading
    /// anything else. Observer errors poison this SAME member; they cannot
    /// become completion, accounting or permission to replay. Metadata and
    /// resolver purposes retain their original non-observing API unchanged.
    pub fn poll_with_observer(
        &mut self,
        deadline: Instant,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<MetadataResult>> {
        self.require_workload_observer()?;
        self.poll_observed(deadline, &mut Some(observer))
    }

    fn require_workload_observer(&self) -> io::Result<()> {
        require_workload_observer(&self.request)
    }

    fn poll_observed(
        &mut self,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> io::Result<Option<MetadataResult>> {
        if self.poisoned {
            return Err(invalid("metadata lifecycle is unusable; never replay"));
        }
        let result = self.poll_inner(deadline, observer);
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    fn poll_inner(
        &mut self,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> io::Result<Option<MetadataResult>> {
        match self.streams.poll_inner(&self.request, deadline, observer)? {
            StreamReady::Pending => Ok(None),
            StreamReady::Refused => {
                self.pin.validate(deadline)?;
                self.refusal_finalized = true;
                Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    format!(
                        "metadata member refused before execution: {}",
                        self.streams.state.refused.as_deref().unwrap_or("unknown")
                    ),
                ))
            }
            StreamReady::Completed => {
                self.pin.validate(deadline)?;
                let state = &mut self.streams.state;
                let prepared =
                    state.prepared.take().ok_or_else(|| invalid("missing preparation"))?;
                let started =
                    state.started.take().ok_or_else(|| invalid("missing actual start"))?;
                let completion =
                    state.completed.take().ok_or_else(|| invalid("missing completion"))?;
                self.poisoned = true;
                self.result_delivered = true;
                Ok(Some(MetadataResult {
                    prepared,
                    started,
                    completion,
                    stdout: std::mem::take(&mut self.streams.output.bytes[0]),
                    stderr: std::mem::take(&mut self.streams.output.bytes[1]),
                    output_limit_exceeded: self.streams.output.exceeded,
                }))
            }
        }
    }
}

fn require_workload_observer(request: &NativeQueryRequest) -> io::Result<()> {
    if matches!(
        request,
        NativeQueryRequest::Workload(_)
            | NativeQueryRequest::Paired(_)
            | NativeQueryRequest::NativeJob(_)
            | NativeQueryRequest::Produced(..)
            | NativeQueryRequest::ContainedProduced(..)
            | NativeQueryRequest::Coordinator(..)
    ) {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "incremental output observation requires a distinct workload purpose",
        ))
    }
}

#[derive(Default)]
struct ObservedEvents {
    prefix: Vec<u8>,
    seen: u64,
}
impl ObservedEvents {
    fn record(&mut self, bytes: &[u8]) {
        self.seen = self.seen.saturating_add(bytes.len() as u64);
        let room = METADATA_EVENT_PREFIX_MAX_BYTES.saturating_sub(self.prefix.len());
        self.prefix.extend_from_slice(&bytes[..bytes.len().min(room)]);
    }
}
enum StreamReady {
    Pending,
    Refused,
    Completed,
}
/// Stream observation has no host pin or capacity authority. Only the outer
/// MetadataMember can accept a result after revalidating its original pin.
struct MetadataStreams {
    events: Channel,
    output: Capture,
    state: Lifecycle,
    observed: ObservedEvents,
    cancel_sent: bool,
    // Permanent protocol/capture failure history, independent of a retained
    // earlier terminal. Final diagnostic draining never clears this veto.
    failed: bool,
}
impl MetadataStreams {
    fn cancel(&mut self, request: &impl NativeQuery, deadline: Instant) -> io::Result<()> {
        if self.cancel_sent || self.state.completed.is_some() || self.state.refused.is_some() {
            return Ok(());
        }
        self.cancel_sent = true;
        // The handshake connection closes after attachment. Cancellation uses
        // the SAME bidirectional event endpoint retained by the actual host.
        self.events.send(
            &Cancel {
                root_attempt: request.member().binding.root_attempt,
                member_attempt: request.member().member_attempt,
            }
            .encode()?,
            deadline,
        )
    }

    #[cfg(test)]
    fn poll(&mut self, request: &impl NativeQuery, deadline: Instant) -> io::Result<StreamReady> {
        self.poll_inner(request, deadline, &mut None)
    }

    fn poll_inner(
        &mut self,
        request: &impl NativeQuery,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> io::Result<StreamReady> {
        self.poll_started(request, deadline, observer, Instant::now())
    }

    #[cfg(test)]
    fn poll_at(
        &mut self,
        request: &impl NativeQuery,
        deadline: Instant,
        started: Instant,
    ) -> io::Result<StreamReady> {
        self.poll_started(request, deadline, &mut None, started)
    }

    fn poll_started(
        &mut self,
        request: &impl NativeQuery,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
        started: Instant,
    ) -> io::Result<StreamReady> {
        if self.failed {
            return Err(invalid("native stream has an earlier protocol/capture failure"));
        }
        let outcome = self.poll_checked(request, deadline, observer, started);
        if outcome.is_err() {
            self.failed = true;
        }
        outcome
    }

    fn poll_checked(
        &mut self,
        request: &impl NativeQuery,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
        started: Instant,
    ) -> io::Result<StreamReady> {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        self.output.drain_observed(observer)?;
        if self.output.exceeded {
            self.cancel(request, deadline)?;
        }
        // Bound one call even if a peer continuously emits complete frames.
        for _ in 0..8 {
            if !self.events.ready_to_receive()? {
                break;
            }
            if self.events.at_eof()? {
                if self.state.completed.is_none() && self.state.refused.is_none() {
                    return Err(invalid("metadata event stream closed before retirement"));
                }
                break;
            }
            let frame_deadline = deadline.min(started + Duration::from_secs(60));
            let observed = &mut self.observed;
            let bytes =
                self.events.receive_observed(frame_deadline, |bytes| observed.record(bytes))?;
            let root = request.member().binding.root_attempt;
            let member = request.member().member_attempt;
            if let Some(loan) = request.linker()
                && crate::wire::header(&bytes, crate::linker::PREPARED_TAG).is_ok()
            {
                self.state.accept_linker(crate::linker::Prepared::decode(&bytes, loan)?)?;
                continue;
            }
            if let Some(coordinator) = request.coordinator()
                && crate::wire::header(&bytes, 85).is_ok()
            {
                let prepared =
                    crate::workload::host::coordinator::Prepared::decode(&bytes, coordinator)?;
                self.state.accept_produced(prepared.produced.clone())?;
                self.state.coordinator_prepared = Some(prepared);
                continue;
            }
            if let Some(prepared) = request.produced_prepared(&bytes)? {
                self.state.accept_produced(prepared)?;
                continue;
            }
            let event = if let Some(loan) = request.linker() {
                if let Ok(completion) = crate::linker::Completion::decode(&bytes, loan) {
                    self.state.accounting = Some(completion.observation);
                    self.state.linker_completed = Some(completion.clone());
                    MetadataEvent::Completed(completion.completed)
                } else {
                    let event = MetadataEvent::decode(&bytes, root, member)?;
                    if matches!(event, MetadataEvent::Completed(_) | MetadataEvent::Prepared(_)) {
                        return Err(invalid(
                            "linker loan requires distinct preparation/retirement",
                        ));
                    }
                    event
                }
            } else if let Some(query) = request.paired_query() {
                use sha2::{Digest, Sha256};

                use crate::paired_qualification::query::Completion;
                let expected: [u8; 32] =
                    Sha256::digest(query.invocation.binding_preimage()?).into();
                if let Ok(completion) = Completion::decode(&bytes, query, expected) {
                    self.state.accounting = Some(completion.observation);
                    self.state.paired = Some(completion.clone());
                    MetadataEvent::Completed(completion.completed)
                } else {
                    let event = MetadataEvent::decode(&bytes, root, member)?;
                    if matches!(event, MetadataEvent::Completed(_)) {
                        return Err(invalid("paired query requires full60-bound55/v2 retirement"));
                    }
                    event
                }
            } else if let Some(query) = request.native_job_query() {
                use crate::native_job::query::Completion;
                let expected: [u8; 32] = query.plan_sha256;
                if let Ok(completion) = Completion::decode(&bytes, query, expected) {
                    self.state.accounting = Some(completion.observation);
                    self.state.native_job = Some(completion.clone());
                    MetadataEvent::Completed(completion.completed)
                } else {
                    let event = MetadataEvent::decode(&bytes, root, member)?;
                    if matches!(event, MetadataEvent::Completed(_)) {
                        return Err(invalid(
                            "native job query requires full106-bound55/v3 retirement",
                        ));
                    }
                    event
                }
            } else if let Some(request) = request.contained() {
                use sha2::{Digest, Sha256};
                let expected: [u8; 32] = Sha256::digest(request.binding_preimage()?).into();
                match crate::workload::host::contained::Completion::decode(
                    &bytes, request, expected,
                ) {
                    Ok(completion) => {
                        self.state.accounting = Some(completion.completion.observation);
                        self.state.workload = Some(completion.completion.clone());
                        let event =
                            MetadataEvent::Completed(completion.completion.completed.clone());
                        self.state.contained = Some(completion);
                        event
                    }
                    Err(_) => {
                        let event = MetadataEvent::decode(&bytes, root, member)?;
                        if matches!(event, MetadataEvent::Completed(_)) {
                            return Err(invalid(
                                "contained operation requires its own native retirement",
                            ));
                        }
                        event
                    }
                }
            } else if let Some((phase, kind)) = request.workload_completion() {
                use crate::workload::host::Completion;
                if let Ok(completion) = Completion::decode(&bytes, root, member) {
                    if completion.phase != phase || completion.kind != kind {
                        return Err(invalid("workload completion purpose or phase differs"));
                    }
                    self.state.accounting = Some(completion.observation);
                    self.state.workload = Some(completion.clone());
                    MetadataEvent::Completed(completion.completed)
                } else {
                    let event = MetadataEvent::decode(&bytes, root, member)?;
                    if matches!(event, MetadataEvent::Completed(_)) {
                        return Err(invalid(
                            "workload member requires original owning-wait accounting",
                        ));
                    }
                    event
                }
            } else {
                MetadataEvent::decode(&bytes, root, member)?
            };
            self.state.accept(event, request)?;
        }
        if self.state.refused.is_some() {
            self.output.drain_observed(observer)?;
            if !self.output.eof.iter().all(|eof| *eof) || !self.events.at_eof()? {
                return Ok(StreamReady::Pending);
            }
            return Ok(StreamReady::Refused);
        }
        if self.state.completed.is_some() {
            self.output.drain_observed(observer)?;
            if !self.output.eof.iter().all(|eof| *eof) || !self.events.at_eof()? {
                return Ok(StreamReady::Pending);
            }
            return Ok(StreamReady::Completed);
        }
        Ok(StreamReady::Pending)
    }
    #[cfg(test)]
    fn take_failure_observation(
        &mut self,
        request: &impl NativeQuery,
    ) -> MetadataFailureObservation {
        self.take_failure_observation_inner(request, &mut None)
    }

    fn take_failure_observation_inner(
        &mut self,
        request: &impl NativeQuery,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> MetadataFailureObservation {
        let capture_error = self.output.drain_observed(observer).err().map(|e| e.to_string());
        MetadataFailureObservation {
            root_attempt: request.member().binding.root_attempt,
            member_attempt: request.member().member_attempt,
            stdout: std::mem::take(&mut self.output.bytes[0]),
            stderr: std::mem::take(&mut self.output.bytes[1]),
            stdout_eof: self.output.eof[0],
            stderr_eof: self.output.eof[1],
            output_limit_exceeded: self.output.exceeded,
            event_prefix: std::mem::take(&mut self.observed.prefix),
            event_bytes_seen: self.observed.seen,
            capture_error,
        }
    }
}

#[derive(Default)]
struct Lifecycle {
    attached: bool,
    prepared: Option<MetadataPrepared>,
    produced: Option<crate::workload::host::produced::ProducedPrepared>,
    coordinator_prepared: Option<crate::workload::host::coordinator::Prepared>,
    linker: Option<crate::linker::Prepared>,
    linker_completed: Option<crate::linker::Completion>,
    started: Option<Started>,
    completed: Option<MetadataCompletion>,
    refused: Option<String>,
    // Retain the exact authenticated binding/status independently of a poll
    // io error. ErrorKind alone must never establish positive refusal.
    refused_frame: Option<StatusFrame>,
    accounting: Option<crate::accounting::Observation>,
    workload: Option<crate::workload::host::Completion>,
    paired: Option<crate::paired_qualification::query::Completion>,
    native_job: Option<crate::native_job::query::Completion>,
    contained: Option<crate::workload::host::contained::Completion>,
}
impl Lifecycle {
    fn accept_linker(&mut self, prepared: crate::linker::Prepared) -> io::Result<()> {
        let (host, boot) = process::host_boot()?;
        if !self.attached
            || self.prepared.is_some()
            || self.produced.is_some()
            || self.linker.is_some()
            || self.started.is_some()
            || self.completed.is_some()
            || self.refused.is_some()
            || prepared.host != host
            || prepared.boot != boot
            || prepared.policy != program::RUNTIME_POLICY
            || prepared.scope != program::INPUT_SCOPE
        {
            return Err(invalid("linker preparation ordering or original input profile differs"));
        }
        self.linker = Some(prepared);
        Ok(())
    }
    fn accept_produced(
        &mut self,
        prepared: crate::workload::host::produced::ProducedPrepared,
    ) -> io::Result<()> {
        let (host, boot) = process::host_boot()?;
        if !self.attached
            || self.prepared.is_some()
            || self.produced.is_some()
            || self.linker.is_some()
            || self.started.is_some()
            || self.completed.is_some()
            || self.refused.is_some()
            || prepared.host != host
            || prepared.boot != boot
        {
            return Err(invalid("produced preparation ordering or original host differs"));
        }
        self.produced = Some(prepared);
        Ok(())
    }
    fn accept(&mut self, event: MetadataEvent, request: &impl NativeQuery) -> io::Result<()> {
        if self.completed.is_some() || self.refused.is_some() {
            return Err(invalid("event after metadata terminal"));
        }
        match event {
            MetadataEvent::Prepared(prepared) => {
                request.validate_prepared(&prepared)?;
                let (host, boot) = process::host_boot()?;
                if !self.attached
                    || self.prepared.is_some()
                    || self.produced.is_some()
                    || self.linker.is_some()
                    || self.started.is_some()
                    || prepared.policy != program::RUNTIME_POLICY
                    || prepared.scope != program::INPUT_SCOPE
                    || prepared.host != host
                    || prepared.boot != boot
                {
                    return Err(invalid("metadata preparation ordering or input policy mismatch"));
                }
                self.prepared = Some(prepared);
            }
            MetadataEvent::Status(frame) => match frame.status {
                Status::Attached
                    if !self.attached
                        && self.prepared.is_none()
                        && self.produced.is_none()
                        && self.linker.is_none() =>
                {
                    self.attached = true
                }
                Status::Started(started)
                    if self.attached
                        && (self.prepared.is_some()
                            || self.produced.is_some()
                            || self.linker.is_some())
                        && self.started.is_none() =>
                {
                    if self
                        .produced
                        .as_ref()
                        .is_some_and(|prepared| prepared.identity != started.identity)
                    {
                        return Err(invalid(
                            "produced Started is not its original suspended child",
                        ));
                    }
                    if self.linker.as_ref().is_some_and(|p| p.identity != started.identity) {
                        return Err(invalid(
                            "linker Started differs from original suspended child",
                        ));
                    }
                    self.started = Some(started)
                }
                Status::Refused { ref reason } if self.started.is_none() => {
                    self.refused = Some(reason.clone());
                    self.refused_frame = Some(frame);
                }
                _ => {
                    return Err(invalid(
                        "metadata lifecycle missing, duplicate, unknown or contradictory",
                    ));
                }
            },
            MetadataEvent::Completed(completion) => {
                if self.started.is_none() {
                    return Err(invalid("metadata completion without actual start"));
                }
                self.completed = Some(completion);
            }
        }
        Ok(())
    }
}

struct Capture {
    pipes: [std::io::PipeReader; 2],
    bytes: [Vec<u8>; 2],
    eof: [bool; 2],
    exceeded: bool,
    observer_failed: bool,
    limit: usize,
}
impl Capture {
    #[cfg(test)]
    fn new() -> io::Result<(Self, std::io::PipeWriter, std::io::PipeWriter)> {
        Self::with_limit(METADATA_MAX_OUTPUT)
    }
    fn with_limit(limit: usize) -> io::Result<(Self, std::io::PipeWriter, std::io::PipeWriter)> {
        if !matches!(
            limit,
            METADATA_MAX_OUTPUT
                | crate::workload::host::produced::MAX_OUTPUT_BYTES
                | crate::linker::MAX_OUTPUT
        ) {
            return Err(invalid("unsupported native capture profile"));
        }
        let (stdout, target_stdout) = io::pipe()?;
        let (stderr, target_stderr) = io::pipe()?;
        for pipe in [&stdout, &stderr] {
            // SAFETY: exclusively owned new read endpoint; preserve all flags.
            let flags = unsafe { libc::fcntl(pipe.as_raw_fd(), libc::F_GETFL) };
            if flags < 0
                || unsafe { libc::fcntl(pipe.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) }
                    < 0
            {
                return Err(io::Error::last_os_error());
            }
        }
        Ok((
            Self {
                pipes: [stdout, stderr],
                bytes: Default::default(),
                eof: [false; 2],
                exceeded: false,
                observer_failed: false,
                limit,
            },
            target_stdout,
            target_stderr,
        ))
    }
    #[cfg(test)]
    fn drain(&mut self) -> io::Result<()> {
        self.drain_observed(&mut None)
    }

    fn drain_observed(&mut self, observer: &mut Option<&mut OutputObserver<'_>>) -> io::Result<()> {
        if self.observer_failed {
            return Err(io::Error::other(
                "workload output observer failed; retained stream prefix is incomplete",
            ));
        }
        let mut buffer = [0; 4096];
        for index in 0..2 {
            for _ in 0..16 {
                match self.pipes[index].read(&mut buffer) {
                    Ok(0) => {
                        self.eof[index] = true;
                        break;
                    }
                    Ok(count) => {
                        let available =
                            self.limit.saturating_sub(self.bytes[0].len() + self.bytes[1].len());
                        self.bytes[index].extend_from_slice(&buffer[..count.min(available)]);
                        self.exceeded |= count > available;
                        if let Some(observer) = observer.as_mut() {
                            let stream = match index {
                                0 => MetadataOutputStream::Stdout,
                                _ => MetadataOutputStream::Stderr,
                            };
                            // Arm before calling user code: even a caught
                            // unwind cannot resume reads or complete capture.
                            self.observer_failed = true;
                            observer(stream, &buffer[..count])?;
                            self.observer_failed = false;
                        }
                    }
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(error),
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
