//! SAME original fixed Root graph connection. These owners supply neither a
//! producing launch nor protected-scope retirement/release. Those require a
//! separately qualified actual Host operation, not support/enrollment DATA.
use std::io;
use std::mem::ManuallyDrop;
use std::os::fd::BorrowedFd;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_provenance::{Host, PinnedHelper};

use super::{Client, Delivery};
use crate::bootstrap_graph::{
    Enrollment, EnrollmentReply, Key, OutputAttachment, OutputReply, SourceAttachment, SourceReply,
    SupportQuery, SupportReply, transport,
};
use crate::{Channel, ContextReply};

mod compilation;
mod configuration;
mod materialization;
pub use compilation::{
    BootstrapMemberFailure, ClosedLinker, CompilerAdoptionFailure, CompilerLinkerFailure,
    CompilerMember, PairedLinkerLoan, RefusedCompilationAdvance, RefusedCompilationClose,
    ResidentBootstrapCompilation, ResidentBootstrapMember, RetiredBootstrapMember, UnlentLinker,
};
mod object;
mod offline_preparation;
mod preparation;
mod preparation_cache;
mod preparation_output;
mod preparation_source;
mod query;
pub use preparation::{InputWorkClosed, ResidentDependencyInputs};
mod store;
pub use object::{CompletedObjectCompile, ObjectFailure, ObjectObservation};
pub use query::{
    CompletedSdkQuery, QueryFailure, QueryObservation, observe_resident_query_channel,
};
pub use store::{EarlyHostStore, PendingHostStore, capture_host_store, snapshot_host_store};

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn finish<T>(deadline: Instant, actual: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    time(deadline)?;
    let value = actual()?;
    time(deadline)?;
    Ok(value)
}
fn live(context: &ContextReply, deadline: Instant) -> io::Result<()> {
    finish(deadline, || {
        super::workload::live_context(&context.context, None)?;
        super::sdk::validate_sdk_keeper(&context.context)
    })
}
fn bounded(original: Instant, requested: Instant) -> io::Result<()> {
    if requested > original {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "cannot extend original graph deadline",
        ));
    }
    time(requested)
}
fn original_deadline(started: Instant, remaining: u64) -> io::Result<Instant> {
    if remaining == 0 {
        return Err(io::ErrorKind::TimedOut.into());
    }
    let deadline = started
        .checked_add(Duration::from_nanos(remaining))
        .ok_or_else(|| io::Error::other("original graph deadline is unrepresentable"))?;
    time(deadline)?;
    Ok(deadline)
}

/// A completed short-lived support observation, initially unreserved. The
/// distinct offline intent may restrict it before enrollment. Its private
/// constructor anchors the original bound before the actual support request.
pub struct BootstrapGraphSupport {
    key: Key,
    context: ContextReply,
    deadline: Instant,
    pin: Arc<PinnedHelper>,
    queries: QueryState,
    offline_intent: Option<offline_preparation::IntentAttempt>,
    offline_staged: Option<offline_preparation::StagedAttempt>,
}
// Restriction only: no counter or branch grants the Host a borrower. Set the
// active state BEFORE connect; only a genuine same-operation opaque completion
// clears it. Errors and unwinds have no ordinary clear/recovery path.
struct QueryState {
    next: u64,
    active: Option<u64>,
    offline_reserved: bool,
}
impl QueryState {
    fn new() -> Self {
        Self { next: 1, active: None, offline_reserved: false }
    }
    fn check(&self, sequence: u64) -> io::Result<()> {
        if self.offline_reserved || self.active.is_some() || self.next != sequence {
            return Err(crate::wire::invalid());
        }
        Ok(())
    }
    fn begin(&mut self) -> io::Result<()> {
        self.check(self.next)?;
        let next = self.next.checked_add(1).ok_or_else(crate::wire::invalid)?;
        self.active = Some(self.next);
        self.next = next;
        Ok(())
    }
    fn reserve_offline(&mut self) -> io::Result<()> {
        self.check(1)?;
        // This is a restriction beside the original support, not a completed
        // query. No carrier ACK or ordinary completion clears it.
        self.offline_reserved = true;
        Ok(())
    }
    fn completed(&mut self, original: &CompletedSdkQuery) -> io::Result<()> {
        if self.active != Some(original.request().key.sequence) {
            return Err(crate::wire::invalid());
        }
        self.active = None;
        Ok(())
    }
    fn completed_object(&mut self, original: &CompletedObjectCompile) -> io::Result<()> {
        if self.active != Some(original.request().key.sequence) {
            return Err(crate::wire::invalid());
        }
        self.active = None;
        Ok(())
    }
    fn enrollment_allowed(&self) -> io::Result<()> {
        if self.active.is_some() {
            return Err(io::Error::other("original SDK query remains unresolved"));
        }
        Ok(())
    }
    fn enrollment_connect<T>(&self, connect: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
        self.enrollment_allowed()?;
        connect()
    }
}
impl BootstrapGraphSupport {
    /// Original binding observation, not a constructor for graph/Root custody.
    pub fn key(&self) -> &Key {
        &self.key
    }
    pub fn observation(&self) -> &ContextReply {
        &self.context
    }
    /// Restriction only. This is not CPU, GNU or protected-scope authority.
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }
}

struct Connection {
    request: Enrollment,
    context: ContextReply,
    deadline: Instant,
    queries: QueryState,
    offline_intent: Option<offline_preparation::IntentAttempt>,
    offline_staged: Option<offline_preparation::StagedAttempt>,
    // Preserve the actual accepted boundary even on an unwind between typed
    // wrappers. Only a future consuming native closure path may dispose it.
    channel: ManuallyDrop<Channel>,
    original: ManuallyDrop<Host>,
    pin: ManuallyDrop<Arc<PinnedHelper>>,
}
impl Connection {
    fn check(&self, deadline: Instant) -> io::Result<()> {
        bounded(self.deadline, deadline)?;
        if let Some(intent) = &self.offline_intent {
            intent.enrolled(&self.request, &self.queries, deadline)?;
        }
        if let Some(intent) = &self.offline_staged {
            intent.enrolled(&self.request, &self.queries, deadline)?;
        }
        finish(deadline, || {
            self.original.revalidate(deadline)?;
            self.pin.validate(deadline)?;
            live(&self.context, deadline)
        })
    }
}

/// Owns the actual accepted connection across uncertain delivery. There is no
/// recover/replay/release method, nor a constructor from an error kind/frame.
/// Delivery describes this operation only: an attachment preflight can be
/// BeforeRequest while still retaining an already enrolled original graph.
pub struct GraphFailure {
    delivery: Delivery,
    error: io::Error,
    original: Option<Box<Connection>>,
}
impl GraphFailure {
    pub fn delivery(&self) -> Delivery {
        self.delivery
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    fn before(error: io::Error) -> Self {
        Self { delivery: Delivery::BeforeRequest, error, original: None }
    }
    fn retaining(original: Connection, delivery: Delivery, error: io::Error) -> Self {
        Self { delivery, error, original: Some(Box::new(original)) }
    }
}
impl std::fmt::Debug for GraphFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GraphFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for GraphFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original Bootstrap graph {:?}: {}", self.delivery, self.error)
    }
}
impl std::error::Error for GraphFailure {}
impl Drop for GraphFailure {
    fn drop(&mut self) {
        // An abandoned failure must not masquerade as graph closure. The Host
        // independently retains actual inputs/resources to original settlement.
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
    }
}

pub struct EnrolledBootstrapGraph {
    original: Option<Connection>,
}
pub struct SourceBoundBootstrapGraph {
    original: Option<Connection>,
    source: SourceAttachment,
    configuration: Vec<crate::bootstrap_graph::ConfigurationAttachment>,
    configuration_budget: crate::bootstrap_graph::configuration::ConfigurationBudget,
    materialization: Option<materialization::PreparedContents>,
    preparation_output: Option<preparation_output::Attempt>,
    preparation_output_started: bool,
    preparation_cache: Option<preparation_cache::Attempt>,
    preparation_source: Option<preparation_source::Attempt>,
}
pub struct OutputBoundBootstrapGraph {
    original: Option<Connection>,
    source: SourceAttachment,
    output: OutputAttachment,
    configuration: Vec<crate::bootstrap_graph::ConfigurationAttachment>,
    materialization: Option<materialization::PreparedContents>,
    preparation: Option<preparation::Attempt>,
}
impl EnrolledBootstrapGraph {
    /// Observation of this actual accepted enrollment, never a constructor.
    pub fn enrollment(&self) -> &Enrollment {
        &self.original.as_ref().expect("private original enrolled graph").request
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        let original =
            self.original.as_ref().ok_or_else(|| io::Error::other("original graph consumed"))?;
        original.queries.enrollment_allowed()?;
        original.check(deadline)
    }
}
impl Drop for EnrolledBootstrapGraph {
    fn drop(&mut self) {
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
    }
}
impl Drop for OutputBoundBootstrapGraph {
    fn drop(&mut self) {
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
    }
}
impl Drop for SourceBoundBootstrapGraph {
    fn drop(&mut self) {
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
    }
}
impl SourceBoundBootstrapGraph {
    pub fn enrollment(&self) -> &Enrollment {
        &self.original.as_ref().expect("private original source-bound graph").request
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        if self.preparation_output_started {
            self.preparation_output.as_ref().ok_or_else(crate::wire::invalid)?.check(deadline)?;
        }
        if let Some(cache) = &self.preparation_cache { cache.check(deadline)?; }
        if let Some(source) = &self.preparation_source { source.check(deadline)?; }
        let original =
            self.original.as_ref().ok_or_else(|| io::Error::other("original graph consumed"))?;
        original.queries.enrollment_allowed()?;
        original.check(deadline)
    }
}
impl OutputBoundBootstrapGraph {
    pub fn enrollment(&self) -> &Enrollment {
        &self.original.as_ref().expect("private original graph").request
    }
    pub fn output(&self) -> &OutputAttachment {
        &self.output
    }
    pub fn original_deadline(&self) -> Instant {
        self.original.as_ref().expect("private original graph").deadline
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        let original =
            self.original.as_ref().ok_or_else(|| io::Error::other("original graph consumed"))?;
        if let Some(attempt) = &self.preparation {
            return attempt.revalidate(original, deadline);
        }
        original.queries.enrollment_allowed()?;
        original.check(deadline)
    }
    // No launch, completion or release API exists until its native counterpart
    // consumes actual operation/retirement owners under this SAME connection.
}

impl Client {
    /// Recheck this exact opaque observation before installing a restrictive
    /// in-process dispatcher. It grants no launch, admission or graph closure.
    pub fn revalidate_bootstrap_graph_support(
        &self,
        support: &BootstrapGraphSupport,
        deadline: Instant,
    ) -> io::Result<()> {
        bounded(support.deadline, deadline)?;
        support.queries.enrollment_allowed()?;
        if let Some(intent) = &support.offline_intent {
            intent.ready(&support.key, &support.queries, deadline)?;
        }
        if let Some(intent) = &support.offline_staged {
            intent.ready(&support.key, &support.queries, deadline)?;
        }
        if !Arc::ptr_eq(&support.pin, &self.host) {
            return Err(crate::wire::invalid());
        }
        finish(deadline, || {
            self.host.validate(deadline)?;
            live(&support.context, deadline)
        })
    }

    pub fn bootstrap_graph_support(
        &self,
        query: &SupportQuery,
        deadline: Instant,
    ) -> Result<BootstrapGraphSupport, GraphFailure> {
        let started = Instant::now();
        let payload = query.encode().map_err(GraphFailure::before)?;
        let hello = query.hello().map_err(GraphFailure::before)?;
        let original = self.host.connect(deadline).map_err(GraphFailure::before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(GraphFailure::before)?)
                .map_err(GraphFailure::before)?;
        let supported = finish(deadline, || {
            original.revalidate(deadline)?;
            channel.send(&hello, deadline)?;
            channel.send(&payload, deadline)?;
            let reply = SupportReply::decode(&channel.receive(deadline)?, query)?;
            crate::runtime_input_retention::transport::require_reply_eof(&mut channel, deadline)?;
            original.revalidate(deadline)?;
            match reply {
                SupportReply::Supported { context, remaining_root_ns, .. } => {
                    let bound = original_deadline(started, remaining_root_ns)?;
                    let final_deadline = deadline.min(bound);
                    live(&context, final_deadline)?;
                    channel.send(&[1], final_deadline)?;
                    original.revalidate(final_deadline)?;
                    self.host.validate(final_deadline)?;
                    let supported = BootstrapGraphSupport {
                        key: query.key.clone(),
                        context: *context,
                        deadline: bound,
                        pin: Arc::clone(&self.host),
                        queries: QueryState::new(),
                        offline_intent: None,
                        offline_staged: None,
                    };
                    time(supported.deadline)?;
                    Ok(supported)
                }
                SupportReply::Refused { reason, .. } => {
                    Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                }
            }
        })
        .map_err(|error| GraphFailure {
            delivery: Delivery::Unknown,
            error,
            original: None,
        })?;
        finish(deadline.min(supported.deadline), || Ok(supported)).map_err(|error| GraphFailure {
            delivery: Delivery::Unknown,
            error,
            original: None,
        })
    }

    /// Retain the SAME original captured GNU owner and actual protected manager
    /// scope throughout this call/graph. This exchange grants neither launch
    /// nor release; Host must validate its actual original fixed Job/resources.
    pub fn enroll_bootstrap_graph(
        &self,
        support: BootstrapGraphSupport,
        request: Enrollment,
        gnu: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<EnrolledBootstrapGraph, GraphFailure> {
        let preflight = || {
            bounded(support.deadline, deadline)?;
            support.queries.enrollment_allowed()?;
            if let Some(intent) = &support.offline_intent {
                intent.enrolled(&request, &support.queries, deadline)?;
            }
            if let Some(intent) = &support.offline_staged {
                intent.enrolled(&request, &support.queries, deadline)?;
            }
            if support.key != request.key || !Arc::ptr_eq(&support.pin, &self.host) {
                return Err(crate::wire::invalid());
            }
            transport::check_gnu(&request, gnu)?;
            live(&support.context, deadline)
        };
        preflight().map_err(GraphFailure::before)?;
        let payload = request.encode().map_err(GraphFailure::before)?;
        let hello = request.hello().map_err(GraphFailure::before)?;
        let digest =
            Sha256::digest(request.binding_preimage().map_err(GraphFailure::before)?).into();
        let original = support
            .queries
            .enrollment_connect(|| self.host.connect(deadline))
            .map_err(GraphFailure::before)?;
        let channel = Channel::new(original.stream().try_clone().map_err(GraphFailure::before)?)
            .map_err(GraphFailure::before)?;
        let mut connection = Connection {
            request,
            context: support.context,
            deadline: support.deadline,
            queries: support.queries,
            offline_intent: support.offline_intent,
            offline_staged: support.offline_staged,
            original: ManuallyDrop::new(original),
            channel: ManuallyDrop::new(channel),
            pin: ManuallyDrop::new(Arc::clone(&self.host)),
        };
        let result = finish(deadline, || {
            connection.check(deadline)?;
            connection.channel.send(&hello, deadline)?;
            connection.channel.send(&payload, deadline)?;
            match EnrollmentReply::decode(
                &connection.channel.receive(deadline)?,
                &connection.request,
                digest,
            )? {
                EnrollmentReply::Prepared { context, .. } if context == connection.context => {}
                EnrollmentReply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            }
            connection.check(deadline)?;
            let original = &connection.original;
            let context = &connection.context;
            transport::send_gnu(
                &mut connection.channel,
                &connection.request,
                gnu,
                deadline,
                || {
                    original.revalidate(deadline)?;
                    live(context, deadline)
                },
            )?;
            match EnrollmentReply::decode(
                &connection.channel.receive(deadline)?,
                &connection.request,
                digest,
            )? {
                EnrollmentReply::Enrolled { context, .. } if context == connection.context => {}
                _ => return Err(crate::wire::invalid()),
            }
            connection.check(deadline)?;
            transport::check_gnu(&connection.request, gnu)
        });
        if let Err(error) = result {
            connection.channel.poison();
            return Err(GraphFailure::retaining(connection, Delivery::Unknown, error));
        }
        let mut owner = EnrolledBootstrapGraph { original: Some(connection) };
        if let Err(error) = time(deadline) {
            return Err(GraphFailure::retaining(
                owner.original.take().expect("same original graph"),
                Delivery::Unknown,
                error,
            ));
        }
        Ok(owner)
    }
}

impl EnrolledBootstrapGraph {
    /// # Safety
    /// The original trusted coordinator must retain an actual
    /// OriginalSourceOffer from the SAME enrolled ProtectedWorkScope before
    /// this call and through every success/failure/unwind/Unknown delivery.
    /// All four supplied descriptions must be that offer's exact original
    /// readonly OFDs. Metadata, hashes and arbitrary opened files cannot
    /// establish this lineage. No release or Manager authority is transferred.
    /// The offer must retain this SAME original Root lifetime. The deadline
    /// argument only restricts this RPC; it cannot supply or extend that owner.
    pub unsafe fn attach_original_source(
        mut self,
        request: SourceAttachment,
        files: &[BorrowedFd<'_>; 4],
        deadline: Instant,
    ) -> Result<SourceBoundBootstrapGraph, GraphFailure> {
        let mut original = self.original.take().expect("private original enrolled graph");
        let preflight = (|| {
            bounded(original.deadline, deadline)?;
            original.queries.enrollment_allowed()?;
            if request.key != original.request.key {
                return Err(crate::wire::invalid());
            }
            transport::check_source(&request, files, deadline)?;
            original.check(deadline)
        })();
        if let Err(error) = preflight {
            return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
        }
        let payload = match request.encode() {
            Ok(payload) => payload,
            Err(error) => {
                return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
            }
        };
        let digest =
            Sha256::digest(request.binding_preimage().expect("same validated source frame")).into();
        let result = finish(deadline, || {
            original.channel.send(&payload, deadline)?;
            match SourceReply::decode(&original.channel.receive(deadline)?, &request, digest)? {
                SourceReply::Prepared { context, .. } if context == original.context => {}
                SourceReply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            }
            original.check(deadline)?;
            let host = &original.original;
            let context = &original.context;
            transport::send_source(&mut original.channel, &request, files, deadline, || {
                host.revalidate(deadline)?;
                live(context, deadline)
            })?;
            match SourceReply::decode(&original.channel.receive(deadline)?, &request, digest)? {
                SourceReply::Attached { context, .. } if context == original.context => {}
                _ => return Err(crate::wire::invalid()),
            }
            original.check(deadline)?;
            transport::check_source(&request, files, deadline)
        });
        if let Err(error) = result {
            original.channel.poison();
            return Err(GraphFailure::retaining(original, Delivery::Unknown, error));
        }
        let mut owner = SourceBoundBootstrapGraph {
            original: Some(original),
            source: request,
            configuration: Vec::new(),
            configuration_budget: Default::default(),
            materialization: None,
            preparation_output: None,
            preparation_output_started: false,
            preparation_cache: None,
            preparation_source: None,
        };
        if let Err(error) = time(deadline) {
            return Err(GraphFailure::retaining(
                owner.original.take().expect("same original graph"),
                Delivery::Unknown,
                error,
            ));
        }
        Ok(owner)
    }
}

impl SourceBoundBootstrapGraph {
    /// # Safety
    /// The trusted original SDK coordinator must lend the SAME actual acquired
    /// OutputLock plus physical output-root description from this engine graph.
    /// The SAME original owned manager guard must already be durably withheld
    /// and bound to its actual pre-work ProtectedWorkScope; borrowed promotion
    /// is forbidden.
    /// Its guard switches to close-only BEFORE any offer and remains held through
    /// actual graph retirement. Paths, hashes and arbitrary opened files cannot
    /// satisfy this lineage contract. No rights may be reconstructed/reacquired.
    pub unsafe fn attach_original_output(
        mut self,
        request: OutputAttachment,
        files: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<OutputBoundBootstrapGraph, GraphFailure> {
        let mut original = self.original.take().expect("private original enrolled graph");
        let preflight = (|| {
            bounded(original.deadline, deadline)?;
            original.queries.enrollment_allowed()?;
            if request.key != original.request.key {
                return Err(crate::wire::invalid());
            }
            if self.preparation_output_started {
                return Err(io::Error::other(
                    "same-OFD configured output transition after early custody is unimplemented",
                ));
            }
            if let Some(materialization) = &self.materialization {
                materialization.check(self.source.source_directory, Some(&request))?;
            }
            transport::check_output(&request, files)?;
            original.check(deadline)
        })();
        if let Err(error) = preflight {
            return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
        }
        let payload = match request.encode() {
            Ok(payload) => payload,
            Err(error) => {
                return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
            }
        };
        let digest =
            Sha256::digest(request.binding_preimage().expect("same validated output frame")).into();
        let result = finish(deadline, || {
            original.channel.send(&payload, deadline)?;
            match OutputReply::decode(&original.channel.receive(deadline)?, &request, digest)? {
                OutputReply::Prepared { context, .. } if context == original.context => {}
                OutputReply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            }
            original.check(deadline)?;
            let host = &original.original;
            let context = &original.context;
            transport::send_output(&mut original.channel, &request, files, deadline, || {
                host.revalidate(deadline)?;
                live(context, deadline)
            })?;
            match OutputReply::decode(&original.channel.receive(deadline)?, &request, digest)? {
                OutputReply::Attached { context, .. } if context == original.context => {}
                _ => return Err(crate::wire::invalid()),
            }
            original.check(deadline)?;
            transport::check_output(&request, files)
        });
        if let Err(error) = result {
            original.channel.poison();
            return Err(GraphFailure::retaining(original, Delivery::Unknown, error));
        }
        let mut owner = OutputBoundBootstrapGraph {
            original: Some(original),
            source: self.source.clone(),
            output: request,
            configuration: std::mem::take(&mut self.configuration),
            materialization: self.materialization.take(),
            preparation: None,
        };
        if let Err(error) = time(deadline) {
            return Err(GraphFailure::retaining(
                owner.original.take().expect("same original graph"),
                Delivery::Unknown,
                error,
            ));
        }
        Ok(owner)
    }
}

#[cfg(test)]
mod tests;
