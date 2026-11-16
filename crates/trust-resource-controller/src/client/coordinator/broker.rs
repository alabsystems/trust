// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual original parent endpoint; the relayed result is observation DATA.
//! Compiler admission/retirement and independent semantic/proof validation
//! remain owned by the trusted parent and native Host, outside this protocol.
use std::os::fd::AsFd as _;
use std::os::unix::net::UnixStream;
use std::time::Duration;

use trust_resource_provenance::program::HeldProgram;

use super::*;
use crate::workload::host::coordinator::{
    BrokerCaptureData, BrokerEvent, BrokerLimits, BrokerRequest, PublicationSelection, StreamEnd,
};

pub struct CoordinatorBroker {
    channel: Channel,
    originals: Arc<CoordinatorOriginals>,
    parent: HeldProgram,
    sequence: u64,
    failed: bool,
    graph_finished: bool,
    // Actual pinned inputs/socket close before the paid envelope returns.
    _descriptors: crate::descriptors::OriginalInputPermit,
}
/// One actual reply from the authenticated original SDK parent, retained
/// with the native original capsule. No public DATA constructor exists.
pub struct PublicationAcknowledgement {
    selection: PublicationSelection,
    operation: [u8; 16],
    _originals: Arc<CoordinatorOriginals>,
}
impl PublicationAcknowledgement {
    pub fn selection(&self) -> &PublicationSelection {
        &self.selection
    }
    pub fn operation(&self) -> [u8; 16] {
        self.operation
    }
}
/// One final whole-graph acknowledgement from the authenticated original
/// parent. No path/hash/status/Boolean constructs this owner.
pub struct GraphAcknowledgement {
    operation: [u8; 16],
    _originals: Arc<CoordinatorOriginals>,
}
impl GraphAcknowledgement {
    pub fn operation(&self) -> [u8; 16] {
        self.operation
    }
}
fn same_local_member(
    local: &crate::workload::host::publication::Key,
    member: &(crate::workload::host::produced::Key, [u8; 16]),
) -> bool {
    local.root_attempt == member.0.root_attempt
        && local.invocation_sha256 == member.0.invocation_sha256
        && local.phase == member.0.phase
        && local.ordinal == member.0.ordinal
        && local.coordinator == member.1
}
fn same_publication_binding(
    expected: &PublicationSelection,
    selected: &PublicationSelection,
    local: &crate::workload::host::publication::Key,
    member: &(crate::workload::host::produced::Key, [u8; 16]),
) -> bool {
    expected == selected && same_local_member(local, member)
}
#[cfg(test)]
mod publication_binding_tests {
    use super::*;
    #[test]
    fn publication_binding_rejects_shared_destinations_with_foreign_unit_or_member() {
        // Equality DATA only. These observations cannot construct any actual
        // native member, local completion, PublishedUnit or acknowledgement.
        let selection = PublicationSelection {
            unit_sha256: "a".repeat(64),
            unit_id: "original-data".into(),
            destinations: vec![b"/selected/debug/bin".to_vec()],
        };
        let member = (
            crate::workload::host::produced::Key {
                root_attempt: [1; 16],
                invocation_sha256: [2; 32],
                phase: [3; 16],
                ordinal: 4,
                output: [5; 16],
            },
            [6; 16],
        );
        let local = crate::workload::host::publication::Key {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            sequence: 1,
            phase: [3; 16],
            ordinal: 4,
            coordinator: [6; 16],
            operation: [7; 16],
        };
        assert!(same_publication_binding(&selection, &selection, &local, &member));
        for alteration in 0..7 {
            let mut expected = selection.clone();
            let mut changed = local;
            match alteration {
                0 => expected.unit_sha256 = "b".repeat(64),
                1 => expected.unit_id.push('x'),
                2 => changed.root_attempt = [8; 16],
                3 => changed.invocation_sha256 = [8; 32],
                4 => changed.phase = [8; 16],
                5 => changed.ordinal += 1,
                6 => changed.coordinator = [8; 16],
                _ => unreachable!(),
            }
            assert!(
                !same_publication_binding(&expected, &selection, &changed, &member),
                "alteration {alteration}"
            );
        }
    }
}
pub struct CoordinatorCompilerCapture {
    observation: BrokerCaptureData,
    _originals: Arc<CoordinatorOriginals>,
}
impl CoordinatorCompilerCapture {
    pub fn started(&self) -> bool {
        self.observation.started
    }
    pub fn status(&self) -> Option<&crate::StatusFrame> {
        self.observation.status.as_ref()
    }
    pub fn accounting(&self) -> &crate::accounting::Observation {
        &self.observation.accounting
    }
    pub fn stdout(&self) -> &[u8] {
        &self.observation.stdout
    }
    pub fn stderr(&self) -> &[u8] {
        &self.observation.stderr
    }
    pub fn stdout_end(&self) -> StreamEnd {
        self.observation.stdout_end
    }
    pub fn stderr_end(&self) -> StreamEnd {
        self.observation.stderr_end
    }
    pub fn truncated(&self) -> bool {
        self.observation.truncated
    }
    pub fn failure(&self) -> Option<&str> {
        self.observation.failure.as_deref()
    }
    pub fn elapsed_ns(&self) -> u64 {
        self.observation.elapsed_ns
    }
    pub fn into_observation(self) -> BrokerCaptureData {
        self.observation
    }
}
fn parent_peer(channel: &Channel, expected: u32) -> io::Result<()> {
    #[cfg(target_os = "macos")]
    {
        let mut pid: libc::pid_t = 0;
        let mut length = std::mem::size_of_val(&pid) as libc::socklen_t;
        // SAFETY: live original socket and correctly sized native output.
        if unsafe {
            libc::getsockopt(
                channel.as_fd().as_raw_fd(),
                libc::SOL_LOCAL,
                libc::LOCAL_PEERPID,
                (&mut pid as *mut libc::pid_t).cast(),
                &mut length,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        if length as usize != std::mem::size_of_val(&pid)
            || u32::try_from(pid).ok() != Some(expected)
        {
            return Err(refused());
        }
    }
    #[cfg(target_os = "linux")]
    {
        let mut cred = std::mem::MaybeUninit::<libc::ucred>::uninit();
        let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        // SAFETY: live original socket and one correctly sized native ucred.
        if unsafe {
            libc::getsockopt(
                channel.as_fd().as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                cred.as_mut_ptr().cast(),
                &mut length,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        if length as usize != std::mem::size_of::<libc::ucred>() {
            return Err(refused());
        }
        let cred = unsafe { cred.assume_init() };
        if u32::try_from(cred.pid).ok() != Some(expected) || cred.uid != unsafe { libc::geteuid() }
        {
            return Err(refused());
        }
    }
    Ok(())
}
impl CoordinatorOriginals {
    pub fn broker(
        self: &Arc<Self>,
        budget: &Arc<crate::descriptors::DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<CoordinatorBroker> {
        self.validate(deadline)?;
        if self.broker_taken.swap(true, Ordering::AcqRel) {
            return Err(refused());
        }
        // The native owner's bound includes its original ancestor/loader
        // directories as well as image files. Counting runtime images alone
        // undercharges capture before the actual originals have materialized.
        let count = HeldProgram::capture_descriptor_bound()?.checked_add(1).ok_or_else(refused)?;
        let descriptors = budget.reserve_original_inputs(count)?;
        let channel = Channel::new(UnixStream::from(self.broker.try_clone()?))?;
        let root = &self.reply.context.context.original_root;
        parent_peer(&channel, root.pid)?;
        let hash = self.reply.parent_program.sha256;
        let parent = HeldProgram::open(
            std::path::Path::new(std::ffi::OsStr::from_bytes(&self.reply.plan.sdk_root)),
            std::path::Path::new(std::ffi::OsStr::from_bytes(&self.reply.parent_program.path)),
            &hash,
            deadline,
        )?;
        let broker = CoordinatorBroker {
            channel,
            originals: Arc::clone(self),
            parent,
            sequence: 0,
            failed: false,
            graph_finished: false,
            _descriptors: descriptors,
        };
        broker.validate(deadline)?;
        Ok(broker)
    }
}
impl CoordinatorBroker {
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.originals.validate(deadline)?;
        let expected = self.originals.observation().context.context.original_root;
        parent_peer(&self.channel, expected.pid)?;
        let actual = process::read_identity(expected.pid)?;
        if actual.birth != expected.birth {
            return Err(refused());
        }
        self.parent.validate_loaded(actual, deadline)
    }
    pub fn publish(
        &mut self,
        selection: PublicationSelection,
        deadline: Instant,
    ) -> io::Result<PublicationAcknowledgement> {
        if self.failed || self.graph_finished {
            return Err(refused());
        }
        self.validate(deadline)?;
        selection.validate()?;
        let sequence = self.sequence.checked_add(1).ok_or_else(refused)?;
        let request = BrokerRequest::Publish { sequence, selection: selection.clone() };
        let bytes = request.encode()?;
        self.failed = true;
        self.sequence = sequence;
        let result = (|| {
            self.channel.send(&bytes, deadline)?;
            let event = BrokerEvent::decode(&self.channel.receive(deadline)?)?;
            self.validate(deadline)?;
            let BrokerEvent::Published { sequence: got, selection: actual, operation, failure } =
                event
            else {
                return Err(refused());
            };
            if got != sequence || actual != selection {
                return Err(refused());
            }
            if let Some(reason) = failure {
                return Err(io::Error::other(reason));
            }
            Ok(PublicationAcknowledgement {
                selection,
                operation,
                _originals: self.originals.clone(),
            })
        })();
        if result.is_ok() {
            self.failed = false;
        } else {
            self.originals.failed.store(true, Ordering::Release);
        }
        result
    }
    pub fn finish_graph(&mut self, deadline: Instant) -> io::Result<GraphAcknowledgement> {
        if self.failed || self.graph_finished {
            return Err(refused());
        }
        self.validate(deadline)?;
        let sequence = self.sequence.checked_add(1).ok_or_else(refused)?;
        let bytes = BrokerRequest::FinishGraph { sequence }.encode()?;
        self.failed = true;
        self.sequence = sequence;
        let result = (|| {
            self.channel.send(&bytes, deadline)?;
            let event = BrokerEvent::decode(&self.channel.receive(deadline)?)?;
            self.validate(deadline)?;
            let BrokerEvent::GraphFinished { sequence: got, operation, failure } = event else {
                return Err(refused());
            };
            if got != sequence {
                return Err(refused());
            }
            if let Some(reason) = failure {
                return Err(io::Error::other(reason));
            }
            Ok(GraphAcknowledgement { operation, _originals: self.originals.clone() })
        })();
        if result.is_ok() {
            self.graph_finished = true;
            self.failed = false;
        } else {
            self.originals.failed.store(true, Ordering::Release);
        }
        result
    }
    pub fn execute(
        &mut self,
        command: &crate::CommandSpec,
        limits: BrokerLimits,
        deadline: Instant,
        cancel: &mut dyn FnMut() -> bool,
    ) -> io::Result<CoordinatorCompilerCapture> {
        if self.failed || self.graph_finished {
            return Err(refused());
        }
        self.validate(deadline)?;
        limits.validate()?;
        if limits.timeout_ns > self.originals.reply.plan.timeout_ns {
            return Err(refused());
        }
        let sequence = self.sequence.checked_add(1).ok_or_else(refused)?;
        let payload = BrokerRequest::encode_execute(sequence, command, limits)?;
        // Before this line errors are positive BeforeRequest. After it even a
        // partial send is Unknown; preserve every actual received prefix and
        // observed start, never relabel a missing terminal as no launch.
        self.failed = true;
        self.sequence = sequence;
        let mut capture = BrokerCaptureData {
            started: false,
            status: None,
            accounting: crate::accounting::Observation::uncollected(),
            stdout: Vec::new(),
            stderr: Vec::new(),
            stdout_end: StreamEnd::Pending,
            stderr_end: StreamEnd::Pending,
            truncated: false,
            failure: None,
            elapsed_ns: 0,
        };
        let mut saw_started = false;
        let result = (|| {
            self.channel.send(&payload, deadline)?;
            let mut cancelled = false;
            loop {
                self.validate(deadline)?;
                if !cancelled && cancel() {
                    self.channel.send(&BrokerRequest::Cancel { sequence }.encode()?, deadline)?;
                    cancelled = true;
                }
                if !self.channel.ready_to_receive()? {
                    if self.channel.at_eof()? {
                        return Err(io::Error::from(io::ErrorKind::UnexpectedEof));
                    }
                    std::thread::sleep(Duration::from_millis(1));
                    continue;
                }
                match BrokerEvent::decode(&self.channel.receive(deadline)?)? {
                    BrokerEvent::Published { .. } | BrokerEvent::GraphFinished { .. } => {
                        return Err(refused());
                    }
                    BrokerEvent::Started { sequence: got, started } => {
                        if got != sequence || saw_started {
                            return Err(refused());
                        }
                        saw_started = true;
                        capture.started = started;
                    }
                    BrokerEvent::Output { sequence: got, stderr: is_err, bytes } => {
                        if got != sequence || !saw_started {
                            return Err(refused());
                        }
                        let output = if is_err { &mut capture.stderr } else { &mut capture.stdout };
                        let room = limits.stream_bytes.saturating_sub(output.len());
                        output.extend_from_slice(&bytes[..room.min(bytes.len())]);
                        if bytes.len() > room {
                            capture.truncated = true;
                            if is_err {
                                capture.stderr_end = StreamEnd::LimitExceeded;
                            } else {
                                capture.stdout_end = StreamEnd::LimitExceeded;
                            }
                            return Err(refused());
                        }
                    }
                    BrokerEvent::Completed {
                        sequence: got,
                        capture: mut completed,
                        stdout_len,
                        stderr_len,
                    } => {
                        if got != sequence
                            || !saw_started
                            || completed.started != capture.started
                            || stdout_len != capture.stdout.len() as u64
                            || stderr_len != capture.stderr.len() as u64
                        {
                            return Err(refused());
                        }
                        if completed.status.as_ref().is_some_and(|status|status.root_attempt!=self.originals.reply.context.context.root_attempt||status.member_attempt==[0;16]||status.member_attempt==self.originals.reply.context.context.root_attempt||matches!(self.originals.reply.context.context.subject,crate::Subject::RegisteredMember{attempt,..}if attempt==status.member_attempt)){return Err(refused());}
                        completed.stdout = std::mem::take(&mut capture.stdout);
                        completed.stderr = std::mem::take(&mut capture.stderr);
                        capture = completed;
                        self.validate(deadline)?;
                        return Ok(());
                    }
                }
            }
        })();
        if let Err(error) = result {
            capture.failure = Some(format!("original parent compiler relay failed: {error}"));
            if capture.stdout_end == StreamEnd::Pending {
                capture.stdout_end = StreamEnd::ReadFailed;
            }
            if capture.stderr_end == StreamEnd::Pending {
                capture.stderr_end = StreamEnd::ReadFailed;
            }
            self.originals.failed.store(true, Ordering::Release);
        } else if capture.failure.is_none()
            && capture.stdout_end == StreamEnd::Eof
            && capture.stderr_end == StreamEnd::Eof
            && !capture.truncated
        {
            self.failed = false;
        }
        Ok(CoordinatorCompilerCapture {
            observation: capture,
            _originals: Arc::clone(&self.originals),
        })
    }
}

/// Native transport only. Its endpoint can be delivered to a candidate solely
/// by actual original-Root/registered-output Host admission. It grants none.
pub struct CoordinatorBrokerEndpoint {
    original: OwnedFd,
}
impl CoordinatorBrokerEndpoint {
    pub fn as_fd(&self) -> BorrowedFd<'_> {
        self.original.as_fd()
    }
}
pub struct CoordinatorBrokerServer {
    channel: Channel,
    sequence: u64,
    active: Option<(u64, BrokerLimits)>,
    publication: Option<(u64, PublicationSelection)>,
    publication_member: Option<(crate::workload::host::produced::Key, [u8; 16])>,
    graph: Option<u64>,
    graph_closed: bool,
    failed: bool,
}
#[cfg(test)]
mod tests;
impl CoordinatorBrokerServer {
    pub fn pair() -> io::Result<(Self, CoordinatorBrokerEndpoint)> {
        let (parent, child) = UnixStream::pair()?;
        Ok((
            Self {
                channel: Channel::new(parent)?,
                sequence: 0,
                active: None,
                publication: None,
                publication_member: None,
                graph: None,
                graph_closed: false,
                failed: false,
            },
            CoordinatorBrokerEndpoint { original: child.into() },
        ))
    }
    /// Observe the SAME actual native prepared coordinator before its first
    /// request/GO. A decoded Prepared or caller-supplied hash cannot bind this
    /// endpoint. The caller continues retaining that original native member.
    pub fn bind_publication_member(
        &mut self,
        member: &mut crate::client::ContainedProducedMember,
        deadline: Instant,
    ) -> io::Result<Option<()>> {
        if self.failed
            || self.publication_member.is_some()
            || self.sequence != 0
            || self.active.is_some()
            || self.publication.is_some()
            || self.graph.is_some()
            || self.graph_closed
        {
            return Err(refused());
        }
        let Some(prepared) = member.coordinator_prepared(deadline)? else {
            return Ok(None);
        };
        self.publication_member = Some((prepared.produced.key, prepared.produced.member_attempt));
        Ok(Some(()))
    }
    pub fn receive(&mut self, deadline: Instant) -> io::Result<Option<BrokerRequest>> {
        if self.failed {
            return Err(refused());
        }
        let result = (|| {
            if !self.channel.ready_to_receive()? {
                if self.channel.at_eof()? && !self.graph_closed {
                    return Err(io::ErrorKind::UnexpectedEof.into());
                }
                return Ok(None);
            }
            if self.graph_closed {
                return Err(refused());
            }
            let request = BrokerRequest::decode(&self.channel.receive(deadline)?)?;
            match &request {
                BrokerRequest::Execute { sequence, limits, .. }
                    if self.active.is_none()
                        && self.publication.is_none()
                        && self.graph.is_none()
                        && *sequence == self.sequence.checked_add(1).ok_or_else(refused)? =>
                {
                    self.sequence = *sequence;
                    self.active = Some((*sequence, *limits));
                }
                BrokerRequest::Cancel { sequence }
                    if self.active.is_some_and(|(active, _)| active == *sequence) => {}
                BrokerRequest::FinishGraph { sequence }
                    if self.active.is_none()
                        && self.publication.is_none()
                        && self.graph.is_none()
                        && *sequence == self.sequence.checked_add(1).ok_or_else(refused)? =>
                {
                    self.sequence = *sequence;
                    self.graph = Some(*sequence);
                }
                BrokerRequest::Publish { sequence, selection }
                    if self.active.is_none()
                        && self.publication.is_none()
                        && self.graph.is_none()
                        && *sequence == self.sequence.checked_add(1).ok_or_else(refused)? =>
                {
                    self.sequence = *sequence;
                    self.publication = Some((*sequence, selection.clone()));
                }
                _ => return Err(refused()),
            }
            Ok(Some(request))
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    /// # Safety
    /// The fixed original parent must have independently checked every exact
    /// current graph row, genuine retired producer/read closure and original
    /// input bookends under this SAME completed native inspection operation.
    /// Neither the request nor this local return grants graph eligibility.
    pub unsafe fn complete_graph(
        &mut self,
        completed: &crate::client::workload::CompletedLocalOperation,
        deadline: Instant,
    ) -> io::Result<()> {
        let result = (|| {
            if self.failed || self.graph_closed {
                return Err(refused());
            }
            completed.require_success()?;
            let sequence = self.graph.ok_or_else(refused)?;
            if !same_local_member(
                &completed.begin().key,
                self.publication_member.as_ref().ok_or_else(refused)?,
            ) {
                return Err(refused());
            }
            if !matches!(&completed.begin().operation,crate::workload::host::publication::Operation::Begin(begin)if begin.kind==crate::workload::host::publication::Kind::PrepareOutputs)
            {
                return Err(refused());
            }
            self.channel.send(
                &BrokerEvent::GraphFinished {
                    sequence,
                    operation: completed.begin().key.operation,
                    failure: None,
                }
                .encode()?,
                deadline,
            )?;
            self.graph = None;
            self.graph_closed = true;
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    pub fn refuse_graph(&mut self, reason: String, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed || self.graph_closed {
                return Err(refused());
            }
            let sequence = self.graph.ok_or_else(refused)?;
            self.channel.send(
                &BrokerEvent::GraphFinished { sequence, operation: [0; 16], failure: Some(reason) }
                    .encode()?,
                deadline,
            )?;
            self.graph = None;
            self.graph_closed = true;
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    /// # Safety
    /// The SAME trusted original parent must retain a fully matched retired
    /// producer, Layout/root originals, complete independent copied files and
    /// actual native writer exclusion. `completed` is the genuine one-use
    /// local return; it alone does not establish producer eligibility.
    pub unsafe fn complete_publication(
        &mut self,
        expected: &PublicationSelection,
        completed: &crate::client::workload::CompletedLocalOperation,
        deadline: Instant,
    ) -> io::Result<()> {
        let result = (|| {
            if self.failed {
                return Err(refused());
            }
            completed.require_success()?;
            let (sequence, selection) = self.publication.as_ref().ok_or_else(refused)?;
            let begin = completed.begin();
            let member = self.publication_member.as_ref().ok_or_else(refused)?;
            if !same_publication_binding(expected, selection, &begin.key, member) {
                return Err(refused());
            }
            let crate::workload::host::publication::Operation::Begin(operation) = &begin.operation
            else {
                return Err(refused());
            };
            let mut destinations = operation
                .intents
                .iter()
                .filter_map(|intent| match intent {
                    crate::workload::host::publication::Intent::PublishFile {
                        destination, ..
                    } => Some(destination.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            destinations.sort();
            if destinations != selection.destinations {
                return Err(refused());
            }
            self.channel.send(
                &BrokerEvent::Published {
                    sequence: *sequence,
                    selection: selection.clone(),
                    operation: begin.key.operation,
                    failure: None,
                }
                .encode()?,
                deadline,
            )?;
            self.publication = None;
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    pub fn refuse_publication(&mut self, reason: String, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed {
                return Err(refused());
            }
            let (sequence, selection) = self.publication.as_ref().ok_or_else(refused)?;
            self.channel.send(
                &BrokerEvent::Published {
                    sequence: *sequence,
                    selection: selection.clone(),
                    operation: [0; 16],
                    failure: Some(reason),
                }
                .encode()?,
                deadline,
            )?;
            self.publication = None;
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    /// # Safety
    /// Only the trusted original SDK parent calls this after retaining the
    /// actual compiler admission, original source/SDK/output owners, native
    /// retirement and complete physical capture (or explicit failed capture).
    /// DATA here cannot manufacture those owners or release their unit. Keep
    /// the real capture separately for parent validation and comparison.
    pub unsafe fn complete(
        &mut self,
        capture: &BrokerCaptureData,
        deadline: Instant,
    ) -> io::Result<()> {
        self.complete_parts(capture, &capture.stdout, &capture.stderr, deadline)
    }
    /// Relay borrowed output from a retained native capture without copying
    /// the complete streams into a second observation. Header streams must be
    /// empty; the same framing, limits and one-shot completion apply.
    /// # Safety
    /// The caller must retain the original native execution/input owners as
    /// required by `complete`. Neither the header nor borrowed bytes supply
    /// native retirement, producer eligibility or execution authority.
    pub unsafe fn complete_with_output(
        &mut self,
        header: &BrokerCaptureData,
        stdout: &[u8],
        stderr: &[u8],
        deadline: Instant,
    ) -> io::Result<()> {
        if !header.stdout.is_empty() || !header.stderr.is_empty() {
            self.failed = true;
            return Err(refused());
        }
        self.complete_parts(header, stdout, stderr, deadline)
    }
    fn complete_parts(
        &mut self,
        capture: &BrokerCaptureData,
        stdout: &[u8],
        stderr: &[u8],
        deadline: Instant,
    ) -> io::Result<()> {
        let result = (|| {
            if self.failed {
                return Err(refused());
            }
            let (sequence, limits) = self.active.ok_or_else(refused)?;
            if stdout.len() > limits.stream_bytes || stderr.len() > limits.stream_bytes {
                return Err(refused());
            }
            self.channel.send(
                &BrokerEvent::Started { sequence, started: capture.started }.encode()?,
                deadline,
            )?;
            for (is_err, bytes) in [(false, stdout), (true, stderr)] {
                for bytes in bytes.chunks(64 * 1024) {
                    self.channel.send(
                        &BrokerEvent::Output { sequence, stderr: is_err, bytes: bytes.to_vec() }
                            .encode()?,
                        deadline,
                    )?;
                }
            }
            self.channel.send(
                &BrokerEvent::Completed {
                    sequence,
                    capture: BrokerCaptureData {
                        started: capture.started,
                        status: capture.status.clone(),
                        accounting: capture.accounting,
                        stdout: Vec::new(),
                        stderr: Vec::new(),
                        stdout_end: capture.stdout_end,
                        stderr_end: capture.stderr_end,
                        truncated: capture.truncated,
                        failure: capture.failure.clone(),
                        elapsed_ns: capture.elapsed_ns,
                    },
                    stdout_len: stdout.len() as u64,
                    stderr_len: stderr.len() as u64,
                }
                .encode()?,
                deadline,
            )?;
            self.active = None;
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
}
