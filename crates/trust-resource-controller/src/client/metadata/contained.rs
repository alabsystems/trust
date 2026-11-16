// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! A completed operation retains its original live native member owner. A
//! public result, decoded terminal or EOF alone cannot construct this type.
use super::*;
use crate::client::workload::RegisteredOutput;
use crate::workload::host::contained;

pub struct ContainedProducedMember {
    original: Option<ProducedMember>,
    pending: Option<ProducedResult>,
    final_failure: Option<String>,
    compacted: Option<CompletedOriginal>,
    coordinator_bound: bool,
}

/// One-use result of the actual accepted contained operation. This value
/// retains the original accepted-derived pin and binding after the exact
/// original control/event/output streams have completed and closed.
/// It is not CPU/SDK admission, a generic protected-scope close or a grant to
/// run another process. There is no constructor or deserializer from DATA.
pub struct CompletedProducedOperation {
    original: std::sync::Arc<CompletedOriginal>,
    observation: Option<ProducedResult>,
}

/// Retains the SAME completed native original after its private, untouched
/// observation established a successful exit and complete bounded output.
/// This is execution evidence, not CPU admission or a proof/correctness grade.
/// Public observation DATA cannot construct or change this owner.
pub struct SuccessfulProducedCompletion {
    original: std::sync::Arc<CompletedOriginal>,
}
impl SuccessfulProducedCompletion {
    pub fn matches_registration(&self, registered: &RegisteredOutput) -> bool {
        self.original.request.produced.validate_registered(registered.registration()).is_ok()
            && registered.matches_pin(&self.original.pin)
    }
}
// Created only by consuming the original validated, actually completed member.
// Keep its original accepted-derived pin. Event/control duplicates and original pipe
// readers have actual EOF before they are closed; no saved observation creates
// this owner. Raw event bytes remain available on a late deadline failure.
struct CompletedOriginal {
    accepted: trust_resource_provenance::PinnedHelper,
    pin: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
    request: contained::Request,
    event_prefix: Vec<u8>,
    event_bytes_seen: u64,
}
fn control_finished(channel: &Channel, deadline: Instant) -> io::Result<bool> {
    if Instant::now() >= deadline {
        return Err(io::ErrorKind::TimedOut.into());
    }
    let eof = channel.at_eof()?;
    if !eof && channel.ready_to_receive()? {
        return Err(invalid("contained control has trailing data"));
    }
    if Instant::now() >= deadline {
        return Err(io::ErrorKind::TimedOut.into());
    }
    Ok(eof)
}
impl CompletedOriginal {
    fn consume(
        mut original: ProducedMember,
        deadline: Instant,
    ) -> Result<Self, Box<(ProducedMember, io::Error)>> {
        let accepted = match original.inner.host.into_helper_preserving(deadline) {
            Ok(accepted) => accepted,
            Err(failure) => {
                let (host, error) = *failure;
                original.inner.host = host;
                return Err(Box::new((original, error)));
            }
        };
        let MetadataMember { pin, streams, request, .. } = original.inner;
        let request = match request {
            NativeQueryRequest::ContainedProduced(request, _) => request,
            NativeQueryRequest::Coordinator(request, _) => request.contained,
            _ => unreachable!("private completed member has contained purpose"),
        };
        Ok(Self {
            accepted,
            pin,
            request,
            event_prefix: streams.observed.prefix,
            event_bytes_seen: streams.observed.seen,
        })
    }
}
impl CompletedProducedOperation {
    pub fn request(&self) -> &contained::Request {
        &self.original.request
    }
    pub fn matches_registration(&self, registered: &RegisteredOutput) -> bool {
        self.request().produced.validate_registered(registered.registration()).is_ok()
            && registered.matches_pin(&self.original.pin)
    }
    /// Inspect only the still-private native observation. Taking its DATA
    /// first permanently prevents this operation from issuing a success owner.
    pub fn successful_completion(&self) -> io::Result<SuccessfulProducedCompletion> {
        let result = self
            .observation
            .as_ref()
            .ok_or_else(|| invalid("native completion observation already delivered"))?;
        if result.output_limit_exceeded
            || !matches!(
                result.completion.completed.finished.status,
                crate::Status::Finished {
                    outcome: crate::Outcome::Exit(0),
                    cause: crate::CompletionCause::Exited,
                    ..
                }
            )
        {
            return Err(invalid("native operation did not complete successfully"));
        }
        Ok(SuccessfulProducedCompletion { original: self.original.clone() })
    }
    /// Move the separate output DATA once while retaining this opaque native
    /// operation owner in the original artifact/phase capsule.
    pub fn take_observation(&mut self) -> Option<ProducedResult> {
        self.observation.take()
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.original.accepted.validate(deadline)?;
        self.original.pin.validate(deadline)?;
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(())
    }
}

pub enum ContainedProducedError {
    BeforeRequest(io::Error),
    Refused,
    Unknown { member: Box<ContainedProducedMember>, error: io::Error },
}
impl std::fmt::Debug for ContainedProducedError {
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
impl std::fmt::Display for ContainedProducedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "contained produced operation {self:?}")
    }
}
impl std::error::Error for ContainedProducedError {}

impl Client {
    /// Execute only an actually registered produced coordinator with the SAME
    /// parent-bank primary and parent-prepared Layout originals.
    /// # Safety
    /// The trusted parent retains its actual registered image/source/SDK,
    /// primary loan and original close-only output capsule through known native
    /// retirement, all physical stream EOF and independent result validation.
    /// Neither selected request bytes nor candidate reports satisfy this.
    pub unsafe fn workload_coordinator(
        &self,
        registered: &RegisteredOutput,
        request: &crate::workload::host::coordinator::Request,
        primary_and_broker: [std::os::fd::BorrowedFd<'_>; 2],
        outputs: &[std::os::fd::BorrowedFd<'_>],
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<ContainedProducedMember, ContainedProducedError> {
        let [primary, broker] = primary_and_broker;
        let prepare = || -> io::Result<_> {
            request.validate()?;
            request.contained.produced.validate_registered(registered.registration())?;
            if !registered.matches(self)
                || !io.descriptions.is_empty()
                || request.primary.source != primary.as_raw_fd() as u32
                || request.broker.source != broker.as_raw_fd() as u32
                || outputs.len() != request.outputs.locks.len()
            {
                return Err(invalid("coordinator differs from actual original parent inputs"));
            }
            let primary = primary.try_clone_to_owned()?;
            let mut request = request.clone();
            request.primary.source = primary.as_raw_fd() as u32;
            let broker = broker.try_clone_to_owned()?;
            request.broker.source = broker.as_raw_fd() as u32;
            let mut descriptions = vec![primary, broker];
            for output in outputs {
                descriptions.push(output.try_clone_to_owned()?);
            }
            Ok((
                NativeQueryRequest::Coordinator(request, registered.observation().clone()),
                MetadataIo { descriptions },
            ))
        };
        let (native, io) = prepare().map_err(ContainedProducedError::BeforeRequest)?;
        self.native_query(&native, io, deadline)
            .map(ContainedProducedMember::from_original)
            .map_err(|error| match error {
                MetadataError::BeforeRequest(error) => ContainedProducedError::BeforeRequest(error),
                MetadataError::Refused => ContainedProducedError::Refused,
                MetadataError::Unknown { member, error } => ContainedProducedError::Unknown {
                    member: Box::new(ContainedProducedMember::from_original(*member)),
                    error,
                },
            })
    }
    pub fn workload_contained_produced(
        &self,
        registered: &RegisteredOutput,
        request: &contained::Request,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<ContainedProducedMember, ContainedProducedError> {
        let check = || -> io::Result<()> {
            request.validate()?;
            request.produced.validate_registered(registered.registration())?;
            if !registered.matches(self) {
                return Err(invalid("contained registration belongs to another original host"));
            }
            Ok(())
        };
        check().map_err(ContainedProducedError::BeforeRequest)?;
        let native = NativeQueryRequest::ContainedProduced(
            request.clone(),
            registered.observation().clone(),
        );
        self.native_query(&native, io, deadline)
            .map(ContainedProducedMember::from_original)
            .map_err(|error| match error {
                MetadataError::BeforeRequest(error) => ContainedProducedError::BeforeRequest(error),
                MetadataError::Refused => ContainedProducedError::Refused,
                MetadataError::Unknown { member, error } => ContainedProducedError::Unknown {
                    member: Box::new(ContainedProducedMember::from_original(*member)),
                    error,
                },
            })
    }
}

impl ContainedProducedMember {
    /// Request DATA borrowed from this actual admitted coordinator member.
    /// It cannot construct the member or replace its original descriptions.
    pub fn coordinator_request(&self) -> io::Result<&crate::workload::host::coordinator::Request> {
        self.original
            .as_ref()
            .and_then(|original| original.inner.request.coordinator())
            .ok_or_else(|| invalid("not a live original coordinator member"))
    }

    /// A coordinator refusal additionally requires its SAME actual control
    /// stream to close. Output/event EOF alone cannot retire its parent's
    /// separately held original primary. Retain this member with the result.
    pub fn coordinator_refusal(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Option<&crate::StatusFrame>> {
        self.coordinator_request()?;
        let original = self.original.as_mut().expect("original coordinator checked above");
        if original.workload_refusal(deadline)?.is_none()
            || !control_finished(&original.inner.control, deadline)?
        {
            return Ok(None);
        }
        original.workload_refusal(deadline)
    }

    pub fn coordinator_prepared(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Option<crate::workload::host::coordinator::Prepared>> {
        let original = self
            .original
            .as_mut()
            .ok_or_else(|| invalid("original coordinator already consumed"))?;
        let inner = &mut original.inner;
        if inner.request.coordinator().is_none() {
            return Err(invalid("not an original coordinator member"));
        }
        inner.pin.validate(deadline)?;
        inner.streams.poll_inner(&inner.request, deadline, &mut None)?;
        inner.pin.validate(deadline)?;
        Ok(inner.streams.state.coordinator_prepared.clone())
    }
    pub fn bind_coordinator(
        &mut self,
        selection: &crate::workload::host::coordinator::SemanticSelection,
        deadline: Instant,
    ) -> io::Result<()> {
        use sha2::{Digest as _, Sha256};
        if self.coordinator_bound {
            return Err(invalid("coordinator selection already delivered"));
        }
        let original = self
            .original
            .as_mut()
            .ok_or_else(|| invalid("original coordinator already consumed"))?;
        let inner = &mut original.inner;
        let request = inner
            .request
            .coordinator()
            .ok_or_else(|| invalid("not an original coordinator member"))?;
        let prepared = inner
            .streams
            .state
            .coordinator_prepared
            .as_ref()
            .ok_or_else(|| invalid("original coordinator preparation not observed"))?;
        let digest: [u8; 32] = Sha256::digest(prepared.encode()?).into();
        if selection.root_attempt != request.contained.produced.key.root_attempt
            || selection.member_attempt != request.contained.produced.member.member_attempt
            || selection.prepared_sha256 != digest
            || inner.streams.failed
            || inner.streams.state.started.is_some()
        {
            return Err(invalid("coordinator selection differs from original native preparation"));
        }
        inner.pin.validate(deadline)?;
        // A partial write is still delivery. Never retry or replace this
        // selection, even if subsequent native-pin validation fails.
        self.coordinator_bound = true;
        inner.streams.events.send(&selection.encode()?, deadline)?;
        inner.pin.validate(deadline)
    }
    fn from_original(original: MetadataMember) -> Self {
        Self {
            original: Some(ProducedMember { inner: original }),
            pending: None,
            final_failure: None,
            compacted: None,
            coordinator_bound: false,
        }
    }
    pub fn cancel(&mut self, deadline: Instant) -> io::Result<()> {
        self.original
            .as_mut()
            .ok_or_else(|| invalid("contained operation already consumed"))?
            .cancel(deadline)
    }
    pub fn workload_refusal(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Option<&crate::StatusFrame>> {
        self.original
            .as_mut()
            .ok_or_else(|| invalid("contained operation already consumed"))?
            .workload_refusal(deadline)
    }
    pub fn poll(&mut self, deadline: Instant) -> io::Result<Option<CompletedProducedOperation>> {
        self.poll_observed(deadline, &mut None)
    }
    pub fn poll_with_observer(
        &mut self,
        deadline: Instant,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<CompletedProducedOperation>> {
        self.poll_observed(deadline, &mut Some(observer))
    }
    fn poll_observed(
        &mut self,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> io::Result<Option<CompletedProducedOperation>> {
        let original = self
            .original
            .as_mut()
            .ok_or_else(|| invalid("contained operation already consumed"))?;
        if self.final_failure.is_some() {
            return Err(invalid("contained final check failed; never replay"));
        }
        if self.pending.is_none() {
            let Some(result) = original.poll_observed(deadline, observer)? else {
                return Ok(None);
            };
            // Keep known status/raw bytes while the SAME original control
            // stream finishes, and across every final native check failure.
            self.pending = Some(result);
        }
        let control = control_finished(&original.inner.control, deadline);
        match control {
            Ok(true) => {}
            Ok(false) => return Ok(None),
            Err(error) => {
                self.final_failure = Some(error.to_string());
                return Err(error);
            }
        }
        let checked = (|| {
            if original.inner.streams.state.contained.is_none() {
                return Err(invalid("missing actual contained retirement"));
            }
            if !original.inner.result_delivered || original.inner.streams.output.eof != [true, true]
            {
                return Err(invalid("contained original streams are not actually complete"));
            }
            original.inner.host.revalidate(deadline)?;
            original.inner.pin.validate(deadline)?;
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            Ok(())
        })();
        if let Err(error) = checked {
            self.final_failure = Some(error.to_string());
            return Err(error);
        }
        let compacted = match CompletedOriginal::consume(
            self.original.take().expect("same original member"),
            deadline,
        ) {
            Ok(compacted) => compacted,
            Err(failure) => {
                let (original, error) = *failure;
                self.original = Some(original);
                self.final_failure = Some(error.to_string());
                return Err(error);
            }
        };
        // Closing exhausted original readers/control duplicates is native work.
        // A late deadline preserves the same accepted owner and actual output.
        if Instant::now() >= deadline {
            self.compacted = Some(compacted);
            self.final_failure = Some("contained completion deadline".into());
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(Some(CompletedProducedOperation {
            original: std::sync::Arc::new(compacted),
            observation: self.pending.take(),
        }))
    }
    pub fn take_failure_observation_with_observer(
        &mut self,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<ProducedFailureObservation>> {
        Ok(self.take_failure(&mut Some(observer)))
    }
    pub fn take_failure_observation(&mut self) -> Option<ProducedFailureObservation> {
        self.take_failure(&mut None)
    }
    fn take_failure(
        &mut self,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> Option<ProducedFailureObservation> {
        if let Some(result) = self.pending.take() {
            let (key, member_attempt, event_prefix, event_bytes_seen, stdout_eof, stderr_eof) =
                if let Some(original) = self.original.as_mut() {
                    let (request, _) = original.inner.request.produced_parts()?;
                    (
                        request.key.clone(),
                        request.member.member_attempt,
                        std::mem::take(&mut original.inner.streams.observed.prefix),
                        original.inner.streams.observed.seen,
                        original.inner.streams.output.eof[0],
                        original.inner.streams.output.eof[1],
                    )
                } else {
                    let original = self.compacted.as_mut()?;
                    (
                        original.request.produced.key.clone(),
                        original.request.produced.member.member_attempt,
                        std::mem::take(&mut original.event_prefix),
                        original.event_bytes_seen,
                        true,
                        true,
                    )
                };
            return Some(ProducedFailureObservation {
                key,
                member_attempt,
                prepared: Some(result.prepared),
                observed_started: Some(result.started),
                observed_completion: Some(result.completion),
                stdout: result.stdout,
                stderr: result.stderr,
                stdout_eof,
                stderr_eof,
                output_limit_exceeded: result.output_limit_exceeded,
                event_prefix,
                event_bytes_seen,
                capture_error: self.final_failure.take(),
            });
        }
        self.original.as_mut()?.take_failure(observer)
    }
}

#[cfg(test)]
mod tests;
