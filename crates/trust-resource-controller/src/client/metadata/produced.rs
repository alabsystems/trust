//! Typed producing facade over the SAME original native member/stream owner.
//! No second process, transport, pool, CPU/GNU grant or local fallback exists.
use super::*;
use crate::client::workload::RegisteredOutput;
use crate::workload::host::produced::{Key, ProducedPrepared, ProducedRequest};

pub struct ProducedMember {
    pub(super) inner: MetadataMember,
}
#[derive(Debug)]
pub struct ProducedResult {
    pub prepared: ProducedPrepared,
    pub started: crate::Started,
    pub completion: crate::workload::host::Completion,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub output_limit_exceeded: bool,
}
#[derive(Debug)]
pub struct ProducedFailureObservation {
    pub key: Key,
    pub member_attempt: [u8; 16],
    pub prepared: Option<ProducedPrepared>,
    /// Observed data only; failed EOF/pin/capture cannot promote it to a
    /// positive retirement, complete bytes or eligible accounting result.
    pub observed_completion: Option<crate::workload::host::Completion>,
    pub observed_started: Option<crate::Started>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_eof: bool,
    pub stderr_eof: bool,
    pub output_limit_exceeded: bool,
    pub event_prefix: Vec<u8>,
    pub event_bytes_seen: u64,
    pub capture_error: Option<String>,
}
pub enum ProducedError {
    BeforeRequest(io::Error),
    Refused,
    Unknown { member: Box<ProducedMember>, error: io::Error },
}
impl std::fmt::Debug for ProducedError {
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
impl std::fmt::Display for ProducedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native produced member {self:?}")
    }
}
impl std::error::Error for ProducedError {}

impl Client {
    /// Execute only against the actual same-host live registration. Its opaque
    /// value is not admission: original private phase/resources/input custody
    /// and the suspended child checks remain mandatory at the actual host.
    pub fn workload_produced(
        &self,
        registered: &RegisteredOutput,
        request: &ProducedRequest,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<ProducedMember, ProducedError> {
        request
            .validate_registered(registered.registration())
            .map_err(ProducedError::BeforeRequest)?;
        if !registered.matches(self) {
            return Err(ProducedError::BeforeRequest(invalid(
                "produced registration belongs to another original host pin",
            )));
        }
        let native =
            NativeQueryRequest::Produced(request.clone(), registered.observation().clone());
        self.native_query(&native, io, deadline).map(|inner| ProducedMember { inner }).map_err(
            |error| match error {
                MetadataError::BeforeRequest(error) => ProducedError::BeforeRequest(error),
                MetadataError::Refused => ProducedError::Refused,
                MetadataError::Unknown { member, error } => ProducedError::Unknown {
                    member: Box::new(ProducedMember { inner: *member }),
                    error,
                },
            },
        )
    }
}
impl ProducedMember {
    pub fn workload_refusal(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Option<&crate::StatusFrame>> {
        self.inner.workload_refusal(deadline)
    }
    pub fn prepared(&self) -> Option<&ProducedPrepared> {
        self.inner.streams.state.produced.as_ref()
    }
    pub fn started(&self) -> Option<crate::Started> {
        self.inner.started()
    }
    pub fn accounting(&self) -> Option<crate::accounting::Observation> {
        self.inner.accounting()
    }
    pub fn cancel(&mut self, deadline: Instant) -> io::Result<()> {
        self.inner.cancel(deadline)
    }
    pub fn poll(&mut self, deadline: Instant) -> io::Result<Option<ProducedResult>> {
        self.poll_observed(deadline, &mut None)
    }
    /// Actual bounded bytes reach the same original sink before callback error
    /// can poison the member. A failed observer can never retry or complete it.
    pub fn poll_with_observer(
        &mut self,
        deadline: Instant,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<ProducedResult>> {
        self.poll_observed(deadline, &mut Some(observer))
    }
    pub(super) fn poll_observed(
        &mut self,
        deadline: Instant,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> io::Result<Option<ProducedResult>> {
        if self.inner.poisoned {
            return Err(invalid("produced lifecycle is unusable; never replay"));
        }
        let result =
            (|| match self.inner.streams.poll_inner(&self.inner.request, deadline, observer)? {
                StreamReady::Pending => Ok(None),
                StreamReady::Refused => {
                    self.inner.pin.validate(deadline)?;
                    self.inner.refusal_finalized = true;
                    Err(io::Error::new(
                        io::ErrorKind::PermissionDenied,
                        format!(
                            "produced member refused before execution: {}",
                            self.inner.streams.state.refused.as_deref().unwrap_or("unknown")
                        ),
                    ))
                }
                StreamReady::Completed => {
                    self.inner.pin.validate(deadline)?;
                    let state = &mut self.inner.streams.state;
                    let prepared = state
                        .produced
                        .take()
                        .ok_or_else(|| invalid("missing actual mixed-root preparation"))?;
                    let started = state
                        .started
                        .take()
                        .ok_or_else(|| invalid("missing actual native start"))?;
                    let terminal = state
                        .completed
                        .take()
                        .ok_or_else(|| invalid("missing native retirement"))?;
                    let completion = state
                        .workload
                        .take()
                        .ok_or_else(|| invalid("missing negotiated produced completion"))?;
                    if completion.completed != terminal {
                        return Err(invalid(
                            "produced completion differs from its original lifecycle",
                        ));
                    }
                    self.inner.poisoned = true;
                    self.inner.result_delivered = true;
                    Ok(Some(ProducedResult {
                        prepared,
                        started,
                        completion,
                        stdout: std::mem::take(&mut self.inner.streams.output.bytes[0]),
                        stderr: std::mem::take(&mut self.inner.streams.output.bytes[1]),
                        output_limit_exceeded: self.inner.streams.output.exceeded,
                    }))
                }
            })();
        if result.is_err() {
            self.inner.poisoned = true;
        }
        result
    }
    pub fn take_failure_observation(&mut self) -> Option<ProducedFailureObservation> {
        self.take_failure(&mut None)
    }
    pub fn take_failure_observation_with_observer(
        &mut self,
        observer: &mut OutputObserver<'_>,
    ) -> io::Result<Option<ProducedFailureObservation>> {
        Ok(self.take_failure(&mut Some(observer)))
    }
    pub(super) fn take_failure(
        &mut self,
        observer: &mut Option<&mut OutputObserver<'_>>,
    ) -> Option<ProducedFailureObservation> {
        let Some((request, _)) = self.inner.request.produced_parts() else {
            unreachable!("opaque produced member has another purpose")
        };
        let key = request.key.clone();
        let prepared = self.inner.streams.state.produced.clone();
        let observed_completion = self.inner.streams.state.workload.clone();
        let observed_started = self.inner.streams.state.started;
        let raw = self.inner.take_failure_observation_inner(observer)?;
        Some(ProducedFailureObservation {
            key,
            member_attempt: raw.member_attempt,
            prepared,
            observed_completion,
            observed_started,
            stdout: raw.stdout,
            stderr: raw.stderr,
            stdout_eof: raw.stdout_eof,
            stderr_eof: raw.stderr_eof,
            output_limit_exceeded: raw.output_limit_exceeded,
            event_prefix: raw.event_prefix,
            event_bytes_seen: raw.event_bytes_seen,
            capture_error: raw.capture_error,
        })
    }
}

#[cfg(test)]
mod tests;
