//! Direct linker ownership through the SAME authenticated native stream owner.
use super::*;

pub struct LinkerMember {
    inner: MetadataMember,
}
#[derive(Debug)]
pub struct LinkerResult {
    pub prepared: crate::linker::Prepared,
    pub started: Started,
    pub completion: crate::linker::Completion,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub output_limit_exceeded: bool,
}
#[derive(Debug)]
pub enum LinkerOutcome {
    Completed(Box<LinkerResult>),
    /// Same host positively refused before execution and closed its streams.
    Refused(String),
}
pub enum LinkerError {
    BeforeRequest(io::Error),
    Refused,
    Unknown { member: Box<LinkerMember>, error: io::Error },
}
impl std::fmt::Debug for LinkerError {
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
impl std::fmt::Display for LinkerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native linker loan {self:?}")
    }
}
impl std::error::Error for LinkerError {}
impl Client {
    /// Borrow only the actual original primary of this registered compiler.
    /// No helper process is spawned by this path.
    /// # Safety
    /// The caller is the trusted SDK's post-join linker path, retains its
    /// original CompilerPause/primary and memory/SDK owners, and has positively
    /// joined all producing workers. Retain that SAME custody until positive
    /// Completed/Refused; Unknown poisons the unit and must never resume/retry.
    /// A decoded request or an arbitrary descriptor cannot meet this contract.
    pub unsafe fn linker_loan(
        &self,
        request: &crate::linker::Request,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<LinkerMember, LinkerError> {
        self.native_query(&NativeQueryRequest::Linker(request.clone()), io, deadline)
            .map(|inner| LinkerMember { inner })
            .map_err(|error| match error {
                MetadataError::BeforeRequest(error) => LinkerError::BeforeRequest(error),
                MetadataError::Refused => LinkerError::Refused,
                MetadataError::Unknown { member, error } => LinkerError::Unknown {
                    member: Box::new(LinkerMember { inner: *member }),
                    error,
                },
            })
    }
}
impl LinkerMember {
    pub fn prepared(&self) -> Option<&crate::linker::Prepared> {
        self.inner.streams.state.linker.as_ref()
    }
    pub fn started(&self) -> Option<Started> {
        self.inner.started()
    }
    pub fn accounting(&self) -> Option<crate::accounting::Observation> {
        self.inner.accounting()
    }
    pub fn cancel(&mut self, deadline: Instant) -> io::Result<()> {
        self.inner.cancel(deadline)
    }
    /// Diagnostic prefixes only, never a completion or permission to resume.
    pub fn take_failure_observation(&mut self) -> Option<MetadataFailureObservation> {
        self.inner.take_failure_observation()
    }
    pub fn poll(&mut self, deadline: Instant) -> io::Result<Option<LinkerOutcome>> {
        if self.inner.poisoned {
            return Err(invalid("linker lifecycle is unusable; never replay"));
        }
        let result =
            (|| match self.inner.streams.poll_inner(&self.inner.request, deadline, &mut None)? {
                StreamReady::Pending => Ok(None),
                StreamReady::Refused => {
                    self.inner.pin.validate(deadline)?;
                    self.inner.poisoned = true;
                    self.inner.result_delivered = true;
                    Ok(Some(LinkerOutcome::Refused(
                        self.inner
                            .streams
                            .state
                            .refused
                            .take()
                            .ok_or_else(|| invalid("missing original refusal"))?,
                    )))
                }
                StreamReady::Completed => {
                    self.inner.pin.validate(deadline)?;
                    let state = &mut self.inner.streams.state;
                    let prepared =
                        state.linker.take().ok_or_else(|| invalid("missing linker preparation"))?;
                    let started = state
                        .started
                        .take()
                        .ok_or_else(|| invalid("missing actual linker start"))?;
                    let terminal = state
                        .completed
                        .take()
                        .ok_or_else(|| invalid("missing linker retirement"))?;
                    let completion = state
                        .linker_completed
                        .take()
                        .ok_or_else(|| invalid("missing original linker owning wait"))?;
                    if completion.completed != terminal {
                        return Err(invalid("linker terminal differs from its original lifecycle"));
                    }
                    self.inner.poisoned = true;
                    self.inner.result_delivered = true;
                    Ok(Some(LinkerOutcome::Completed(Box::new(LinkerResult {
                        prepared,
                        started,
                        completion,
                        stdout: std::mem::take(&mut self.inner.streams.output.bytes[0]),
                        stderr: std::mem::take(&mut self.inner.streams.output.bytes[1]),
                        output_limit_exceeded: self.inner.streams.output.exceeded,
                    }))))
                }
            })();
        if result.is_err() {
            self.inner.poisoned = true;
        }
        result
    }
}

#[cfg(test)]
mod tests;
