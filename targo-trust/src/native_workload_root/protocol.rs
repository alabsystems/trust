//! Strict observations from one original service stream. None of these
//! decoders constructs an SDK, process, output owner or execution grant.
use sha2::{Digest as _, Sha256};
use trust_qualification::{Refusal, Result};
use trust_resource_controller::workload::service::checkpoint::Checkpoint;
use trust_resource_controller::workload::service::{self, Binding, OutputEnd, Ready, finish};
use trust_resource_controller::workload::{Continuation, Decision, WorkloadInvocation};

#[derive(Debug)]
pub(super) struct CheckpointOutput {
    pub checkpoint: Checkpoint,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub end: OutputEnd,
}
#[derive(Debug)]
pub(super) enum Event {
    Ready,
    Checkpoint(CheckpointOutput),
    Graph,
}
pub(super) struct Protocol {
    pub invocation: WorkloadInvocation,
    digest: [u8; 32],
    pub ready: Option<Ready>,
    pub graph: Option<finish::Graph>,
    pub census: Option<finish::Census>,
    output: Option<service::Output>,
    next: u64,
    pending: Option<Continuation>,
    diagnostics: [u64; 2],
    pub failure: Option<String>,
}
impl Protocol {
    pub fn new(invocation: WorkloadInvocation) -> Result<Self> {
        let digest = Sha256::digest(invocation.encode()?).into();
        Ok(Self {
            invocation,
            digest,
            ready: None,
            graph: None,
            census: None,
            output: None,
            next: 1,
            pending: None,
            diagnostics: [0, 0],
            failure: None,
        })
    }
    pub fn binding(&self) -> Result<&Binding> {
        self.ready
            .as_ref()
            .map(|ready| &ready.binding)
            .ok_or_else(|| Refusal("original service readiness has not been observed".into()))
    }
    pub fn take_continuation(&mut self) -> Option<Continuation> {
        self.pending.take()
    }
    pub fn frame(&mut self, bytes: &[u8]) -> Result<Option<Event>> {
        if self.failure.is_some() {
            return Err(Refusal("original workload protocol previously failed".into()));
        }
        let result = self.accept(bytes);
        if let Err(error) = &result {
            self.failure = Some(error.0.clone());
        }
        result
    }
    fn accept(&mut self, bytes: &[u8]) -> Result<Option<Event>> {
        if self.graph.is_some() {
            return Err(Refusal("native service emitted bytes after its final graph".into()));
        }
        if self.ready.is_none() {
            let ready = Ready::decode(bytes, self.digest)?;
            self.output = Some(service::Output::new(ready.binding.clone(), 1)?);
            self.census = Some(finish::Census::new(ready.binding.clone()));
            self.ready = Some(ready);
            return Ok(Some(Event::Ready));
        }
        let binding = self.binding()?.clone();
        if let Ok(chunk) = service::Chunk::decode(bytes, &binding) {
            self.output
                .as_mut()
                .ok_or_else(|| Refusal("native output outside its planned checkpoint".into()))?
                .append(chunk)?;
            return Ok(None);
        }
        if let Ok(end) = OutputEnd::decode(bytes, &binding) {
            self.output
                .as_mut()
                .ok_or_else(|| {
                    Refusal("native stream closure outside its planned checkpoint".into())
                })?
                .close(end)?;
            return Ok(None);
        }
        if let Ok(checkpoint) = Checkpoint::decode(bytes, &binding, &self.invocation) {
            if checkpoint.sequence != self.next || self.pending.is_some() {
                return Err(Refusal(
                    "native checkpoint repeated or has no original continuation boundary".into(),
                ));
            }
            let output = self.output.take().ok_or_else(|| {
                Refusal("native checkpoint omitted its original output owner".into())
            })?;
            let (stdout, stderr, end, failed) = output.into_parts();
            let end = end.ok_or_else(|| {
                Refusal("native checkpoint omitted explicit output-end facts".into())
            })?;
            if failed {
                return Err(Refusal(
                    "native checkpoint output is incomplete or inconsistent".into(),
                ));
            }
            self.pending = Some(Continuation {
                invocation_sha256: binding.invocation_sha256,
                root_attempt: binding.root_attempt,
                checkpoint: self.next,
                checkpoint_sha256: Sha256::digest(bytes).into(),
                decision: Decision::Continue,
            });
            self.next += 1;
            if self.next <= 3 + 2 * u64::from(self.invocation.repetitions) {
                self.output = Some(service::Output::new(binding, self.next)?);
            }
            return Ok(Some(Event::Checkpoint(CheckpointOutput {
                checkpoint,
                stdout,
                stderr,
                end,
            })));
        }
        if let Ok(diagnostic) = finish::Diagnostic::decode(bytes, &binding) {
            let index = usize::from(diagnostic.stream == service::Stream::Stderr);
            if self.next == 1 || diagnostic.offset != self.diagnostics[index] {
                return Err(Refusal(
                    "postcompiler diagnostic repeated or appeared before compiler retirement"
                        .into(),
                ));
            }
            self.diagnostics[index] += diagnostic.bytes.len() as u64;
            return Ok(None);
        }
        if let Ok(page) = finish::decode_page(bytes, &binding) {
            if self.pending.is_some() {
                return Err(Refusal(
                    "native census arrived before the original continuation".into(),
                ));
            }
            self.census.as_mut().expect("readiness initialized census").append(page)?;
            return Ok(None);
        }
        if let Ok(graph) = finish::Graph::decode(bytes, &binding) {
            if self.pending.is_some() {
                return Err(Refusal(
                    "native graph arrived before the original continuation".into(),
                ));
            }
            if graph.succeeded && self.next != 4 + 2 * u64::from(self.invocation.repetitions) {
                return Err(Refusal(
                    "native successful graph omitted its full original checkpoint population"
                        .into(),
                ));
            }
            self.census.as_ref().expect("readiness initialized census").check_finished(&graph)?;
            self.graph = Some(graph);
            return Ok(Some(Event::Graph));
        }
        Err(Refusal("unknown, malformed or misbound native workload service frame".into()))
    }
    pub fn diagnostic_lengths(&self) -> [u64; 2] {
        self.diagnostics
    }
}
