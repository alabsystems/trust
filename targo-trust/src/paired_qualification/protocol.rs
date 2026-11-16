//! Checked observations from the distinct full60 service. Continuations only
//! resume the original live graph; this reader never constructs native rights.
use std::collections::{BTreeMap, BTreeSet};

use service::{Node, OutputScope, Stream};
use sha2::{Digest as _, Sha256};
use trust_qualification::{Refusal, Result};
use trust_resource_controller::paired_qualification::{PairedInvocation, service};
use trust_resource_controller::workload::host::census::SourceKind;
use trust_resource_controller::{CompletionCause, Outcome, Status};

#[derive(Default)]
struct StreamState {
    length: u64,
    sha256: Sha256,
    end: Option<service::DiagnosticEnd>,
}
#[derive(Default)]
struct NodeState {
    registered: Option<service::Registered>,
    terminal: Option<service::Finished>,
    continued: bool,
    streams: BTreeMap<(u8, u8), StreamState>,
    compiler_observation: Option<service::compiler_observation::Observation>,
}
fn key(scope: OutputScope, stream: Stream) -> (u8, u8) {
    (
        match scope {
            OutputScope::Diagnostics => 0,
            OutputScope::CompilerReport => 1,
            OutputScope::NativeAction => 2,
        },
        u8::from(stream == Stream::Stderr),
    )
}
pub(super) enum Event {
    Ready(service::Ready),
    Registered(service::Registered),
    Artifact(service::Artifact),
    Chunk(service::Chunk),
    DiagnosticEnd(service::DiagnosticEnd),
    CompilerObservation(service::compiler_observation::Observation),
    Finished(service::Finished),
    Checkpoint(service::Checkpoint),
    Final(service::Final),
}

pub(super) struct Protocol {
    plan: PairedInvocation,
    digest: [u8; 32],
    pub ready: Option<service::Ready>,
    nodes: BTreeMap<Node, NodeState>,
    artifacts: BTreeMap<u32, service::Artifact>,
    expected: Option<(Node, [u8; 32])>,
    pending: Option<service::Checkpoint>,
    next: u64,
    pub census: Option<trust_resource_controller::workload::service::finish::Census>,
    pub final_observation: Option<service::Final>,
    pub failure: Option<String>,
}
impl Protocol {
    pub fn new(plan: PairedInvocation) -> Result<Self> {
        let digest = Sha256::digest(plan.binding_preimage()?).into();
        let nodes = Node::population(plan.consumer.repetitions)?
            .into_iter()
            .map(|node| (node, NodeState::default()))
            .collect();
        Ok(Self {
            plan,
            digest,
            ready: None,
            nodes,
            artifacts: BTreeMap::new(),
            expected: None,
            pending: None,
            next: 1,
            census: None,
            final_observation: None,
            failure: None,
        })
    }
    pub fn binding(&self) -> Result<&service::Binding> {
        self.ready
            .as_ref()
            .map(|ready| &ready.binding)
            .ok_or_else(|| Refusal("paired service has not observed original readiness".into()))
    }
    /// Called only AFTER the original input checks and actual write of this
    /// exact66 frame. Taking a checkpoint does not itself acknowledge it.
    pub fn continued(&mut self, checkpoint: &service::Checkpoint) -> Result<()> {
        let result = (|| {
            if self.failure.is_some() || self.pending.as_ref() != Some(checkpoint) {
                return Err(Refusal("paired continuation is missing, stale or misbound".into()));
            }
            self.nodes.get_mut(&checkpoint.node).expect("decoded population").continued = true;
            self.pending = None;
            Ok(())
        })();
        self.keep_failure(result)
    }
    pub fn frame(&mut self, bytes: &[u8]) -> Result<Option<Event>> {
        if self.failure.is_some() {
            return Err(Refusal(
                "paired protocol previously failed; retained observations are incomplete".into(),
            ));
        }
        let result = self.accept(bytes);
        self.keep_failure(result)
    }
    fn keep_failure<T>(&mut self, result: Result<T>) -> Result<T> {
        if let Err(error) = &result {
            self.failure.get_or_insert(error.0.clone());
        }
        result
    }
    fn accept(&mut self, bytes: &[u8]) -> Result<Option<Event>> {
        if self.final_observation.is_some() {
            return Err(Refusal("paired bytes after the final full graph observation".into()));
        }
        let repetitions = self.plan.consumer.repetitions;
        if self.ready.is_none() {
            // Revision2 explicitly promises the checked compiler projection.
            // An old61/v1 root refuses here before its project configuration.
            let ready = service::compiler_observation::Ready::decode(bytes, self.digest)?.original;
            if ready.repetitions != repetitions {
                return Err(Refusal("paired readiness changed the requested denominator".into()));
            }
            // A shared census reducer consumes equality data only. This does
            // not synthesize a workload-v1 Ready/startup or an execution owner.
            self.census = Some(trust_resource_controller::workload::service::finish::Census::new(
                trust_resource_controller::workload::service::Binding {
                    root_attempt: ready.binding.root_attempt,
                    invocation_sha256: ready.binding.invocation_sha256,
                },
            ));
            self.ready = Some(ready.clone());
            return Ok(Some(Event::Ready(ready)));
        }
        let binding = self.binding()?.clone();
        if let Ok(chunk) = service::Chunk::decode(bytes, &binding, repetitions) {
            let state = self.nodes.get_mut(&chunk.node).expect("decoded population");
            if state.registered.is_none() || (!chunk.node.is_compile() && state.terminal.is_some())
            {
                return Err(Refusal(
                    "paired bytes outside their original registered action".into(),
                ));
            }
            let stream = state.streams.entry(key(chunk.scope, chunk.stream)).or_default();
            if stream.end.is_some() || stream.length != chunk.offset {
                return Err(Refusal(
                    "paired stream repeated, skipped bytes or followed writer closure".into(),
                ));
            }
            stream.length += chunk.bytes.len() as u64;
            if chunk.scope == OutputScope::CompilerReport {
                stream.sha256.update(&chunk.bytes);
            }
            return Ok(Some(Event::Chunk(chunk)));
        }
        if let Ok(observation) = service::compiler_observation::Observation::decode(bytes, &binding)
        {
            let state = self.nodes.get_mut(&observation.node).expect("decoded compile node");
            let report =
                state.streams.get(&key(OutputScope::CompilerReport, Stream::Stdout)).ok_or_else(
                    || Refusal("compiler projection precedes original report closure".into()),
                )?;
            let end = report.end.as_ref().ok_or_else(|| {
                Refusal("compiler projection precedes original writer end".into())
            })?;
            let digest: [u8; 32] = report.sha256.clone().finalize().into();
            if state.compiler_observation.is_some()
                || observation.report_bytes != report.length
                || observation.report_sha256 != digest
                || (observation.counts.is_some() && (!end.writer_closed || end.truncated))
            {
                return Err(Refusal(
                    "compiler projection repeated or changed original report bytes/closure".into(),
                ));
            }
            state.compiler_observation = Some(observation.clone());
            return Ok(Some(Event::CompilerObservation(observation)));
        }
        if let Ok(end) = service::DiagnosticEnd::decode(bytes, &binding, repetitions) {
            // A preparation failure can close the pre-created, unused stage
            // before its explicit Blocked node is registered. Nonzero bytes
            // still require an original registration above.
            let stream = self
                .nodes
                .get_mut(&end.node)
                .expect("decoded population")
                .streams
                .entry(key(end.scope, end.stream))
                .or_default();
            if stream.end.is_some() || stream.length != end.length {
                return Err(Refusal(
                    "paired diagnostic end changed the actual received length".into(),
                ));
            }
            stream.end = Some(end.clone());
            return Ok(Some(Event::DiagnosticEnd(end)));
        }
        if let Ok(registered) = service::Registered::decode(bytes, &binding, repetitions) {
            if self.expected.is_some() || self.pending.is_some() {
                return Err(Refusal(
                    "paired action registered before the original continuation".into(),
                ));
            }
            if let Some(unit) = &registered.original_compile_unit {
                let mut source = self.plan.ay.root.clone();
                source.extend_from_slice(b"/crates/ay-proof-common/src/lib.rs");
                // `package` is Cargo's full PackageId, not a package-name
                // string. Retain and compare it exactly between policies;
                // the actual Unit owner supplies its selection authority.
                if unit.target != "ay_proof_common" || unit.source != source {
                    return Err(Refusal(
                        "paired verifier selected a different original AY subject".into(),
                    ));
                }
                for state in self.nodes.values() {
                    if let Some(previous) =
                        state.registered.as_ref().and_then(|row| row.original_compile_unit.as_ref())
                    {
                        if previous != unit {
                            return Err(Refusal(
                                "paired policies changed their original compile Unit".into(),
                            ));
                        }
                    }
                }
            }
            let state = self.nodes.get_mut(&registered.node).expect("decoded population");
            if state.registered.is_some() {
                return Err(Refusal("paired node registered twice".into()));
            }
            state.registered = Some(registered.clone());
            return Ok(Some(Event::Registered(registered)));
        }
        if let Ok(artifact) =
            service::Artifact::decode(bytes, &binding, &self.plan.consumer.output_root)
        {
            if self.nodes[&Node::ConsumerCompile].registered.is_none()
                || self.nodes[&Node::ConsumerCompile].terminal.is_some()
                || self.artifacts.insert(artifact.target, artifact.clone()).is_some()
            {
                return Err(Refusal(
                    "paired target artifact is repeated or outside original compilation".into(),
                ));
            }
            return Ok(Some(Event::Artifact(artifact)));
        }
        if let Ok(finished) = service::Finished::decode(bytes, &binding, repetitions) {
            self.finish_node(&finished)?;
            self.expected = Some((finished.node, Sha256::digest(bytes).into()));
            self.nodes.get_mut(&finished.node).expect("decoded population").terminal =
                Some(finished.clone());
            return Ok(Some(Event::Finished(finished)));
        }
        if let Ok(checkpoint) = service::Checkpoint::decode(bytes, &binding, repetitions) {
            if self.pending.is_some()
                || checkpoint.sequence != self.next
                || self.expected != Some((checkpoint.node, checkpoint.outcome_sha256))
            {
                return Err(Refusal(
                    "paired checkpoint does not bind its actual original terminal".into(),
                ));
            }
            self.expected = None;
            self.next += 1;
            self.pending = Some(checkpoint.clone());
            return Ok(Some(Event::Checkpoint(checkpoint)));
        }
        if let Ok(page) = service::decode_census(bytes, &binding) {
            if self.expected.is_some()
                || self.pending.is_some()
                || self.nodes.values().any(|state| !state.continued)
            {
                return Err(Refusal(
                    "paired census preceded complete original node continuations".into(),
                ));
            }
            self.census.as_mut().expect("Ready initializes reducer").append(page)?;
            return Ok(None);
        }
        if let Ok(final_observation) = service::Final::decode(bytes, &binding) {
            self.check_final(&final_observation)?;
            self.final_observation = Some(final_observation.clone());
            return Ok(Some(Event::Final(final_observation)));
        }
        Err(Refusal("unknown, malformed or misbound paired service frame".into()))
    }
    fn finish_node(&self, finished: &service::Finished) -> Result<()> {
        let state = &self.nodes[&finished.node];
        if state.registered.is_none()
            || state.terminal.is_some()
            || self.expected.is_some()
            || self.pending.is_some()
        {
            return Err(Refusal(
                "paired terminal is repeated, unregistered or precedes continuation".into(),
            ));
        }
        let scope = if finished.node.is_compile() {
            OutputScope::Diagnostics
        } else {
            OutputScope::NativeAction
        };
        let received = [Stream::Stdout, Stream::Stderr]
            .map(|stream| state.streams.get(&key(scope, stream)).map_or(0, |state| state.length));
        if received != finished.lengths {
            return Err(Refusal("paired terminal changed actual received output lengths".into()));
        }
        if matches!(finished.result, service::Result::Blocked { .. }) {
            return Ok(());
        }
        let prerequisite = |node| self.nodes[&node].continued;
        let ordered = match finished.node {
            Node::AyCompile => true,
            Node::Advisory => prerequisite(Node::AyCompile),
            Node::Strict => prerequisite(Node::Advisory),
            Node::ConsumerCompile => {
                [Node::AyCompile, Node::Advisory, Node::Strict].into_iter().all(prerequisite)
            }
            Node::Inventory { .. } => prerequisite(Node::ConsumerCompile),
            Node::Sample { target, repetition } => {
                (0..2).all(|target| prerequisite(Node::Inventory { target }))
                    && (0..repetition)
                        .all(|repetition| prerequisite(Node::Sample { target, repetition }))
            }
        };
        if !ordered
            || (finished.node.is_verification()
                && state
                    .registered
                    .as_ref()
                    .and_then(|row| row.original_compile_unit.as_ref())
                    .is_none())
        {
            return Err(Refusal(
                "paired action lacks its actual original prerequisites or Unit binding".into(),
            ));
        }
        if finished.node == Node::ConsumerCompile
            && matches!(finished.result, service::Result::Compiled { succeeded: true, .. })
            && self.artifacts.len() != 2
        {
            return Err(Refusal(
                "paired consumer compilation omitted its complete artifact population".into(),
            ));
        }
        Ok(())
    }
    fn check_final(&self, final_observation: &service::Final) -> Result<()> {
        if final_observation.repetitions != self.plan.consumer.repetitions
            || self.expected.is_some()
            || self.pending.is_some()
            || self.nodes.values().any(|state| !state.continued)
        {
            return Err(Refusal(
                "paired final omitted original phase population or continuations".into(),
            ));
        }
        let blocked = self
            .nodes
            .values()
            .filter(|state| {
                state
                    .terminal
                    .as_ref()
                    .is_some_and(|row| matches!(row.result, service::Result::Blocked { .. }))
            })
            .count();
        if blocked != final_observation.blocked as usize
            || self.nodes.len() - blocked != final_observation.finished as usize
        {
            return Err(Refusal("paired final changed complete phase counts".into()));
        }
        for node in [Node::AyCompile, Node::ConsumerCompile] {
            let state = &self.nodes[&node];
            if state.compiler_observation.is_none() {
                return Err(Refusal(
                    "paired revision2 final omitted declared compiler observation".into(),
                ));
            }
            for (scope, stream) in [
                (OutputScope::Diagnostics, Stream::Stdout),
                (OutputScope::Diagnostics, Stream::Stderr),
                (OutputScope::CompilerReport, Stream::Stdout),
            ] {
                if state
                    .streams
                    .get(&key(scope, stream))
                    .and_then(|state| state.end.as_ref())
                    .is_none()
                {
                    return Err(Refusal(
                        "paired final omitted an original logical writer end".into(),
                    ));
                }
            }
        }
        let census = self.census.as_ref().expect("Ready initializes reducer");
        census.check_finished(&trust_resource_controller::workload::service::finish::Graph {
            binding: trust_resource_controller::workload::service::Binding {
                root_attempt: final_observation.binding.root_attempt,
                invocation_sha256: final_observation.binding.invocation_sha256,
            },
            succeeded: false,
            snapshot: final_observation.snapshot,
            members: final_observation.members,
        })?;
        let mut seen = BTreeSet::new();
        for (node, state) in &self.nodes {
            let Some(service::Finished {
                result: service::Result::Captured { capture, .. }, ..
            }) = &state.terminal
            else {
                continue;
            };
            let kind = match node {
                Node::Advisory | Node::Strict => SourceKind::Compiler,
                Node::Inventory { .. } => SourceKind::Inventory,
                Node::Sample { .. } => SourceKind::Sample,
                _ => return Err(Refusal("paired native capture has a compile graph index".into())),
            };
            // A never-started known refusal is useful failed evidence and
            // cannot masquerade as a completed/metered native target.
            if !capture.started && capture.member_attempt.is_none() && capture.outcome.is_none() {
                continue;
            }
            let member = capture
                .member_attempt
                .ok_or_else(|| Refusal("paired capture omitted its original member".into()))?;
            let matching = census
                .entries()
                .iter()
                .filter(|entry| entry.member_attempt == member && entry.kind == kind)
                .collect::<Vec<_>>();
            if !seen.insert(member) || matching.len() != 1 {
                return Err(Refusal(
                    "paired native member missing or repeated in complete census".into(),
                ));
            }
            let entry = matching[0];
            let Status::Finished { outcome, cause, runtime_ns } = entry.terminal else {
                return Err(Refusal(
                    "paired capture lacks matching original target terminal".into(),
                ));
            };
            if !capture.started
                || !capture.retirement_confirmed
                || !entry.retired
                || !entry.drained
                || entry.identity.is_none()
                || entry.started.is_none()
                || capture.outcome != Some(outcome)
                || capture.cause != Some(cause)
                || capture.runtime_ns != Some(runtime_ns)
                || capture.accounting != Some(entry.accounting)
            {
                return Err(Refusal(
                    "paired native result differs from original owning-wait census".into(),
                ));
            }
        }
        if census.entries().iter().any(|entry| {
            !entry.retired
                || !entry.drained
                || (matches!(entry.kind, SourceKind::Inventory | SourceKind::Sample)
                    && !seen.contains(&entry.member_attempt))
        }) {
            return Err(Refusal(
                "paired census has uncertain retirement or an unreported harness action".into(),
            ));
        }
        Ok(())
    }
    pub fn native_complete(finished: &service::Finished) -> bool {
        matches!(&finished.result, service::Result::Captured { capture, input_failure: None, .. }
            if capture.started && capture.retirement_confirmed && capture.failure.is_none()
            && capture.member_attempt.is_some() && capture.cause == Some(CompletionCause::Exited)
            && matches!(capture.outcome, Some(Outcome::Exit(_))))
            && finished.ends == [service::StreamEnd::Eof; 2]
            && finished.truncated == [false; 2]
    }
    pub fn measured(&self) -> bool {
        self.final_observation.as_ref().is_some_and(|finished| finished.inputs_unchanged)
            && self.failure.is_none()
            && [Node::AyCompile, Node::ConsumerCompile].into_iter().all(|node| {
                self.nodes[&node]
                    .compiler_observation
                    .as_ref()
                    .and_then(|observation| observation.counts.as_ref())
                    .is_some_and(|counts| counts.successful_primary_processes.is_some())
                    && self.nodes[&node].streams.values().all(|stream| {
                        stream.end.as_ref().is_some_and(|end| end.writer_closed && !end.truncated)
                    })
            })
            && self.census.as_ref().is_some_and(|census| {
                census.entries().iter().all(|entry| {
                    entry.accounting.cpu_times.is_some()
                        && entry.accounting.peak_rss_bytes.is_some()
                })
            })
            && self.nodes.values().filter_map(|state| state.terminal.as_ref()).all(|finished| {
                match &finished.result {
                    service::Result::Captured { capture, .. } => {
                        Self::native_complete(finished)
                            && capture.accounting.is_some_and(|observation| {
                                observation.cpu_times.is_some()
                                    && observation.peak_rss_bytes.is_some()
                            })
                    }
                    service::Result::Compiled { succeeded, local_workers_joined, .. } => {
                        *succeeded && *local_workers_joined
                    }
                    service::Result::Blocked { .. } => false,
                }
            })
    }
    pub fn compiler_observations(
        &self,
    ) -> impl Iterator<Item = &service::compiler_observation::Observation> {
        self.nodes.values().filter_map(|state| state.compiler_observation.as_ref())
    }
    /// Borrow checked observation data only; no live execution rights escape.
    pub fn outcomes(&self) -> impl Iterator<Item = &service::Finished> {
        self.nodes.values().filter_map(|state| state.terminal.as_ref())
    }
}

#[cfg(test)]
pub(super) mod tests;
