//! One real retained Targo graph per side, using the existing native root
//! process owner. Service records are consistency data; they grant no custody.
use std::fs::{self, File};
use std::io::Write as _;
use std::os::fd::OwnedFd;
use std::os::unix::fs::{DirBuilderExt as _, MetadataExt as _};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use trust_qualification::dependencies::{ResolverOutcome, Side};
use trust_qualification::workloads::{self, Capture, Compilation, Event, Measurement, Request};
use trust_qualification::{Refusal, Result, pair};
use trust_resource_controller::accounting::Observation;
use trust_resource_controller::workload::service::checkpoint::{self, Body};
use trust_resource_controller::workload::{self, InputFile, WorkloadInvocation, budget, service};
use trust_resource_controller::{CompletionCause, Outcome, Status};
use trust_test_execution::workload::{Action, TARGETS};

use crate::native_root_transport::{self as transport, RootCapture, RootSpec, hex};

#[path = "io.rs"]
pub(crate) mod io;
#[path = "protocol.rs"]
mod protocol;
#[cfg(test)]
#[path = "tests.rs"]
mod tests;

// Every permitted checkpoint can contain two complete 64MiB streams. Include
// postcompiler diagnostics, framing and the complete bounded census on disk.
// Retained in-memory stdout is only a labelled 64KiB prefix.
const RAW_STDOUT_MAX: usize =
    if usize::BITS >= 64 { (10u64 * 1024 * 1024 * 1024) as usize } else { usize::MAX };
const PREFIX: usize = 64 * 1024;
const ROOT_STDERR_MAX: usize = 1024 * 1024;

struct ResultRoot {
    path: PathBuf,
    descriptor: File,
    key: (u64, u64),
}
impl ResultRoot {
    fn check(&self) -> Result<()> {
        let held = self.descriptor.metadata()?;
        let named = fs::symlink_metadata(&self.path)?;
        if !named.is_dir()
            || named.file_type().is_symlink()
            || (held.dev(), held.ino()) != self.key
            || (named.dev(), named.ino()) != self.key
        {
            return Err(Refusal("original workload result directory changed".into()));
        }
        Ok(())
    }
}
pub(crate) struct NativeWorkloadProducer {
    host_store: Option<PathBuf>,
    output: Option<ResultRoot>,
    observation: Option<Value>,
}
impl NativeWorkloadProducer {
    pub(crate) fn new(host_store: Option<PathBuf>) -> Self {
        Self { host_store, output: None, observation: None }
    }
    pub(crate) fn evidence_root(&mut self, request: &Request) -> Result<PathBuf> {
        let parent = request
            .target_directory
            .parent()
            .ok_or_else(|| Refusal("workload target has no result parent".into()))?;
        self.evidence_root_at(request.side, parent)
    }
    pub(crate) fn evidence_root_at(
        &mut self,
        side: Side,
        parent: &std::path::Path,
    ) -> Result<PathBuf> {
        if self.output.is_none() {
            if side != Side::Control {
                return Err(Refusal("candidate cannot create a second result owner".into()));
            }
            let mut builder = fs::DirBuilder::new();
            builder.mode(0o700).create(parent)?;
            let descriptor = fs::OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(parent)?;
            let actual = descriptor.metadata()?;
            self.output = Some(ResultRoot {
                path: parent.into(),
                descriptor,
                key: (actual.dev(), actual.ino()),
            });
        }
        let owner = self.output.as_ref().expect("created original output owner");
        owner.check()?;
        if owner.path != parent {
            return Err(Refusal("candidate differs from the original result owner".into()));
        }
        let root = parent.join(match side {
            Side::Control => "control-evidence",
            Side::Candidate => "candidate-evidence",
        });
        fs::DirBuilder::new().mode(0o700).create(&root)?;
        owner.check()?;
        Ok(root)
    }
}
use std::os::unix::fs::OpenOptionsExt as _;

fn digest(text: &str) -> Result<[u8; 32]> {
    if text.len() != 64 || !text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
        return Err(Refusal("native workload input digest must be exact lowercase SHA256".into()));
    }
    let mut out = [0; 32];
    for (at, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[2 * at..2 * at + 2], 16)
            .map_err(|e| Refusal(e.to_string()))?;
    }
    Ok(out)
}
fn input(original: &pair::FileIdentity) -> Result<InputFile> {
    if pair::file_identity(&original.path)? != *original {
        return Err(Refusal("original workload executable/fixture changed before delivery".into()));
    }
    Ok(InputFile {
        path: original.path.as_os_str().as_encoded_bytes().to_vec(),
        sha256: digest(&original.sha256)?,
    })
}
pub(crate) fn invocation(request: &Request, store: &Option<PathBuf>) -> Result<WorkloadInvocation> {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        return Err(Refusal(
            "native paired workload currently requires macOS arm64 custody".into(),
        ));
    }
    if request.program.path != request.sdk_root.join("bin/targo")
        || request.compiler.path != request.sdk_root.join("bin/trustc")
    {
        return Err(Refusal("workload must use both exact original sealed SDK siblings".into()));
    }
    let fixture =
        |name: &str| -> Result<InputFile> {
            input(request.proof_fixtures.get(name).ok_or_else(|| {
                Refusal("original workload fixture population is incomplete".into())
            })?)
        };
    let mut nonce = [0; 16];
    getrandom::fill(&mut nonce).map_err(|e| Refusal(e.to_string()))?;
    let value = WorkloadInvocation {
        invocation: nonce,
        observed_host_store: store.as_ref().map(|p| p.as_os_str().as_encoded_bytes().to_vec()),
        root: request.sdk_root.as_os_str().as_encoded_bytes().to_vec(),
        program: input(&request.program)?,
        compiler: input(&request.compiler)?,
        cwd: request.cwd.as_os_str().as_encoded_bytes().to_vec(),
        cargo_home: request.cargo_home.as_os_str().as_encoded_bytes().to_vec(),
        output_root: request.target_directory.as_os_str().as_encoded_bytes().to_vec(),
        refutation_step: fixture("crates/ay-pb/proofs/trust_vc/refutation_step_realbody.rs")?,
        refutation_loop: fixture("crates/ay-pb/proofs/trust_vc/refutation_loop_realbody.rs")?,
        trust_spec_source: input(&request.trust_spec_source)?,
        repetitions: request.repetitions,
        timeout_ns: request.timeout_ns,
    };
    value.validate()?;
    Ok(value)
}
impl workloads::Producer for NativeWorkloadProducer {
    fn start_observation(&self) -> Option<Value> {
        self.observation.clone()
    }
    fn start(&mut self, request: &Request) -> Result<Box<dyn workloads::Run>> {
        self.observation = Some(
            json!({"scope":"attempted original native workload root; no source/proof/admission authority from this record","request":request}),
        );
        // A pinned private helper does not select the actual GUI root backend.
        // The peer is implementing expectation-only original-directory intake.
        if self.host_store.is_some() {
            return Err(Refusal("private workload root requires original-store root CLI intake; account fallback is forbidden".into()));
        }
        let invocation = invocation(request, &self.host_store)?;
        let root = self.evidence_root(request)?;
        let mut run = Run::launch(request.clone(), invocation, self.host_store.clone(), root)?;
        let ready = run.await_ready();
        if let Err(error) = ready {
            run.failure.get_or_insert_with(|| error.0.clone());
            let _ = run.stop_inner();
            self.observation = Some(run.observation_value());
            return Err(error);
        }
        self.observation = Some(run.observation_value());
        Ok(Box::new(run))
    }
}

struct ActionFact {
    member: [u8; 16],
    kind: workload::host::census::SourceKind,
    capture: checkpoint::Capture,
}
struct Run {
    request: Request,
    protocol: protocol::Protocol,
    writer: Option<UnixStream>,
    receiver: mpsc::Receiver<io::Input>,
    finished: mpsc::Receiver<Result<RootCapture>>,
    owner: Option<JoinHandle<()>>,
    pump: Arc<Mutex<io::Pump>>,
    cancelled: Arc<AtomicBool>,
    deadline: Instant,
    started: Instant,
    stdout_eof: bool,
    failure: Option<String>,
    observation: Value,
    actions: Vec<ActionFact>,
    settled: Option<Capture>,
}
impl Run {
    fn launch(
        request: Request,
        invocation: WorkloadInvocation,
        store: Option<PathBuf>,
        root: PathBuf,
    ) -> Result<Self> {
        let started = Instant::now();
        let budget = budget::Budget::new(invocation.repetitions, invocation.timeout_ns)?;
        let deadline = started
            .checked_add(budget.root_duration())
            .and_then(|d| d.checked_add(Duration::from_nanos(budget::STARTUP_NS)))
            .ok_or_else(|| {
                Refusal("original complete workload deadline cannot be represented".into())
            })?;
        let protocol = protocol::Protocol::new(invocation.clone())?;
        let bytes = invocation.encode()?;
        let (mut writer, reader) = UnixStream::pair()?;
        writer.set_write_timeout(Some(Duration::from_nanos(budget::CHECKPOINT_NS)))?;
        write_frame(&mut writer, &bytes, deadline)?;
        let input = File::from(OwnedFd::from(reader));
        let (sender, receiver) = mpsc::sync_channel(16);
        let (complete, finished) = mpsc::channel();
        let cancelled = Arc::new(AtomicBool::new(false));
        let pump = io::Pump::new(&root, sender, deadline, Arc::clone(&cancelled))?;
        let observed = Arc::clone(&pump);
        let conversation = crate::bounded_process::Conversation::new(
            Arc::new(move |index, bytes| io::lock(&observed, deadline)?.accept(index, bytes)),
            Arc::clone(&cancelled),
            PREFIX,
        );
        let actual = request.clone();
        let owner = std::thread::Builder::new().name("paired-native-workload-owner".into()).spawn(
            move || {
                let environment = [
                    ("CARGO_HOME", actual.cargo_home.as_os_str()),
                    ("CARGO", actual.program.path.as_os_str()),
                    ("RUSTC", actual.compiler.path.as_os_str()),
                    ("CARGO_CACHE_RUSTC_INFO", std::ffi::OsStr::new("0")),
                ];
                let capture = transport::capture_interactive(
                    RootSpec {
                        program: &actual.program.path,
                        cwd: &actual.cwd,
                        entry: workload::WORKLOAD_STARTUP_ARGUMENT,
                        environment: &environment,
                        input: &bytes,
                        max_output: RAW_STDOUT_MAX,
                        max_stderr: ROOT_STDERR_MAX,
                        job: "trust-native-paired-workload",
                    },
                    &store,
                    transport::Interactive {
                        input,
                        deadline,
                        root_timeout_ms: budget.root_timeout_ms,
                        conversation,
                        protocol: transport::InteractiveProtocol::Workload,
                    },
                );
                let _ = complete.send(capture);
            },
        )?;
        Ok(Self {
            request,
            protocol,
            writer: Some(writer),
            receiver,
            finished,
            owner: Some(owner),
            pump,
            cancelled,
            deadline,
            started,
            stdout_eof: false,
            failure: None,
            observation: json!({"raw_evidence_directory":root,"root_timeout_ms":budget.root_timeout_ms}),
            actions: Vec::new(),
            settled: None,
        })
    }
    fn await_ready(&mut self) -> Result<()> {
        let until = (self.started + Duration::from_nanos(budget::STARTUP_NS)).min(self.deadline);
        loop {
            match self.next(until)? {
                Some(protocol::Event::Ready) => return Ok(()),
                Some(_) => {
                    return Err(Refusal(
                        "original native workload omitted its first readiness frame".into(),
                    ));
                }
                None => {}
            }
        }
    }
    fn next(&mut self, until: Instant) -> Result<Option<protocol::Event>> {
        loop {
            if Instant::now() >= until {
                return Err(Refusal(
                    "original native workload conversation deadline expired".into(),
                ));
            }
            match self.receiver.recv_timeout(
                until.saturating_duration_since(Instant::now()).min(Duration::from_millis(50)),
            ) {
                Ok(io::Input::Frame(bytes)) => return self.protocol.frame(&bytes),
                Ok(io::Input::Eof) => {
                    self.stdout_eof = true;
                    return Err(Refusal(
                        "native workload stream ended before its required checkpoint/graph".into(),
                    ));
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    if self.owner.as_ref().is_some_and(|owner| owner.is_finished()) {
                        // Drain all actual queued frames before reporting the
                        // process ending; the final result stays for settlement.
                        match self.receiver.try_recv() {
                            Ok(io::Input::Frame(bytes)) => return self.protocol.frame(&bytes),
                            Ok(io::Input::Eof) => self.stdout_eof = true,
                            Err(_) => {}
                        }
                        return Err(Refusal(
                            "original native CLI ended without its required service frame".into(),
                        ));
                    }
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(Refusal("original native workload read channel closed".into()));
                }
            }
        }
    }
    fn continue_original(&mut self) -> Result<()> {
        if let Some(continuation) = self.protocol.take_continuation() {
            let until =
                (Instant::now() + Duration::from_nanos(budget::CHECKPOINT_NS)).min(self.deadline);
            write_frame(
                self.writer
                    .as_mut()
                    .ok_or_else(|| Refusal("original continuation writer closed".into()))?,
                &continuation.encode()?,
                until,
            )?;
        }
        Ok(())
    }
    fn checkpoint(&mut self, output: protocol::CheckpointOutput) -> Result<Event> {
        let sequence = output.checkpoint.sequence;
        match output.checkpoint.body {
            Body::Compiled {
                succeeded,
                workers_retired,
                output_complete,
                jobs,
                artifacts,
                failure,
            } => {
                let mut inputs = Vec::new();
                for artifact in artifacts {
                    inputs.push(workloads::Artifact {
                        target: TARGETS[artifact.target as usize].into(),
                        input: artifact_identity(
                            &artifact.executable,
                            &self.request.target_directory,
                        )?,
                    });
                }
                Ok(Event::Compiled(Compilation {
                    stdout: output.stdout,
                    stderr: output.stderr,
                    succeeded,
                    workers_retired,
                    output_complete: output_complete
                        && output.end.closed == [true, true]
                        && !output.end.truncated.into_iter().any(|v| v),
                    artifacts: inputs,
                    unit_observations: json!({"checkpoint":sequence,"jobs":jobs,"failure":failure,
                        "scope":"compiler graph checkpoint; complete original member census follows after same-root drain"}),
                }))
            }
            Body::Harness { target, action, capture } => {
                let source = match action {
                    checkpoint::Action::Inventory => workload::host::census::SourceKind::Inventory,
                    checkpoint::Action::Sample { .. } => workload::host::census::SourceKind::Sample,
                };
                if let Some(member) = capture.member_attempt {
                    self.actions.push(ActionFact {
                        member,
                        kind: source,
                        capture: capture.clone(),
                    });
                } else {
                    self.failure
                        .get_or_insert("native action omitted its original member binding".into());
                }
                let observation = json!({"checkpoint":sequence,"member_attempt":capture.member_attempt.map(|m|hex(&m)),
                    "started":capture.started,"target":TARGETS[target as usize],"scope":"original target owning wait; separate from Root/helper CPU"});
                let actual = Capture {
                    stdout: output.stdout,
                    stderr: output.stderr,
                    outcome: outcome(capture.outcome),
                    cause: capture.cause,
                    retirement_confirmed: capture.retirement_confirmed,
                    stdout_eof: output.end.closed[0],
                    stderr_eof: output.end.closed[1],
                    output_limit_exceeded: output.end.truncated.into_iter().any(|v| v),
                    failure: capture.failure,
                    measurement: capture.accounting.map(|accounting| Measurement {
                        target_runtime_ns: capture.runtime_ns,
                        accounting,
                    }),
                    producer_observation: observation,
                };
                Ok(Event::Harness {
                    target: TARGETS[target as usize].into(),
                    action: match action {
                        checkpoint::Action::Inventory => Action::Inventory,
                        checkpoint::Action::Sample { repetition } => Action::Sample { repetition },
                    },
                    capture: actual,
                })
            }
        }
    }
    fn validate_census(&self) -> Result<()> {
        let graph = self
            .protocol
            .graph
            .as_ref()
            .ok_or_else(|| Refusal("original graph completion absent".into()))?;
        let census = self
            .protocol
            .census
            .as_ref()
            .ok_or_else(|| Refusal("original member census absent".into()))?;
        census.check_finished(graph)?;
        let entries = census.entries();
        if entries
            .iter()
            .filter(|entry| {
                matches!(
                    entry.kind,
                    workload::host::census::SourceKind::Inventory
                        | workload::host::census::SourceKind::Sample
                )
            })
            .count()
            != self.actions.len()
        {
            return Err(Refusal(
                "complete original census has additional/unobserved native workload actions".into(),
            ));
        }
        let mut seen = std::collections::BTreeSet::new();
        for action in &self.actions {
            let matches = entries
                .iter()
                .filter(|entry| entry.member_attempt == action.member && entry.kind == action.kind)
                .collect::<Vec<_>>();
            if !seen.insert(action.member) || matches.len() != 1 {
                return Err(Refusal(
                    "native checkpoint member missing/repeated in complete original census".into(),
                ));
            }
            let entry = matches[0];
            let Status::Finished { outcome, cause, runtime_ns } = entry.terminal else {
                return Err(Refusal("native action census lacks actual completed outcome".into()));
            };
            if !entry.retired
                || !entry.drained
                || entry.started.is_none()
                || entry.identity.is_none()
                || !action.capture.started
                || !action.capture.retirement_confirmed
                || action.capture.outcome != Some(outcome)
                || action.capture.cause != Some(cause)
                || action.capture.runtime_ns != Some(runtime_ns)
                || action.capture.accounting != Some(entry.accounting)
            {
                return Err(Refusal(
                    "native checkpoint differs from its original completed member census".into(),
                ));
            }
        }
        for entry in entries {
            if !entry.retired
                || !entry.drained
                || !matches!(
                    entry.terminal,
                    Status::Finished { cause: CompletionCause::Exited, .. }
                )
                || entry.accounting.cpu_times.is_none()
                || entry.accounting.peak_rss_bytes.is_none()
            {
                return Err(Refusal("complete original member census has unknown retirement or missing owning-wait measurements".into()));
            }
        }
        Ok(())
    }
    fn census_data(&self) -> Value {
        let Some(census) = self.protocol.census.as_ref() else {
            return Value::Null;
        };
        let graph = self.protocol.graph.as_ref();
        json!({"snapshot":graph.map(|graph|hex(&graph.snapshot)),
            "complete":graph.is_some_and(|graph|census.check_finished(graph).is_ok()),
            "members":census.entries().iter().map(|entry|json!({
            "member_attempt":hex(&entry.member_attempt),"kind":format!("{:?}",entry.kind),
            "identity":entry.identity.map(|identity|json!({"pid":identity.pid,"birth":identity.birth})),
            "started":entry.started.as_ref().map(|started|json!({"monotonic_ns":started.monotonic_ns,"unix_ns":started.unix_ns})),
            "terminal":format!("{:?}",entry.terminal),"retired":entry.retired,"drained":entry.drained,
            "accounting":accounting_json(entry.accounting),
        })).collect::<Vec<_>>(),"scope":"all received registered target roles, including failed/unknown; do not sum with overlapping Root/helper waits"})
    }
    fn settle(&mut self) -> Result<Capture> {
        if let Some(capture) = &self.settled {
            return Ok(clone_capture(capture));
        }
        let settlement =
            (Instant::now() + Duration::from_nanos(budget::SETTLEMENT_NS)).min(self.deadline);
        // Keep consuming the original bounded channel while the SAME owner
        // drains; otherwise backpressure could deadlock its observer at EOF.
        let capture = loop {
            match self.finished.try_recv() {
                Ok(result) => break result,
                Err(mpsc::TryRecvError::Disconnected) => {
                    break Err(Refusal("original capture owner ended without result".into()));
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            if Instant::now() >= settlement {
                self.cancelled.store(true, Ordering::Release);
            }
            match self.receiver.recv_timeout(Duration::from_millis(20)) {
                Ok(io::Input::Eof) => self.stdout_eof = true,
                Ok(io::Input::Frame(bytes)) => {
                    if self.protocol.failure.is_none() {
                        if let Err(error) = self.protocol.frame(&bytes) {
                            self.failure.get_or_insert(error.0);
                        }
                    }
                }
                Err(_) => {}
            }
        };
        self.writer.take();
        if let Some(owner) = self.owner.take() {
            if owner.join().is_err() {
                self.failure.get_or_insert("original native capture thread panicked".into());
            }
        }
        while let Ok(input) = self.receiver.try_recv() {
            match input {
                io::Input::Eof => self.stdout_eof = true,
                io::Input::Frame(bytes) => {
                    if self.protocol.failure.is_none() {
                        if let Err(error) = self.protocol.frame(&bytes) {
                            self.failure.get_or_insert(error.0);
                        }
                    }
                }
            }
        }
        let elapsed_through_drain = self.started.elapsed();
        let raw = match io::lock(&self.pump, self.deadline) {
            Ok(mut pump) => pump.finish(),
            Err(error) => {
                self.failure.get_or_insert(format!("original raw evidence incomplete: {error}"));
                json!({"failure":error.to_string()})
            }
        };
        let mut result = Capture {
            stdout: Vec::new(),
            stderr: Vec::new(),
            outcome: ResolverOutcome::Unknown,
            cause: None,
            retirement_confirmed: false,
            stdout_eof: false,
            stderr_eof: false,
            output_limit_exceeded: false,
            failure: self.failure.clone(),
            measurement: None,
            producer_observation: Value::Null,
        };
        self.observation["actual_outer_raw_capture"] = raw;
        self.observation["complete_original_member_census"] = self.census_data();
        match capture {
            Err(error) => {
                result.failure.get_or_insert(error.0);
            }
            Ok(capture) => {
                self.observation["actual_root_transport"] = capture.observation;
                if let Some(prefix) = capture.conversation_output {
                    result.stdout_eof = prefix.eof[0];
                    result.stderr_eof = prefix.eof[1];
                    result.stderr = prefix.bytes[1].clone();
                    result.output_limit_exceeded = prefix.bytes_seen[0] > RAW_STDOUT_MAX as u64
                        || prefix.bytes_seen[1] > ROOT_STDERR_MAX as u64;
                }
                let checked = (|| -> Result<()> {
                    if !capture.image_valid {
                        return Err(Refusal(
                            "original native custodian image validation failed".into(),
                        ));
                    }
                    let exit = capture.exit_observation.ok_or_else(|| {
                        Refusal("actual outer CLI owning wait unavailable".into())
                    })?;
                    let root = transport::validate_accounted_statuses(
                        &capture.statuses.map_err(Refusal)?,
                        &exit,
                    )?;
                    result.outcome = root.outcome;
                    result.cause = Some(root.cause);
                    result.retirement_confirmed = true;
                    result.measurement = root.accounting.map(|accounting| Measurement {
                        target_runtime_ns: Some(root.runtime_ns),
                        accounting,
                    });
                    if root.accounting.is_none_or(|value| {
                        value.cpu_times.is_none() || value.peak_rss_bytes.is_none()
                    }) {
                        return Err(Refusal(
                            "original root owning-wait measurements are unavailable".into(),
                        ));
                    }
                    let ready = self
                        .protocol
                        .ready
                        .as_ref()
                        .ok_or_else(|| Refusal("original service Ready absent".into()))?;
                    if ready.original_root.pid != root.pid
                        || ready.original_root.birth != root.birth
                        || hex(&ready.binding.root_attempt) != root.attempt
                    {
                        return Err(Refusal(
                            "original service process/binding differs from actual root lifecycle"
                                .into(),
                        ));
                    }
                    capture.output.map_err(Refusal)?;
                    if !self.stdout_eof || !result.stdout_eof || !result.stderr_eof {
                        return Err(Refusal("original workload streams lack physical EOF".into()));
                    }
                    if self.protocol.failure.is_some() {
                        return Err(Refusal("original service protocol failed".into()));
                    }
                    self.validate_census()?;
                    if self
                        .protocol
                        .graph
                        .as_ref()
                        .is_none_or(|graph| graph.succeeded != root.normal)
                    {
                        return Err(Refusal(
                            "original graph success differs from its actual root outcome".into(),
                        ));
                    }
                    Ok(())
                })();
                if let Err(error) = checked {
                    result.failure.get_or_insert(error.0);
                }
            }
        }
        for original in [&self.request.program, &self.request.compiler] {
            if !matches!(pair::file_identity(&original.path),Ok(current) if &current==original) {
                result.failure.get_or_insert(
                    "original workload SDK executable drifted at final handoff".into(),
                );
            }
        }
        self.observation["invocation_elapsed_through_outer_exit_and_drain_ns"] =
            json!(u64::try_from(elapsed_through_drain.as_nanos()).ok());
        self.observation["diagnostic_stream_lengths"] = json!(self.protocol.diagnostic_lengths());
        self.observation["graph_succeeded"] =
            json!(self.protocol.graph.as_ref().map(|g| g.succeeded));
        self.observation["final_root_observation"] = json!({"outcome":result.outcome,"cause":result.cause.map(|cause|format!("{cause:?}")),
            "retirement_confirmed":result.retirement_confirmed,"stdout_eof":result.stdout_eof,"stderr_eof":result.stderr_eof,
            "failure":result.failure,"owning_wait":result.measurement.map(|value|json!({"target_runtime_ns":value.target_runtime_ns,
                "accounting":accounting_json(value.accounting)}))});
        result.producer_observation = self.observation_value();
        self.settled = Some(clone_capture(&result));
        Ok(result)
    }
    fn stop_inner(&mut self) -> Result<Capture> {
        if self.settled.is_some() {
            return self.settle();
        }
        if self.protocol.graph.is_none() {
            let stop = self
                .protocol
                .binding()
                .ok()
                .cloned()
                .and_then(|binding| service::Stop { binding }.encode().ok());
            let sent = stop.and_then(|bytes| {
                self.writer.as_mut().map(|writer| {
                    write_frame(
                        writer,
                        &bytes,
                        (Instant::now() + Duration::from_secs(1)).min(self.deadline),
                    )
                })
            });
            if !matches!(sent, Some(Ok(()))) {
                self.cancelled.store(true, Ordering::Release);
            }
        }
        self.settle()
    }
    fn observation_value(&self) -> Value {
        let mut value = self.observation.clone();
        value["failure"] = json!(self.failure);
        value["protocol_failure"] = json!(self.protocol.failure);
        value["scope"] = json!(
            "one original live root/graph; records, metrics and ACKs grant no admission/proof/source authority"
        );
        value
    }
}
impl workloads::Run for Run {
    fn advance(&mut self) -> Result<Event> {
        if self.settled.is_some() {
            return Err(Refusal("original workload already settled".into()));
        }
        let result = (|| {
            self.continue_original()?;
            loop {
                match self.next(self.deadline)? {
                    Some(protocol::Event::Checkpoint(output)) => return self.checkpoint(output),
                    Some(protocol::Event::Graph) => {
                        return Ok(Event::Finished { capture: self.settle()? });
                    }
                    Some(protocol::Event::Ready) => {
                        return Err(Refusal("original service repeated readiness".into()));
                    }
                    None => {}
                }
            }
        })();
        if let Err(error) = &result {
            self.failure.get_or_insert(error.0.clone());
        }
        result
    }
    fn stop(&mut self) -> Result<Capture> {
        self.stop_inner()
    }
    fn observation(&self) -> Value {
        self.observation_value()
    }
}
impl Drop for Run {
    fn drop(&mut self) {
        if self.owner.is_some() {
            let _ = self.stop_inner();
        }
    }
}
pub(crate) fn write_frame(writer: &mut UnixStream, bytes: &[u8], deadline: Instant) -> Result<()> {
    if bytes.is_empty()
        || bytes.len() > trust_resource_controller::MAX_PAYLOAD
        || Instant::now() >= deadline
    {
        return Err(Refusal("invalid or expired original native frame write".into()));
    }
    writer.set_write_timeout(Some(
        deadline.saturating_duration_since(Instant::now()).max(Duration::from_millis(1)),
    ))?;
    writer.write_all(&(bytes.len() as u32).to_be_bytes())?;
    writer.write_all(bytes)?;
    Ok(())
}
fn outcome(value: Option<Outcome>) -> ResolverOutcome {
    match value {
        Some(Outcome::Exit(code)) if (0..=255).contains(&code) => ResolverOutcome::Exit(code),
        Some(Outcome::Signal(signal)) if (1..=127).contains(&signal) => {
            ResolverOutcome::Signal(signal)
        }
        _ => ResolverOutcome::Unknown,
    }
}
fn accounting_json(value: Observation) -> Value {
    json!({"scope":"child-and-waited-descendants-v1","cpu_times":value.cpu_times.map(|cpu|json!({"user_ns":cpu.user_ns,"system_ns":cpu.system_ns})),"peak_rss_bytes":value.peak_rss_bytes})
}
/// Expected digest data for the retained consumer's independent hash/descriptor
/// check. This read checks publication identity, never execution eligibility.
pub(crate) fn artifact_identity(
    file: &trust_resource_controller::MetadataFile,
    target: &std::path::Path,
) -> Result<pair::FileIdentity> {
    use std::os::unix::ffi::OsStringExt as _;
    let path = PathBuf::from(std::ffi::OsString::from_vec(file.path.clone()));
    let actual = fs::symlink_metadata(&path)?;
    if !path.starts_with(target)
        || !actual.is_file()
        || actual.file_type().is_symlink()
        || actual.mode() & 0o111 == 0
        || actual.nlink() != 1
        || actual.dev() != file.device
        || actual.ino() != file.inode
        || actual.len() != file.bytes
        || fs::canonicalize(&path)? != path
    {
        return Err(Refusal(
            "reported native artifact differs from its original current publication identity"
                .into(),
        ));
    }
    Ok(pair::FileIdentity {
        path: path.clone(),
        resolved_path: path,
        sha256: hex(&file.sha256),
        link_text: None,
    })
}
fn clone_capture(capture: &Capture) -> Capture {
    Capture {
        stdout: capture.stdout.clone(),
        stderr: capture.stderr.clone(),
        outcome: capture.outcome,
        cause: capture.cause,
        retirement_confirmed: capture.retirement_confirmed,
        stdout_eof: capture.stdout_eof,
        stderr_eof: capture.stderr_eof,
        output_limit_exceeded: capture.output_limit_exceeded,
        failure: capture.failure.clone(),
        measurement: capture.measurement,
        producer_observation: capture.producer_observation.clone(),
    }
}
