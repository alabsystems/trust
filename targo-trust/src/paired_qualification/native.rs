//! The real paired frontend owns the original DependencyAttempt until both
//! disjoint root lifetimes end. Service bytes and ACKs grant no execution.
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use trust_qualification::dependencies::{DependencyAttempt, Side};
use trust_qualification::workloads::{ArtifactInput, Options, Request};
use trust_qualification::{Git, Refusal, Result, pair};
use trust_resource_controller::paired_qualification::{
    self as paired, AySubject, PairedInvocation, service,
};
use trust_test_execution::workload::{Inventory, TARGETS};

use super::ledger::Ledger;
use super::protocol::{Event, Protocol};
use crate::native_root_transport::{self as transport, InteractiveProtocol, RootCapture, RootSpec};
use crate::native_workload_root::{self as shared, io};
mod cache;
mod costs;

const RAW_MAX: usize =
    if usize::BITS >= 64 { (10u64 * 1024 * 1024 * 1024) as usize } else { usize::MAX };
const ROOT_STDERR_MAX: usize = 1024 * 1024;

struct NativeRun {
    protocol: Protocol,
    plan: PairedInvocation,
    request: Request,
    writer: Option<UnixStream>,
    receiver: mpsc::Receiver<io::Input>,
    owner: Option<JoinHandle<Result<RootCapture>>>,
    pump: Arc<Mutex<io::Pump>>,
    cancelled: Arc<AtomicBool>,
    deadline: Instant,
    started: Instant,
    physical_eof: bool,
    failure: Option<String>,
    records: Vec<Value>,
    raw: BTreeMap<service::Node, [Vec<u8>; 2]>,
    artifacts: BTreeMap<u32, ArtifactInput>,
    ledgers: BTreeMap<service::Node, Ledger>,
    inventories: BTreeMap<u32, Inventory>,
    samples: BTreeSet<(u32, u32)>,
    root: Option<Value>,
    evidence_root: PathBuf,
    retired: bool,
    root_succeeded: bool,
    measured: bool,
    cache: Option<Arc<cache::Cache>>,
    // Read-only compatibility/input custody only. The actual Host must still
    // retain/admit its independently selected original SDK keeper and image.
    input_program: trust_resource_provenance::program::HeldProgram,
    node_started: BTreeMap<service::Node, Instant>,
    node_intervals: BTreeMap<service::Node, Option<u64>>,
    root_cost: Option<costs::RootObservation>,
}
impl NativeRun {
    fn launch(
        request: Request,
        plan: PairedInvocation,
        store: Option<PathBuf>,
        root: PathBuf,
        cache: Option<Arc<cache::Cache>>,
    ) -> Result<Self> {
        let budget =
            paired::budget::Budget::new(plan.consumer.repetitions, plan.consumer.timeout_ns)?;
        let started = Instant::now();
        let deadline = started
            .checked_add(budget.root_duration())
            .ok_or_else(|| Refusal("paired original deadline is unrepresentable".into()))?;
        let bytes = plan.encode()?;
        let protocol = Protocol::new(plan.clone())?;
        let compatibility_deadline = (started
            + Duration::from_nanos(trust_resource_controller::workload::budget::STARTUP_NS))
        .min(deadline);
        // A live Ready alone is too late: an old producer may configure the
        // project immediately after sending it. Refuse its actual held image
        // BEFORE any resource-run child/delivery, even when the Host is old.
        let input_program =
            retain_input_program(&request.sdk_root, &request.program, compatibility_deadline)?;
        let (reader, mut writer) = UnixStream::pair()?;
        shared::write_frame(&mut writer, &bytes, (started + Duration::from_secs(1)).min(deadline))?;
        let input = File::from(OwnedFd::from(reader));
        let (sender, receiver) = mpsc::sync_channel(16);
        let cancelled = Arc::new(AtomicBool::new(false));
        let pump = io::Pump::new(&root, sender, deadline, cancelled.clone())?;
        let observed = pump.clone();
        let conversation = crate::bounded_process::Conversation::new(
            Arc::new(move |index, bytes| io::lock(&observed, deadline)?.accept(index, bytes)),
            cancelled.clone(),
            64 * 1024,
        );
        let actual = request.clone();
        let owner = std::thread::Builder::new()
            .name("paired-qualification-original-root".into())
            .spawn(move || {
            let environment = [
                ("CARGO_HOME", actual.cargo_home.as_os_str()),
                ("CARGO", actual.program.path.as_os_str()),
                ("RUSTC", actual.compiler.path.as_os_str()),
                ("CARGO_CACHE_RUSTC_INFO", std::ffi::OsStr::new("0")),
            ];
            transport::capture_interactive(
                RootSpec {
                    program: &actual.program.path,
                    cwd: &actual.cwd,
                    entry: paired::PAIRED_STARTUP_ARGUMENT,
                    environment: &environment,
                    input: &bytes,
                    max_output: RAW_MAX,
                    max_stderr: ROOT_STDERR_MAX,
                    job: "trust-native-paired-qualification",
                },
                &store,
                transport::Interactive {
                    input,
                    deadline,
                    root_timeout_ms: budget.root_timeout_ms,
                    conversation,
                    protocol: InteractiveProtocol::PairedQualification,
                },
            )
        })?;
        Ok(Self {
            protocol,
            plan,
            request,
            writer: Some(writer),
            receiver,
            owner: Some(owner),
            pump,
            cancelled,
            deadline,
            started,
            physical_eof: false,
            failure: None,
            records: Vec::new(),
            raw: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            ledgers: BTreeMap::new(),
            inventories: BTreeMap::new(),
            samples: BTreeSet::new(),
            root: None,
            evidence_root: root,
            retired: false,
            root_succeeded: false,
            measured: false,
            cache,
            input_program,
            node_started: BTreeMap::new(),
            node_intervals: BTreeMap::new(),
            root_cost: None,
        })
    }
    fn check_inputs(&self, dependencies: &DependencyAttempt, git: &impl Git) -> Result<()> {
        let mut errors = Vec::new();
        if let Err(error) = dependencies.check_unchanged(git) {
            errors.push(error.0);
        }
        if let Err(error) = self.input_program.validate(self.deadline) {
            errors.push(format!("original paired input program changed: {error}"));
        }
        for artifact in self.artifacts.values() {
            if let Err(error) = artifact.check() {
                errors.push(error.0);
            }
        }
        if let Some(cache) = &self.cache {
            if let Err(error) = cache.check() {
                errors.push(error.0);
            }
        }
        if errors.is_empty() { Ok(()) } else { Err(Refusal(errors.join("; "))) }
    }
    fn drive(
        &mut self,
        dependencies: &DependencyAttempt,
        git: &impl Git,
        control: Option<&Self>,
    ) -> Result<()> {
        let startup = (self.started
            + Duration::from_nanos(trust_resource_controller::workload::budget::STARTUP_NS))
        .min(self.deadline);
        let mut pending = None;
        loop {
            let until = if self.protocol.ready.is_none() { startup } else { self.deadline };
            if Instant::now() >= until {
                return Err(Refusal("paired original conversation deadline expired".into()));
            }
            let input = pending.take().map(Ok).unwrap_or_else(|| {
                self.receiver.recv_timeout(
                    until.saturating_duration_since(Instant::now()).min(Duration::from_millis(50)),
                )
            });
            match input {
                Ok(io::Input::Frame(bytes)) => {
                    match self.protocol.frame(&bytes)? {
                        Some(Event::Ready(ready)) => self.records.push(json!({"stage":"original-ready","root_attempt":super::hex(&ready.binding.root_attempt),
                            "full60_digest":super::hex(&ready.binding.invocation_sha256),"reserved_domain":ready.reserved_domain,
                            "dispatch_ceiling":ready.dispatch_ceiling,"memory_bytes":ready.memory_bytes})),
                        Some(Event::Registered(row)) => {self.node_started.insert(row.node,Instant::now()); self.records.push(json!({"stage":"registered","node":format!("{:?}",row.node),
                            "original_unit":row.original_compile_unit.map(|unit|json!({"index":unit.index,"package":unit.package,"target":unit.target,
                                "unit_hash":unit.unit_hash,"source_hex":super::hex(&unit.source)}))}));},
                        Some(Event::Artifact(row)) => {
                            let input=shared::artifact_identity(&row.executable,&self.request.target_directory)?;
                            let retained=ArtifactInput::bind(input.clone(),&self.request.target_directory)?;
                            self.records.push(json!({"stage":"artifact","target":TARGETS[row.target as usize],"input":input}));
                            if self.artifacts.insert(row.target,retained).is_some() { return Err(Refusal("paired actual artifact repeated".into())); }
                        }
                        Some(Event::Chunk(chunk)) => {
                            if chunk.scope==service::OutputScope::NativeAction {
                                let raw=self.raw.entry(chunk.node).or_insert_with(||[Vec::new(),Vec::new()]);
                                let stream=&mut raw[usize::from(chunk.stream==service::Stream::Stderr)];
                                stream.try_reserve(chunk.bytes.len()).map_err(|e|Refusal(e.to_string()))?;
                                stream.extend_from_slice(&chunk.bytes);
                            }
                        }
                        Some(Event::DiagnosticEnd(end)) => self.records.push(json!({"stage":"logical-writer-end","node":format!("{:?}",end.node),
                            "scope":format!("{:?}",end.scope),"stream":format!("{:?}",end.stream),"bytes":end.length,
                            "writer_closed":end.writer_closed,"truncated":end.truncated})),
                        Some(Event::CompilerObservation(observation)) => self.records.push(compiler_observation_json(&observation)),
                        Some(Event::Finished(row)) => {
                            self.node_intervals.insert(row.node,self.node_started.get(&row.node)
                                .and_then(|started|u64::try_from(started.elapsed().as_nanos()).ok()));
                            // Rebinding also runs on known failures before a
                            // single continuation byte can be sent.
                            let observed=self.observe(&row,control);
                            let rebound=self.check_inputs(dependencies,git);
                            if let Err(error)=&rebound {self.records.push(json!({"stage":"original-input-refusal","reason":error.0}));}
                            observed?;rebound?;
                        }
                        Some(Event::Checkpoint(checkpoint)) => {
                            self.check_inputs(dependencies,git)?;
                            let until=(Instant::now()+Duration::from_nanos(trust_resource_controller::workload::budget::CHECKPOINT_NS)).min(self.deadline);
                            shared::write_frame(self.writer.as_mut().ok_or_else(||Refusal("original paired writer closed".into()))?,
                                &service::Control::Continue(checkpoint.clone()).encode(self.plan.consumer.repetitions)?,until)?;
                            self.protocol.continued(&checkpoint)?;
                            self.check_inputs(dependencies,git)?;
                        }
                        Some(Event::Final(final_observation)) => {
                            self.records.push(json!({"stage":"complete-original-graph-observation",
                                "finished":final_observation.finished,"blocked":final_observation.blocked,
                                "inputs_unchanged":final_observation.inputs_unchanged,
                                "snapshot":super::hex(&final_observation.snapshot),"members":final_observation.members,
                                "scope":"data consistency only; actual outer exit, EOF and original host retirement remain separately required"}));
                            self.check_inputs(dependencies,git)?;return Ok(());
                        }
                        None=>{}
                    }
                }
                Ok(io::Input::Eof) => {
                    self.physical_eof = true;
                    return Err(Refusal(
                        "paired physical stdout ended before complete graph".into(),
                    ));
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    if self.owner.as_ref().is_some_and(|owner| owner.is_finished()) {
                        match self.receiver.try_recv() {
                            Ok(input) => pending = Some(input),
                            Err(_) => {
                                return Err(Refusal(
                                    "paired original owner ended before complete graph".into(),
                                ));
                            }
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(Refusal("paired original read channel closed".into()));
                }
            }
        }
    }
    fn observe(&mut self, row: &service::Finished, control: Option<&Self>) -> Result<()> {
        let raw = self.raw.remove(&row.node).unwrap_or_else(|| [Vec::new(), Vec::new()]);
        let mut record = finished_json(row);
        record["frontend_observed_registration_to_terminal_ns"] =
            json!(self.node_intervals.get(&row.node).copied().flatten());
        record["raw_source"] = json!({"scope":"exact native bytes retained inside original root.stdout.frames.bin; diagnostic scopes excluded",
            "stdout_bytes":raw[0].len(),"stderr_bytes":raw[1].len(),
            "stdout_sha256":hash(&raw[0]),"stderr_sha256":hash(&raw[1])});
        let mut failure = None;
        if row.node == service::Node::Advisory && !native_passed(row) {
            failure = Some("original advisory verification did not exit successfully".into());
        }
        if row.node.is_verification() && Protocol::native_complete(row) {
            match Ledger::parse(&self.plan, row.node, &raw[1]) {
                Ok(ledger) => {
                    record["ledger"] = ledger_json(&ledger);
                    self.ledgers.insert(row.node, ledger);
                    if row.node == service::Node::Strict {
                        match self
                            .ledgers
                            .get(&service::Node::Advisory)
                            .ok_or_else(|| Refusal("original advisory ledger missing".into()))
                            .and_then(|advisory| {
                                advisory.agrees_with(&self.ledgers[&service::Node::Strict])
                            }) {
                            Ok(()) => record["independent_strict_agreement"] = json!(true),
                            Err(error) => {
                                record["independent_strict_agreement"] = json!(false);
                                failure = Some(error.0);
                            }
                        }
                    }
                }
                Err(error) => failure = Some(error.0),
            }
        } else if let service::Node::Inventory { target } = row.node {
            if native_passed(row) {
                let inventory = match Inventory::parse(&raw[0]) {
                    Ok(inventory) => inventory,
                    Err(error) => {
                        record["comparison_refusal"] = json!(error);
                        self.records.push(record);
                        return Err(Refusal(
                            "native inventory lacks its complete meaningful denominator".into(),
                        ));
                    }
                };
                if let Some(control) = control {
                    if control.inventories.get(&target) != Some(&inventory) {
                        record["comparison_refusal"] =
                            json!("control/candidate complete test denominator differs");
                        self.records.push(record);
                        return Err(Refusal("control/candidate complete test denominator differs; original candidate stops before samples".into()));
                    }
                }
                self.inventories.insert(target, inventory);
            } else {
                failure = Some("native inventory failed or is incomplete".into());
            }
        } else if let service::Node::Sample { target, repetition } = row.node {
            if self.inventories.len() != TARGETS.len() {
                self.records.push(record);
                return Err(Refusal("paired sample lacks complete original inventories".into()));
            }
            if !self.samples.insert((target, repetition)) {
                self.records.push(record);
                return Err(Refusal("paired native sample repeated".into()));
            }
            if native_passed(row) {
                if let Err(error) = self.inventories[&target].validate_sample(&raw[0], &raw[1]) {
                    failure = Some(error);
                }
            } else {
                failure = Some("native sample failed or is incomplete".into());
            }
        }
        if let Some(failure) = failure {
            record["semantic_failure"] = json!(failure);
        }
        self.records.push(record);
        Ok(())
    }
    fn stop(&mut self) {
        let binding = self.protocol.binding().ok().cloned();
        let sent = stop_input(
            &mut self.writer,
            binding.as_ref(),
            self.plan.consumer.repetitions,
            (Instant::now() + Duration::from_secs(1)).min(self.deadline),
        );
        if sent.is_err() {
            self.cancelled.store(true, Ordering::Release);
        }
        // The SAME original writer also closes on failure. This gives the
        // actual root its own EOF/cancel path even if no Ready binding could
        // be accepted; killing the outer CLI is not a substitute for it.
    }
    fn settle(&mut self) -> Result<()> {
        let Some(owner) = self.owner.take() else { return Ok(()) };
        self.writer.take();
        let until = (Instant::now()
            + Duration::from_nanos(trust_resource_controller::workload::budget::SETTLEMENT_NS))
        .min(self.deadline);
        while !owner.is_finished() {
            if Instant::now() >= until {
                self.cancelled.store(true, Ordering::Release);
            }
            match self.receiver.recv_timeout(Duration::from_millis(20)) {
                Ok(io::Input::Eof) => self.physical_eof = true,
                Ok(io::Input::Frame(bytes)) => {
                    if self.failure.is_none() {
                        if let Err(error) = self.protocol.frame(&bytes) {
                            self.failure = Some(error.0);
                        }
                    }
                }
                Err(_) => {}
            }
        }
        let captured = owner.join();
        self.writer.take();
        while let Ok(input) = self.receiver.try_recv() {
            match input {
                io::Input::Eof => self.physical_eof = true,
                io::Input::Frame(bytes) => {
                    if self.failure.is_none() {
                        if let Err(error) = self.protocol.frame(&bytes) {
                            self.failure = Some(error.0);
                        }
                    }
                }
            }
        }
        let raw = match io::lock(&self.pump, self.deadline) {
            Ok(mut pump) => pump.finish(),
            Err(error) => {
                json!({"failure":error.to_string(),"scope":"original raw prefix finalization unavailable; no complete bytes inferred"})
            }
        };
        self.root = Some(
            json!({"raw_capture":raw,"invocation_elapsed_through_outer_exit_and_drain_ns":u64::try_from(self.started.elapsed().as_nanos()).ok()}),
        );
        let captured = match captured {
            Ok(Ok(captured)) => captured,
            Ok(Err(error)) => {
                self.root.as_mut().expect("retained actual raw observation")["capture_error"] =
                    json!(error.0);
                return Err(error);
            }
            Err(_) => {
                let error = Refusal("original paired capture owner panicked".into());
                self.root.as_mut().expect("retained actual raw observation")["owner_error"] =
                    json!(error.0);
                return Err(error);
            }
        };
        let invocation_elapsed_ns = u64::try_from(self.started.elapsed().as_nanos()).ok();
        let mut report = captured.observation;
        report["raw_capture"] = raw;
        report["invocation_elapsed_through_outer_exit_and_drain_ns"] = json!(invocation_elapsed_ns);
        let checked = (|| -> Result<()> {
            if !captured.image_valid {
                return Err(Refusal("original paired custodian image changed".into()));
            }
            let exit = captured
                .exit_observation
                .ok_or_else(|| Refusal("original paired CLI owning wait unavailable".into()))?;
            let terminal = transport::validate_accounted_statuses(
                &captured.statuses.map_err(Refusal)?,
                &exit,
            )?;
            self.retired = true;
            self.root_succeeded = terminal.normal;
            report["checked_root_terminal"] = json!({"pid":terminal.pid,"birth":terminal.birth,"attempt":terminal.attempt,
                "outcome":terminal.outcome,"cause":format!("{:?}",terminal.cause),"leader_runtime_ns":terminal.runtime_ns,
                "accounting":terminal.accounting.map(accounting_json)});
            let ready = self
                .protocol
                .ready
                .as_ref()
                .ok_or_else(|| Refusal("paired original Ready absent".into()))?;
            if ready.original_root.pid != terminal.pid
                || ready.original_root.birth != terminal.birth
                || super::hex(&ready.binding.root_attempt) != terminal.attempt
            {
                return Err(Refusal(
                    "paired service differs from its actual original Root lifecycle".into(),
                ));
            }
            captured.output.map_err(Refusal)?;
            if report["raw_capture"].get("failure").is_some_and(|value| !value.is_null()) {
                return Err(Refusal("paired original raw prefix capture is incomplete".into()));
            }
            if !self.physical_eof
                || !captured
                    .conversation_output
                    .as_ref()
                    .is_some_and(|streams| streams.eof == [true; 2])
            {
                return Err(Refusal("paired original outer streams lack physical EOF".into()));
            }
            self.measured = self.protocol.measured()
                && terminal.accounting.is_some_and(|accounting| {
                    accounting.cpu_times.is_some() && accounting.peak_rss_bytes.is_some()
                });
            if self.protocol.final_observation.is_none() || self.protocol.failure.is_some() {
                return Err(Refusal("paired original complete final/census unavailable".into()));
            }
            self.root_cost = Some(costs::RootObservation {
                invocation_elapsed_ns,
                leader_runtime_ns: terminal.runtime_ns,
                accounting: terminal.accounting,
            });
            Ok(())
        })();
        self.root = Some(report);
        checked
    }
    fn report(&self) -> Value {
        json!({"request":self.request,"raw_evidence_directory":self.evidence_root,"records":self.records,"failure":self.failure,
            "protocol_failure":self.protocol.failure,"root":self.root,"retirement_confirmed":self.retired,"root_succeeded":self.root_succeeded,
            "performance_observations_complete":self.measured,"inventories":self.inventories,"samples":self.samples,
            "compiler_observations":self.protocol.compiler_observations().map(compiler_observation_json).collect::<Vec<_>>(),
            "complete_original_member_census":self.protocol.census.as_ref().map(|census|census.entries().iter().map(|entry|json!({
                "member_attempt":super::hex(&entry.member_attempt),"kind":format!("{:?}",entry.kind),
                "identity":entry.identity.map(|identity|json!({"pid":identity.pid,"birth":identity.birth})),
                "started":entry.started.map(|started|json!({"monotonic_ns":started.monotonic_ns,"unix_ns":started.unix_ns})),
                "terminal":format!("{:?}",entry.terminal),"retired":entry.retired,"drained":entry.drained,
                "accounting":accounting_json(entry.accounting)})).collect::<Vec<_>>())})
    }
}
/// Input-only compatibility check, deliberately before any delivery owner.
fn retain_input_program(
    root: &Path,
    program: &pair::FileIdentity,
    deadline: Instant,
) -> Result<trust_resource_provenance::program::HeldProgram> {
    let retained = trust_resource_provenance::program::HeldProgram::open(
        root,
        &program.path,
        &decode(program.sha256.as_bytes())?,
        deadline,
    )?;
    retained.require_paired_protocol_marker(&paired::PAIRED_PROTOCOL_MARKER, deadline)?;
    Ok(retained)
}
fn stop_input(
    writer: &mut Option<UnixStream>,
    binding: Option<&service::Binding>,
    repetitions: u32,
    deadline: Instant,
) -> Result<()> {
    let mut original =
        writer.take().ok_or_else(|| Refusal("original paired writer closed".into()))?;
    let binding = binding.ok_or_else(|| {
        Refusal(
            "original paired Ready binding unavailable; input closes without a forged Stop".into(),
        )
    })?;
    shared::write_frame(
        &mut original,
        &service::Control::Stop(binding.clone()).encode(repetitions)?,
        deadline,
    )
}
impl Drop for NativeRun {
    fn drop(&mut self) {
        if self.owner.is_some() {
            self.stop();
            let _ = self.settle();
        }
    }
}

fn native_passed(row: &service::Finished) -> bool {
    Protocol::native_complete(row)
        && matches!(&row.result,service::Result::Captured{capture,..}
        if capture.outcome==Some(trust_resource_controller::Outcome::Exit(0)))
}
fn hash(bytes: &[u8]) -> String {
    use sha2::{Digest as _, Sha256};
    format!("{:x}", Sha256::digest(bytes))
}
fn accounting_json(value: trust_resource_controller::accounting::Observation) -> Value {
    json!({"scope":"child-and-waited-descendants-v1","cpu_times":value.cpu_times.map(|cpu|json!({"user_ns":cpu.user_ns,"system_ns":cpu.system_ns})),
        "peak_rss_bytes":value.peak_rss_bytes})
}
fn compiler_observation_json(observation: &service::compiler_observation::Observation) -> Value {
    json!({"stage":"checked-compiler-report","node":format!("{:?}",observation.node),
        "run_id":observation.run_id,"report_bytes":observation.report_bytes,"report_sha256":super::hex(&observation.report_sha256),
        "unavailable":observation.unavailable,"counts":observation.counts.as_ref().map(|counts|json!({
            "graph_outcome":format!("{:?}",counts.graph_outcome),"registered_units":counts.registered,
            "scheduled":counts.scheduled,"scheduled_fresh":counts.scheduled_fresh,"completed":counts.completed,
            "succeeded":counts.succeeded,"failed":counts.failed,"tolerated_failure":counts.tolerated_failure,
            "cancelled":counts.cancelled,"not_executed":counts.not_executed,"rusage_requested":counts.rusage_requested,
            "successful_primary_processes":counts.successful_primary_processes,"observed_successful_units":counts.observed_successful_units,
            "unmeasured_starts":counts.unmeasured_starts,"completed_without_start":counts.completed_without_start})),
        "scope":"compiler-unit-primary-processes-v1 from original closed strict report; freshness is not a launch/cache-hit count; verifier/test actions and overlapping root/member CPU scopes stay separate"})
}
fn finished_json(row: &service::Finished) -> Value {
    let result = match &row.result {
        service::Result::Compiled { succeeded, local_workers_joined, failure } => {
            json!({"kind":"compile-graph","succeeded":succeeded,
            "actual_local_workers_joined":local_workers_joined,"failure":failure})
        }
        service::Result::Blocked { reason } => json!({"kind":"blocked","reason":reason}),
        service::Result::Captured { capture, elapsed_ns, input_failure } => {
            json!({"kind":"native-action","started":capture.started,
            "outcome":format!("{:?}",capture.outcome),"cause":format!("{:?}",capture.cause),"leader_runtime_ns":capture.runtime_ns,
            "retirement_confirmed":capture.retirement_confirmed,"accounting":capture.accounting.map(accounting_json),
            "member_attempt":capture.member_attempt.map(|member|super::hex(&member)),"failure":capture.failure,
            "input_failure":input_failure,"action_elapsed_ns":elapsed_ns})
        }
    };
    json!({"stage":"node-outcome","node":format!("{:?}",row.node),"result":result,"lengths":row.lengths,
        "ends":row.ends.map(|end|format!("{end:?}")),"truncated":row.truncated})
}
fn ledger_json(ledger: &Ledger) -> Value {
    json!({"claim_scope":ledger.claim_scope,"source_commit":ledger.source_commit,"crate_tree":ledger.crate_tree,
        "policy":ledger.policy,"session":ledger.verification_session,"denominator_complete":ledger.denominator_complete,
        "classes":ledger.classes,"truncated_functions":ledger.truncated_functions,
        "entries":ledger.entries.iter().map(|(key,row)|(key,json!({"class":row.class,"conservative_outcome":row.conservative_outcome,
            "location":row.original.location,"claim_digest_sha256":row.original.claim_digest_sha256,"assumes":row.original.assumes,
            "grade":row.original.grade,"vcgen_truncated_function":row.vcgen_truncated_function,"absent_callee":row.absent_callee}))).collect::<BTreeMap<_,_>>(),
        "raw_proof_payloads":"retained verbatim in original native-action chunks in root.stdout.frames.bin; no serialized proof grant"})
}

pub(super) fn run(
    dependencies: DependencyAttempt,
    git: &impl Git,
    options: Options,
    store: Option<PathBuf>,
    requested_cache: Option<PathBuf>,
) -> Value {
    let mut errors = Vec::new();
    let mut runs = Vec::new();
    let mut attempted = Vec::new();
    let mut evidence = shared::NativeWorkloadProducer::new(store.clone());
    let mut cache: Option<Arc<cache::Cache>> = None;
    let mut evidence_directory = options.output.clone();
    let plan = (|| -> Result<(AySubject, Vec<Request>)> {
        if !dependencies.consistent() {
            return Err(Refusal(
                "original compiler probes/dependencies refused; paired producer not called".into(),
            ));
        }
        dependencies.check_unchanged(git)?;
        let snapshot = dependencies.snapshot();
        let parent = options
            .output
            .parent()
            .ok_or_else(|| Refusal("paired output has no parent".into()))?
            .canonicalize()?;
        let output = parent.join(
            options
                .output
                .file_name()
                .ok_or_else(|| Refusal("paired output has no name".into()))?,
        );
        let home = dependencies.requested_inputs().cargo_home.canonicalize()?;
        evidence_directory = output.clone();
        if requested_cache
            .as_ref()
            .is_some_and(|cache| output.starts_with(cache) || cache.starts_with(&output))
        {
            return Err(Refusal(
                "paired warm cache must be disjoint from its new evidence directory".into(),
            ));
        }
        for input in snapshot
            .sources
            .values()
            .map(|source| source.path.as_path())
            .chain([
                snapshot.control.path.as_path(),
                snapshot.candidate.path.as_path(),
                home.as_path(),
            ])
            .chain(dependencies.dependency_input_roots())
        {
            if std::iter::once(output.as_path())
                .chain(requested_cache.as_deref())
                .any(|output| output.starts_with(input) || input.starts_with(output))
            {
                return Err(Refusal("paired output aliases an original frozen input".into()));
            }
        }
        let timeout_ns = u64::try_from(options.timeout.as_nanos())
            .map_err(|_| Refusal("paired phase budget is unrepresentable".into()))?;
        paired::budget::Budget::new(options.repetitions, timeout_ns)?;
        let ay = &snapshot.sources["ay"];
        let tree = git.probe(&ay.path, &["rev-parse", "HEAD:crates/ay-proof-common"])?;
        let subject = AySubject {
            root: ay.path.as_os_str().as_encoded_bytes().to_vec(),
            workspace_manifest: subject_input(&ay.path.join("Cargo.toml"))?,
            crate_manifest: subject_input(&ay.path.join("crates/ay-proof-common/Cargo.toml"))?,
            lockfile: subject_input(&ay.path.join("Cargo.lock"))?,
            cargo_config: subject_input(&ay.path.join(".cargo/config.toml"))?,
            toolchain_config: subject_input(&ay.path.join("rust-toolchain.toml"))?,
            source_commit: decode(ay.commit.as_bytes())?,
            crate_tree: decode(tree.strip_suffix(b"\n").unwrap_or(&tree))?,
        };
        subject.validate()?;
        if let Some(path) = &requested_cache {
            cache = Some(Arc::new(cache::Cache::open(path)?));
        }
        let mut requests = Vec::new();
        for (side, sdk, name) in [
            (Side::Control, &snapshot.control, "control-target"),
            (Side::Candidate, &snapshot.candidate, "candidate-target"),
        ] {
            requests.push(Request {
                side,
                sdk_root: sdk.path.clone(),
                program: sdk.executables["targo"].clone(),
                compiler: sdk.executables["trustc"].clone(),
                cwd: snapshot.sources["trust_vc"].path.clone(),
                target_directory: cache
                    .as_ref()
                    .map_or_else(|| output.join(name), |cache| cache.target(side).to_path_buf()),
                cargo_home: home.clone(),
                proof_fixtures: snapshot.proof_fixtures.clone(),
                trust_spec_source: snapshot.trust_spec_source.clone(),
                repetitions: options.repetitions,
                timeout_ns,
            });
        }
        dependencies.check_unchanged(git)?;
        Ok((subject, requests))
    })();
    match plan {
        Err(error) => errors.push(error.0),
        Ok((subject, requests)) => {
            for request in requests {
                attempted.push(json!({"side":request.side,"request":request,"attempted":true}));
                let prepared = (|| -> Result<NativeRun> {
                    dependencies.check_unchanged(git)?;
                    let plan = PairedInvocation {
                        consumer: shared::invocation(&request, &store)?,
                        ay: subject.clone(),
                    };
                    plan.validate()?;
                    if let Some(cache) = &cache {
                        cache.check()?;
                    }
                    let root = evidence.evidence_root_at(request.side, &evidence_directory)?;
                    NativeRun::launch(request.clone(), plan, store.clone(), root, cache.clone())
                })();
                let mut actual = match prepared {
                    Ok(actual) => actual,
                    Err(error) => {
                        errors.push(error.0);
                        break;
                    }
                };
                let driven = actual.drive(&dependencies, git, runs.first());
                if let Err(error) = driven {
                    actual.records.push(json!({"stage":"original-drive-error","reason":error.0}));
                    actual.failure = Some(error.0);
                    actual.stop();
                }
                if let Err(error) = actual.settle() {
                    actual
                        .records
                        .push(json!({"stage":"original-settlement-error","reason":error.0}));
                    actual.failure.get_or_insert(error.0);
                }
                if let Err(error) = actual.check_inputs(&dependencies, git) {
                    actual
                        .records
                        .push(json!({"stage":"original-final-input-error","reason":error.0}));
                    actual.failure.get_or_insert(error.0);
                }
                let failed = actual.failure.is_some();
                runs.push(actual);
                // Never ask for the next original all-domain admission while the
                // first root's positive retirement or input state is unavailable.
                if failed {
                    break;
                }
            }
        }
    }
    if let Err(error) = dependencies.check_unchanged(git) {
        errors.push(error.0);
    }
    for run in &runs {
        if let Err(error) = run.check_inputs(&dependencies, git) {
            errors.push(error.0);
        }
    }
    if let Some(cache) = &cache {
        if let Err(error) = cache.check() {
            errors.push(error.0);
        }
    }
    let comparison = compare(&runs, errors.is_empty());
    let complete = errors.is_empty()
        && runs.len() == 2
        && runs.iter().all(|run| run.failure.is_none() && run.retired)
        && comparison["complete"].as_bool() == Some(true);
    json!({"schema":"trust.paired-native-qualification.v1","stage":"native-AY-and-consumer-graphs",
        "status":if complete{"paired-observations-checked"}else{"refused"},
        "claim_scope":"actual native observed graph/policy/test comparison; no source/build/proof, admission or publication grant from this record",
        "dependencies":dependencies.report(),"requested_options":options,"requested_cache":requested_cache,
        "retained_cache_observation":cache.as_ref().map(|cache|cache.report()),"attempted":attempted,"errors":errors,
        "sides":runs.iter().map(NativeRun::report).collect::<Vec<_>>(),"comparison":comparison,
        "pending_stages":["live-paired-host-and-SDK-qualification","remaining-lock-and-writer-policy","all-active-callers-and-helper-retirement","whole-paired-goal-qualification"]})
}
fn subject_input(path: &Path) -> Result<trust_resource_controller::workload::InputFile> {
    let identity = pair::file_identity(path)?;
    if identity.link_text.is_some() || identity.path != identity.resolved_path {
        return Err(Refusal("paired AY subject input is aliased".into()));
    }
    Ok(trust_resource_controller::workload::InputFile {
        path: path.as_os_str().as_encoded_bytes().to_vec(),
        sha256: decode(identity.sha256.as_bytes())?,
    })
}
fn decode<const N: usize>(bytes: &[u8]) -> Result<[u8; N]> {
    if bytes.len() != N * 2
        || !bytes.iter().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(Refusal(
            "paired source/digest observation is not canonical lowercase hex".into(),
        ));
    }
    let mut out = [0; N];
    for (at, value) in out.iter_mut().enumerate() {
        let digit = |byte: u8| if byte <= b'9' { byte - b'0' } else { byte - b'a' + 10 };
        *value = (digit(bytes[2 * at]) << 4) | digit(bytes[2 * at + 1]);
    }
    Ok(out)
}
fn compare(runs: &[NativeRun], final_inputs_unchanged: bool) -> Value {
    if runs.len() != 2 {
        return json!({"complete":false,"reason":"both original roots are required"});
    }
    let (before, after) = (&runs[0], &runs[1]);
    let ledgers = (|| -> Result<(&Ledger, &Ledger)> {
        let mut advisory = Vec::new();
        for run in runs {
            let a = run
                .ledgers
                .get(&service::Node::Advisory)
                .ok_or_else(|| Refusal("native advisory ledger unavailable".into()))?;
            let s = run
                .ledgers
                .get(&service::Node::Strict)
                .ok_or_else(|| Refusal("native strict ledger unavailable".into()))?;
            a.agrees_with(s)?;
            advisory.push(a);
        }
        if advisory[0].source_commit != advisory[1].source_commit
            || advisory[0].crate_tree != advisory[1].crate_tree
        {
            return Err(Refusal("paired AY sources changed across toolchains".into()));
        }
        Ok((advisory[0], advisory[1]))
    })();
    let (base, current) = match ledgers {
        Ok(ledgers) => ledgers,
        Err(error) => return json!({"complete":false,"reason":error.0}),
    };
    let inventories = before.inventories.len() == 2 && before.inventories == after.inventories;
    let samples =
        runs.iter().all(|run| run.samples.len() == 2 * run.plan.consumer.repetitions as usize);
    let semantic = runs.iter().all(|run| {
        run.root_succeeded
            && !run.records.iter().any(|record| {
                record.get("semantic_failure").is_some()
                    || record.pointer("/result/kind").and_then(Value::as_str) == Some("blocked")
                    || record.pointer("/result/succeeded").and_then(Value::as_bool) == Some(false)
            })
    });
    let ratchet = ratchet(base, current);
    let ratchet_passed = ratchet["ratchet_regressions"].as_array().is_some_and(Vec::is_empty);
    let eligible = final_inputs_unchanged
        && inventories
        && samples
        && semantic
        && ratchet_passed
        && runs.iter().all(|run| run.failure.is_none() && run.retired);
    let costs = costs::compare(
        before.plan.consumer.repetitions,
        costs::Side {
            protocol: &before.protocol,
            intervals: &before.node_intervals,
            root: before.root_cost.as_ref(),
        },
        costs::Side {
            protocol: &after.protocol,
            intervals: &after.node_intervals,
            root: after.root_cost.as_ref(),
        },
        eligible,
    );
    json!({"complete":eligible&&runs.iter().all(|run|run.measured)&&costs["complete"].as_bool()==Some(true),
        "independent_policy_agreement":true,"complete_equal_test_denominators":inventories,"complete_repeated_samples":samples,
        "actual_measurements_complete":runs.iter().all(|run|run.measured),"semantic_observations_succeeded":semantic,"ratchet":ratchet,
        "compiler_primary_processes":runs.iter().map(|run|run.protocol.compiler_observations().map(compiler_observation_json).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "costs":costs,"final_inputs_unchanged":final_inputs_unchanged,
        "resource_scope":"original canonical-domain reservation and queue/foreign phases; no machine-wide exclusivity inferred"})
}
/// Pure observed census accounting. This receives no native owner, cannot
/// execute a candidate, and never constructs a proof from a reported grade.
fn ratchet(base: &Ledger, current: &Ledger) -> Value {
    let mut gained = Vec::new();
    let mut lost = Vec::new();
    let mut removed = Vec::new();
    let mut added = Vec::new();
    let credit = |row: &super::ledger::Entry| {
        row.class == super::ledger::Class::ProvedSolver
            && row.conservative_outcome == crate::types::VerificationOutcome::Proved
    };
    for (identity, row) in &current.entries {
        match base.entries.get(identity) {
            None => added.push(identity.clone()),
            Some(previous) if credit(row) && !credit(previous) => gained.push(identity.clone()),
            _ => {}
        }
    }
    for (identity, row) in &base.entries {
        match current.entries.get(identity) {
            None => {
                if credit(row) {
                    lost.push(identity.clone());
                }
                removed.push(json!({"identity":identity,"previous_class":row.class,"absent_callee_hint":row.absent_callee,
            "scope":"removed denominator; never counted as a discharged proof"}));
            }
            Some(now) if credit(row) && !credit(now) => lost.push(identity.clone()),
            _ => {}
        }
    }
    let mut regressions = Vec::new();
    let proved = |ledger: &Ledger| ledger.entries.values().filter(|row| credit(row)).count();
    // These are reported current-compiler grades after ordinary conservative
    // transport normalization. The actual kernel/claim checks remain in the
    // original compiler; this creates no proof capability from a saved row.
    let certified = |ledger: &Ledger| {
        ledger
            .conservative_results
            .iter()
            .filter(|row| {
                row.outcome == crate::types::VerificationOutcome::Proved
                    && row.kind != "no_obligations"
                    && crate::types::structured_transport_evidence(row)
                        .and_then(|envelope| envelope.proof_evidence)
                        .and_then(|proof| proof.evidence)
                        .is_some_and(|evidence| evidence.is_certified())
            })
            .count()
    };
    if proved(current) < proved(base) {
        regressions.push("solver-discharged identity floor fell");
    }
    if certified(current) < certified(base) {
        regressions.push("reported kernel-certified row floor fell");
    }
    if !lost.is_empty() {
        regressions.push("existing solver-discharged identities lost proof");
    }
    if current.terminal.total_timed_out > base.terminal.total_timed_out {
        regressions.push("timeout count rose");
    }
    let newly_failed = current
        .entries
        .iter()
        .filter(|(identity, row)| {
            !base.entries.contains_key(*identity) && row.class == super::ledger::Class::Failed
        })
        .count();
    let newly_unknown = current
        .entries
        .iter()
        .filter(|(identity, row)| {
            !base.entries.contains_key(*identity)
                && matches!(
                    row.class,
                    super::ledger::Class::Unknown
                        | super::ledger::Class::Skipped
                        | super::ledger::Class::Timeout
                        | super::ledger::Class::Unsupported
                        | super::ledger::Class::Canceled
                        | super::ledger::Class::Rejected
                )
        })
        .count();
    if current.terminal.total_failed.saturating_sub(base.terminal.total_failed) > newly_failed {
        regressions.push("failed growth is not explained by newly emitted obligations");
    }
    if current.terminal.total_unknown.saturating_sub(base.terminal.total_unknown) > newly_unknown {
        regressions.push("unknown growth is not explained by newly emitted obligations");
    }
    json!({"solver_discharged_identity_gains":gained,"solver_discharged_identity_losses":lost,
        "obligations_removed":removed,"obligations_newly_asked":added,
        "ratchet_regressions":regressions,"floors":{"conservative_solver_discharged":[proved(base),proved(current)],
            "producer_reported_kernel_certified_full_rows":[certified(base),certified(current)]},
        "scope":"identity movement; denominator shrinkage and structural verdicts are not solver improvements; current compiler proof authority remains separate"})
}

#[cfg(test)]
mod tests;
