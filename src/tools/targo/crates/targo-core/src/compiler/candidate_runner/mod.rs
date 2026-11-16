//! Original parent compiler relay for a separately hosted produced Targo.
//!
//! The socket carries proposals and observations only. Every execution uses
//! the actual parent's native factory, second original bank unit, input owners
//! and capture. This module cannot create a Root, SDK, registered output or a
//! successful coordinator operation from a report.

use super::build_runner::OriginalOutputLeases;
use super::candidate_dependencies::{
    GraphClosure, Ledger, PendingUnit, PublishedProgram, PublishedUnit,
};
use crate::resource_v3::workload::bank::{CoordinatorLocalOperation, PrimaryLoan};
use crate::resource_v3::{CoordinatorCompilerCapture, CoordinatorCompilerFactory, Startup};
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use cargo_util::{
    CaptureStreamEnd, CapturedProcess, EnvironmentInputs, ProcessBuilder, StreamingOutputLimits,
    StreamingProcessScope,
};
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};
use trust_resource_controller::client::CoordinatorBrokerServer;
use trust_resource_controller::client::workload::CompletedLocalOperation;
use trust_resource_controller::descriptors::AdmittedPackageSource;
use trust_resource_controller::workload::host::coordinator::{
    BrokerCaptureData, BrokerLimits, BrokerRequest, Plan, StreamEnd,
};
use trust_resource_controller::workload::host::publication::{Intent, Kind};
use trust_resource_controller::{CommandSpec, accounting::Observation};

const MAX_OPERATIONS: usize = 4096;
const MAX_RETAINED_BYTES: usize = 256 * 1024 * 1024;
const REPLY_BUDGET: Duration = Duration::from_secs(1);
// The private protocol bounds each complete request/preparation to 1MiB and
// each argument/environment population to 4096. Reserve all native request,
// final-command and status snapshots before delivery; charge their actual
// capacities after retirement so tiny successful units can still be reused.
const NATIVE_CAPTURE_RESERVE: usize = 8 * trust_resource_controller::MAX_PAYLOAD;

pub(crate) mod lifecycle;
mod preparation;

/// Actual original owners, shared by the parent and each native worker.
/// The factory's owner must retain this capsule, never the relay/capture vector
/// itself: captures retain their factory owner and must not form an Arc cycle.
pub(crate) struct Inputs {
    // The SAME selected output root is a distinct original from the master
    // workload output. Neither an umbrella path nor a fabricated invocation
    // can replace this description when retaining dependency artifacts.
    selected_output: Arc<trust_resource_provenance::program::produced::HeldOutputRoot>,
    original: Arc<crate::ops::cargo_test::workload::Inputs>,
    startup: Arc<Startup>,
    plan: Plan,
    sources: Vec<Arc<AdmittedPackageSource>>,
    outputs: Arc<OriginalOutputLeases>,
    commands: OnceLock<super::candidate_commands::ExpectedCommands>,
    deadline: Instant,
}
impl Inputs {
    pub(crate) fn new(
        startup: Arc<Startup>,
        original: Arc<crate::ops::cargo_test::workload::Inputs>,
        selected_output: Arc<trust_resource_provenance::program::produced::HeldOutputRoot>,
        plan: Plan,
        sources: Vec<Arc<AdmittedPackageSource>>,
        outputs: Arc<OriginalOutputLeases>,
        deadline: Instant,
    ) -> CargoResult<Arc<Self>> {
        plan.validate()?;
        let inputs = Arc::new(Self {
            selected_output,
            original,
            startup,
            plan,
            sources,
            outputs,
            commands: OnceLock::new(),
            deadline,
        });
        inputs.validate()?;
        Ok(inputs)
    }

    fn validate(&self) -> CargoResult<()> {
        self.original.validate()?;
        self.selected_output.validate(self.deadline)?;
        ensure!(
            self.selected_output.path() == path(&self.plan.output_root)
                && self
                    .startup
                    .workload_evidence
                    .as_ref()
                    .is_some_and(|actual| Arc::ptr_eq(actual, &self.original.evidence)),
            "parent relay lost SAME selected output root or original workload inputs"
        );
        let process = self
            .startup
            .workload_process
            .as_ref()
            .context("parent relay lost its original compiler/SDK owners")?;
        ensure!(
            self.startup.original_root
                && self.startup.candidate.is_none()
                && self.startup.workload_bank.is_some()
                && Instant::now() < self.deadline.min(process.deadline)
                && !process.poisoned.load(std::sync::atomic::Ordering::Acquire)
                && !process.cancelled.load(std::sync::atomic::Ordering::Acquire),
            "parent relay has no live original native workload"
        );
        ensure!(
            process.compiler.program().as_os_str().as_bytes() == self.plan.compiler.path
                && process.compiler.root().as_os_str().as_bytes() == self.plan.sdk_root
                && process.compiler.observation().executable.sha256
                    == hex::encode(self.plan.compiler.sha256)
                && self.sources.len() == self.plan.sources.len(),
            "parent relay selected different original compiler/source inputs"
        );
        process.sysroot.validate(self.deadline)?;
        for (actual, selected) in self.sources.iter().zip(&self.plan.sources) {
            ensure!(
                actual.path().as_os_str().as_bytes() == selected.root
                    && actual.content_digest() == &selected.sha256,
                "parent relay source population differs from the original plan"
            );
            actual.validate(self.deadline)?;
        }
        self.outputs.validate(&path(&self.plan.output_root))
    }

    fn command(&self, proposed: &CommandSpec) -> CargoResult<(ProcessBuilder, CommandSpec)> {
        self.validate()?;
        ensure!(
            proposed.program == self.plan.compiler.path
                && proposed.arg0.is_none()
                && self
                    .sources
                    .iter()
                    .any(|source| source.path().as_os_str().as_bytes() == proposed.cwd),
            "parent relay refuses another compiler, arg0 or package working directory"
        );
        // Validate bounded command syntax before copying any proposal fields.
        // The native Host still owns filesystem confinement and final typed
        // CPU/GNU/SDK construction; these bytes confer none of those rights.
        BrokerRequest::encode_execute(
            1,
            proposed,
            BrokerLimits {
                line_bytes: 1,
                stream_bytes: 1,
                timeout_ns: 1,
                capture_rusage: false,
            },
        )?;
        let environment = EnvironmentInputs::from_variables(
            proposed
                .environment
                .iter()
                .map(|(name, value)| (os(name), os(value))),
        )?;
        let mut command = ProcessBuilder::new(os(&proposed.program));
        command
            .cwd(path(&proposed.cwd))
            .environment_snapshot(environment);
        for argument in &proposed.args {
            command.arg(os(argument));
        }
        let expected = self
            .commands
            .get()
            .context("compiler proposal arrived before independent command selection")?;
        // Materialize only the SAME already retained original GNU transport.
        // Its observable values participate in complete command equality.
        command.inherit_jobserver(expected.jobserver());
        let mut remaining = MAX_RETAINED_BYTES;
        let actual = super::candidate_commands::capture_command(&command, &mut remaining)?;
        if !crate::resource_v3::is_coordinator_query(&proposed.args) {
            expected.require(&actual)?;
        }
        Ok((command, actual))
    }

    pub(crate) fn install_commands(
        &self,
        member: &mut trust_resource_controller::client::ContainedProducedMember,
        commands: super::candidate_commands::ExpectedCommands,
    ) -> CargoResult<()> {
        self.validate()?;
        commands.require_member(member, self.deadline)?;
        self.commands.set(commands).map_err(|_| {
            anyhow::anyhow!("independent compiler command selection was already installed")
        })
    }
    fn require_commands(
        &self,
        member: &mut trust_resource_controller::client::ContainedProducedMember,
    ) -> CargoResult<()> {
        self.commands
            .get()
            .context("candidate GO lacks independently prepared compiler commands")?
            .require_member(member, self.deadline)
    }
}

fn os(bytes: &[u8]) -> OsString {
    OsString::from_vec(bytes.to_vec())
}
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(os(bytes))
}

pub(super) fn command_demand(command: &CommandSpec) -> CargoResult<usize> {
    // Charge every retained variable-sized field and collection allocation,
    // plus its execution record. Tiny compiler output cannot hide thousands
    // of large command environments. Wire decoding already bounds each field.
    let mut bytes = std::mem::size_of::<Execution>();
    let mut add = |amount: usize| -> CargoResult<()> {
        bytes = bytes
            .checked_add(amount)
            .context("retained compiler command size overflow")?;
        ensure!(
            bytes <= MAX_RETAINED_BYTES,
            "retained compiler command exceeds byte budget"
        );
        Ok(())
    };
    add(command.program.capacity())?;
    add(command.cwd.capacity())?;
    if let Some(arg0) = &command.arg0 {
        add(arg0.capacity())?;
    }
    add(command
        .args
        .capacity()
        .checked_mul(std::mem::size_of::<Vec<u8>>())
        .context("retained compiler argument population overflow")?)?;
    for arg in &command.args {
        add(arg.capacity())?;
    }
    add(command
        .environment
        .capacity()
        .checked_mul(std::mem::size_of::<(Vec<u8>, Vec<u8>)>())
        .context("retained compiler environment population overflow")?)?;
    for (key, value) in &command.environment {
        add(key.capacity())?;
        add(value.capacity())?;
    }
    Ok(bytes)
}

struct Active {
    sequence: u64,
    proposal: Option<CommandSpec>,
    command: Option<CommandSpec>,
    pending: Option<PendingUnit>,
    scope: StreamingProcessScope,
    worker: Option<JoinHandle<CargoResult<(CoordinatorCompilerCapture, Duration)>>>,
}
impl Drop for Active {
    fn drop(&mut self) {
        if let Some(worker) = self.worker.take() {
            self.scope.cancel();
            // Join this exact owned worker. Its native cancellation/retirement
            // path owns all signalling; no PID search or replacement waiter.
            if worker.join().is_err() {
                crate::resource_v3::workload::abort_unknown();
            }
        }
    }
}

/// Retain the exact command and opaque actual child/capture through comparison.
/// There is no deserializer or conversion from a successful broker message.
pub(crate) struct Execution {
    // Retain the exact proposal DATA beside its actual command and capture.
    pub(crate) _proposal: CommandSpec,
    pub(crate) command: CommandSpec,
    pub(crate) native: Arc<CoordinatorCompilerCapture>,
    pub(crate) elapsed: Duration,
}
pub(crate) struct PreparationFailure {
    // Keep the complete bounded failed record even without a reporting consumer.
    pub(crate) _proposal: CommandSpec,
    pub(crate) _command: CommandSpec,
    pub(crate) _reason: String,
}

pub(crate) struct CompilerRelay {
    active: Option<Active>,
    executions: Vec<Execution>,
    preparation_failures: Vec<PreparationFailure>,
    dependencies: Option<Ledger>,
    coordinator: Arc<PrimaryLoan>,
    local_operations: Vec<CompletedLocalOperation>,
    publications: Vec<PublishedUnit>,
    graph: Option<GraphClosure>,
    server: CoordinatorBrokerServer,
    factory: Arc<CoordinatorCompilerFactory>,
    inputs: Arc<Inputs>,
    preparation_output: preparation::Output,
    retained_bytes: usize,
    failed: bool,
}
impl CompilerRelay {
    fn begin_local(
        &self,
        kind: Kind,
        producer: Option<[u8; 16]>,
        intents: Vec<Intent>,
    ) -> CargoResult<CoordinatorLocalOperation> {
        ensure!(
            self.active.is_none()
                && self.local_operations.len() + self.publications.len() < MAX_OPERATIONS,
            "local IO overlaps a compiler or exceeds the retained operation bound"
        );
        ensure!(
            self.retained_bytes
                .checked_add(NATIVE_CAPTURE_RESERVE)
                .is_some_and(|bytes| bytes <= MAX_RETAINED_BYTES),
            "local IO exceeds the remaining native retention reservation"
        );
        let control = self
            .inputs
            .startup
            .workload_control
            .as_ref()
            .context("local IO lost its original workload broker")?;
        let budget = self
            .inputs
            .startup
            .descriptor_budget
            .as_ref()
            .context("local IO lost its original descriptor budget")?;
        loop {
            self.inputs.validate()?;
            let operation = control
                .lock()
                .map_err(|_| anyhow::anyhow!("local IO broker poisoned"))?
                .as_mut()
                .context("local IO broker was already consumed")?
                .begin_local(
                    &self.coordinator,
                    self.inputs.selected_output.clone(),
                    budget.clone(),
                    kind,
                    producer,
                    intents.clone(),
                )?;
            if let Some(operation) = operation {
                return Ok(operation);
            }
            // Only an authenticated positive no-admission may retry. The
            // dedicated broker still services genuine original-bank returns.
            // Inputs::validate preserves the SAME absolute cancellation/deadline.
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    fn finish_local<T>(
        &mut self,
        mut operation: CoordinatorLocalOperation,
        result: CargoResult<T>,
    ) -> CargoResult<(T, CompletedLocalOperation)> {
        if let Err(error) = &result {
            operation.fail(format!("{error:#}"));
        }
        // Every fixed IO primitive has closed its writer/staging descriptions
        // before this call. Even failed IO must positively return the SAME
        // distinct original; a successful source callback grants nothing.
        let completed = self
            .inputs
            .startup
            .workload_control
            .as_ref()
            .context("local return lost its original workload broker")?
            .lock()
            .map_err(|_| anyhow::anyhow!("local return broker poisoned"))?
            .as_mut()
            .context("local return broker was already consumed")?
            .complete_local(operation)?;
        let success = completed.require_success();
        match (result, success) {
            (Ok(value), Ok(())) => Ok((value, completed)),
            (Err(error), _) => {
                self.retain_local(completed)?;
                Err(error)
            }
            (Ok(_), Err(error)) => {
                self.retain_local(completed)?;
                Err(error.into())
            }
        }
    }

    fn retain_local(&mut self, completed: CompletedLocalOperation) -> CargoResult<()> {
        let footprint = completed.retained_bytes();
        let capacity = self.local_operations.capacity();
        // Keep the actual failed/completed native owner before quota errors.
        self.local_operations.push(completed);
        let bytes = footprint
            .and_then(|bytes| bytes.checked_sub(std::mem::size_of::<CompletedLocalOperation>()))
            .and_then(|bytes| {
                self.local_operations
                    .capacity()
                    .checked_sub(capacity)
                    .and_then(|slots| {
                        slots.checked_mul(std::mem::size_of::<CompletedLocalOperation>())
                    })
                    .and_then(|population| bytes.checked_add(population))
            })
            .context("local return retained footprint overflow")?;
        self.retained_bytes = self
            .retained_bytes
            .checked_add(bytes)
            .filter(|bytes| *bytes <= MAX_RETAINED_BYTES)
            .context("local return exceeds retained byte budget")?;
        Ok(())
    }

    pub(crate) fn install_commands(
        &mut self,
        member: &mut trust_resource_controller::client::ContainedProducedMember,
        commands: super::candidate_commands::ExpectedCommands,
    ) -> CargoResult<()> {
        self.inputs.install_commands(member, commands)?;
        let expected = self
            .inputs
            .commands
            .get()
            .context("parent lost its independently selected commands")?;
        let intents = Ledger::preparation_intents(expected)?;
        let mut operation = self.begin_local(Kind::PrepareOutputs, None, intents)?;
        let prepared = (|| -> CargoResult<Option<Ledger>> {
            if let Some(ledger) = &mut self.dependencies {
                ledger.require_inputs(
                    &self.inputs.startup,
                    &self.inputs.original,
                    &self.inputs.selected_output,
                    &self.inputs.outputs,
                )?;
                ledger.prepare_graph(expected, &mut operation)?;
                Ok(None)
            } else {
                Ok(Some(Ledger::new(
                    self.inputs.startup.clone(),
                    self.inputs.original.clone(),
                    self.inputs.selected_output.clone(),
                    self.inputs.outputs.clone(),
                    expected,
                    &path(&self.inputs.plan.output_root),
                    self.inputs.deadline,
                    &mut operation,
                )?))
            }
        })();
        let (prepared, completed) = self.finish_local(operation, prepared)?;
        if let Some(ledger) = prepared {
            self.dependencies = Some(ledger);
        }
        self.retain_local(completed)?;
        Ok(())
    }
    pub(crate) fn new(
        server: CoordinatorBrokerServer,
        factory: Arc<CoordinatorCompilerFactory>,
        inputs: Arc<Inputs>,
        dependencies: Option<Ledger>,
        coordinator: Arc<PrimaryLoan>,
    ) -> CargoResult<Self> {
        inputs.validate()?;
        factory.require_coordinator(
            &inputs.startup,
            &coordinator,
            coordinator
                .coordinator_attempt()
                .context("relay has no actual coordinator")?,
        )?;
        Ok(Self {
            active: None,
            executions: Vec::new(),
            preparation_failures: Vec::new(),
            dependencies,
            coordinator,
            local_operations: Vec::new(),
            publications: Vec::new(),
            graph: None,
            server,
            factory,
            inputs,
            preparation_output: preparation::Output::new(),
            retained_bytes: preparation::MAX_DIAGNOSTIC_BYTES + std::mem::size_of::<Self>(),
            failed: false,
        })
    }

    /// Poll from the SAME loop that polls the native coordinator lifecycle.
    /// Queries and compilation run on one separate owned worker so Stop and
    /// compiler cancellation remain observable while capture is in progress.
    pub(crate) fn poll(&mut self) -> CargoResult<()> {
        let result = self.poll_inner();
        if result.is_err() {
            self.failed = true;
            self.cancel();
        }
        result
    }
    fn poll_inner(&mut self) -> CargoResult<()> {
        ensure!(!self.failed, "original compiler relay is poisoned");
        self.inputs.validate()?;
        let until = self
            .inputs
            .deadline
            .min(Instant::now() + Duration::from_millis(100));
        // Read an already queued cancellation BEFORE publishing completion.
        // A synchronous child can send it while the native worker retires.
        if let Some(request) = self.server.receive(until)? {
            match request {
                BrokerRequest::Cancel { sequence } => {
                    let active = self
                        .active
                        .as_ref()
                        .context("cancel has no actual compiler worker")?;
                    ensure!(
                        sequence == active.sequence,
                        "cancel names another compiler worker"
                    );
                    active.scope.cancel();
                }
                BrokerRequest::Publish { selection, .. } => {
                    self.publish_unit(selection)?;
                }
                BrokerRequest::FinishGraph { .. } => {
                    if let Err(error) = self.finish_graph() {
                        // A failed final inspection is an explicit refusal,
                        // never a graph closure or a successful child exit.
                        self.server.refuse_graph(
                            bounded_reason(&format!("{error:#}")),
                            self.inputs.deadline.min(Instant::now() + REPLY_BUDGET),
                        )?;
                        // The authenticated refusal closes this protocol. Let
                        // the actual child report it and exit; cancellation
                        // must not replace its original compiler diagnostics.
                        return Ok(());
                    }
                }
                BrokerRequest::Execute {
                    sequence,
                    command,
                    limits,
                } => {
                    ensure!(
                        self.active.is_none(),
                        "parent compiler relay is already active"
                    );
                    ensure!(
                        self.executions.len() < MAX_OPERATIONS,
                        "parent compiler relay exceeds its complete operation bound"
                    );
                    limits.validate()?;
                    let remaining = MAX_RETAINED_BYTES
                        .checked_sub(self.retained_bytes)
                        .context("parent compiler retained byte count overflow")?;
                    let command_bytes = command_demand(&command)?;
                    ensure!(
                        limits
                            .stream_bytes
                            .checked_mul(2)
                            .and_then(|n| n.checked_add(command_bytes))
                            .and_then(|n| n.checked_add(NATIVE_CAPTURE_RESERVE))
                            .is_some_and(|n| n <= remaining),
                        "parent compiler capture exceeds its remaining retained-byte budget"
                    );
                    let (mut process, actual_command) = self.inputs.command(&command)?;
                    let command_bytes = command_bytes
                        .checked_add(command_demand(&actual_command)?)
                        .context("original proposal and command byte count overflow")?;
                    ensure!(
                        limits
                            .stream_bytes
                            .checked_mul(2)
                            .and_then(|n| n.checked_add(command_bytes))
                            .and_then(|n| n.checked_add(NATIVE_CAPTURE_RESERVE))
                            .is_some_and(|n| n <= remaining),
                        "original proposal and finalized command exceed remaining retained-byte budget"
                    );
                    let scope = StreamingProcessScope::new()?;
                    // Issue the exact unit/source/dependency snapshot BEFORE
                    // the actual worker enters capture. Only the ledger can
                    // turn the later SAME native capture into a producer.
                    let (pending, compiler_inputs) =
                        if crate::resource_v3::is_coordinator_query(&actual_command.args) {
                            (None, None)
                        } else {
                            let expected = self.inputs.commands.get().context(
                                "producing compiler arrived without independent command selection",
                            )?;
                            let intents = self
                                .dependencies
                                .as_ref()
                                .context("producing compiler has no original dependency ledger")?
                                .inspection_intents()?;
                            let mut operation =
                                self.begin_local(Kind::PrepareOutputs, None, intents)?;
                            let prepared =
                                (|| -> CargoResult<_> {
                                    let pending = self
                            .dependencies
                            .as_mut()
                            .context("producing compiler lost its original dependency ledger")?
                            .begin(
                                expected,
                                &actual_command,
                                &self.inputs.sources,
                                &mut operation,
                            )?;
                                    // Issue only the SAME pending unit's FD/read/source
                                    // capsule while its actual inspection is still paid.
                                    // CPU admission remains in the worker below so this
                                    // lifecycle can continue observing Stop/cancellation.
                                    let compiler_inputs = self.factory.prepare_unit(&pending)?;
                                    Ok((pending, compiler_inputs))
                                })();
                            let ((pending, compiler_inputs), completed) =
                                self.finish_local(operation, prepared)?;
                            self.retain_local(completed)?;
                            (Some(pending), Some(compiler_inputs))
                        };
                    ensure!(
                        limits
                            .stream_bytes
                            .checked_mul(2)
                            .and_then(|bytes| bytes.checked_add(command_bytes))
                            .and_then(|bytes| bytes.checked_add(NATIVE_CAPTURE_RESERVE))
                            .and_then(|bytes| bytes.checked_add(self.retained_bytes))
                            .is_some_and(|bytes| bytes <= MAX_RETAINED_BYTES),
                        "compiler no longer fits after retaining actual preparation"
                    );
                    process.supervised_by(&scope);
                    let cancel = process
                        .execution_cancellation()
                        .context("compiler scope lost cancellation")?;
                    let factory = self.factory.clone();
                    let inputs = self.inputs.clone();
                    let timeout = Duration::from_nanos(limits.timeout_ns).min(
                        self.inputs
                            .deadline
                            .saturating_duration_since(Instant::now()),
                    );
                    ensure!(!timeout.is_zero(), "parent compiler deadline expired");
                    let capture_limits =
                        StreamingOutputLimits::new(limits.line_bytes, limits.stream_bytes)
                            .with_timeout(timeout)
                            .with_child_exit_cleanup();
                    let worker = std::thread::Builder::new()
                        .name("targo-candidate-compiler".into())
                        .spawn(move || {
                            // Validation failures remain errors before native
                            // delivery; no substitute compiler/pool is started.
                            inputs.validate()?;
                            let executor = match compiler_inputs {
                                Some(originals) => factory
                                    .executor_for_prepared_unit_with_cancellation(
                                        originals, &cancel,
                                    )?,
                                None => factory.executor_with_cancellation(&cancel)?,
                            };
                            let entered = Instant::now();
                            Ok((
                                executor.capture_owned(
                                    &process,
                                    capture_limits,
                                    limits.capture_rusage,
                                ),
                                entered.elapsed(),
                            ))
                        })?;
                    self.retained_bytes += command_bytes;
                    self.active = Some(Active {
                        sequence,
                        proposal: Some(command),
                        command: Some(actual_command),
                        pending,
                        scope,
                        worker: Some(worker),
                    });
                }
            }
        }
        if !self
            .active
            .as_ref()
            .is_some_and(|active| active.worker.as_ref().is_some_and(JoinHandle::is_finished))
        {
            return Ok(());
        }
        self.reap_worker(true)?;
        self.inputs.validate()
    }
    /// Stop only the actual active compiler and join that same worker. Keep
    /// its opaque capture even when the coordinator has closed the broker.
    pub(crate) fn stop(&mut self) -> CargoResult<()> {
        self.cancel();
        if self.active.is_some() {
            self.reap_worker(false)?;
        }
        Ok(())
    }
    fn reap_worker(&mut self, reply: bool) -> CargoResult<()> {
        let mut active = self
            .active
            .take()
            .context("finished worker lost its owner")?;
        let result = match active
            .worker
            .take()
            .context("compiler worker consumed twice")?
            .join()
        {
            Ok(result) => result,
            Err(_) => crate::resource_v3::workload::abort_unknown(),
        };
        let (native, elapsed) = match result {
            Ok(result) => result,
            Err(error) => {
                // This worker returned before capture_owned/native delivery.
                // Keep the failed attempt explicit; no native terminal exists.
                let reason = bounded_reason(&format!("parent preparation: {error:#}"));
                self.preparation_failures.push(PreparationFailure {
                    _proposal: active
                        .proposal
                        .take()
                        .context("failed proposal consumed twice")?,
                    _command: active
                        .command
                        .take()
                        .context("failed command consumed twice")?,
                    _reason: reason.clone(),
                });
                let data = BrokerCaptureData {
                    started: false,
                    status: None,
                    accounting: Observation::uncollected(),
                    stdout: Vec::new(),
                    stderr: Vec::new(),
                    stdout_end: StreamEnd::Pending,
                    stderr_end: StreamEnd::Pending,
                    truncated: false,
                    failure: Some(reason),
                    elapsed_ns: 0,
                };
                // SAFETY: no execution was delivered; the original parent
                // retains the failed input/phase/factory owners. This is an
                // explicit failed observation, never successful retirement.
                if reply {
                    unsafe {
                        self.server.complete(
                            &data,
                            self.inputs.deadline.min(Instant::now() + REPLY_BUDGET),
                        )?;
                    }
                }
                self.failed = true;
                return Err(error);
            }
        };
        let native = Arc::new(native);
        let retained = native.retained_bytes();
        let stream_limit = native
            .capture()
            .limits
            .as_ref()
            .map(|limits| limits.stream_bytes());
        self.executions.push(Execution {
            _proposal: active
                .proposal
                .take()
                .context("completed proposal consumed twice")?,
            command: active
                .command
                .take()
                .context("completed command consumed twice")?,
            native,
            elapsed,
        });
        // Preserve the SAME actual failed capture before any accounting error.
        // Stream capacity and every retained request/final-command copy count;
        // a tiny visible output must not hide large native control snapshots.
        let retained = retained.context("parent native capture size overflow")?;
        ensure!(
            stream_limit
                .and_then(|limit| limit.checked_mul(2))
                .and_then(|limit| limit.checked_add(NATIVE_CAPTURE_RESERVE))
                .is_some_and(|limit| retained <= limit),
            "native compiler capture exceeded its pre-delivery memory reservation"
        );
        self.retained_bytes = self
            .retained_bytes
            .checked_add(retained)
            .filter(|bytes| *bytes <= MAX_RETAINED_BYTES)
            .context("parent compiler retained byte budget exceeded")?;
        let materialized = (|| -> CargoResult<()> {
            if let Some(pending) = active.pending.take() {
                let actual = self
                    .executions
                    .last()
                    .context("completed producer lost its SAME native capture")?;
                let failed =
                    actual
                        .native
                        .native_status()
                        .is_some_and(|frame| match frame.status {
                            trust_resource_controller::Status::Finished { outcome, .. } => {
                                !matches!(outcome, trust_resource_controller::Outcome::Exit(0))
                            }
                            trust_resource_controller::Status::Refused { .. } => true,
                            _ => false,
                        });
                if failed {
                    actual.native.require_compiler_read_retirement(
                        &self.inputs.startup,
                        &actual.command,
                        pending.coordinator_attempt(),
                        pending.issued(),
                    )?;
                    // The SAME failed attempt has physically retired. Retire
                    // every shared reader and record this failed epoch without
                    // invalidating unrelated genuine earlier producers. This
                    // creates no materialization or publication; the retained
                    // native failed capture is relayed below.
                    self.dependencies
                        .as_mut()
                        .context("failed compiler lost its original dependency ledger")?
                        .retire_failed(pending, &actual.native)?;
                    return Ok(());
                }
                let intents = self
                    .dependencies
                    .as_ref()
                    .context("completed producer lost its original dependency ledger")?
                    .materialization_intents(&pending)?;
                let native = self
                    .executions
                    .last()
                    .context("completed producer lost its SAME native capture")?
                    .native
                    .clone();
                let producer = native
                    .native_status()
                    .map(|status| status.member_attempt)
                    .context("completed producer has no actual native member")?;
                let mut operation =
                    self.begin_local(Kind::MaterializeAndPublish, Some(producer), intents)?;
                let result = self
                    .dependencies
                    .as_mut()
                    .context("completed producer lost its original dependency ledger")?
                    .finish(pending, native, &mut operation);
                let ((), completed) = self.finish_local(operation, result)?;
                self.retain_local(completed)?;
            }
            Ok(())
        })();
        let actual = self
            .executions
            .last()
            .context("original compiler capture was not retained")?;
        if reply {
            let data = relay_data(&actual.native, actual.elapsed);
            // SAFETY: the actual native capture and all original owners were
            // retained above. This sends only observations and cannot settle a
            // loan, establish producer eligibility or certify candidate behavior.
            unsafe {
                self.server.complete_with_output(
                    &data,
                    &actual.native.capture().stdout,
                    &actual.native.capture().stderr,
                    self.inputs.deadline.min(Instant::now() + REPLY_BUDGET),
                )?;
            }
        }
        materialized
    }

    fn publish_unit(
        &mut self,
        selection: trust_resource_controller::workload::host::coordinator::PublicationSelection,
    ) -> CargoResult<()> {
        ensure!(
            self.active.is_none(),
            "publication overlaps an actual compiler"
        );
        ensure!(
            !self
                .publications
                .iter()
                .any(|published| published.selection() == &selection),
            "unit publication was already acknowledged in this coordinator epoch"
        );
        ensure!(
            selection
                .retained_bytes()
                .and_then(|bytes| bytes.checked_add(NATIVE_CAPTURE_RESERVE))
                .and_then(|bytes| bytes.checked_add(self.retained_bytes))
                .is_some_and(|bytes| bytes <= MAX_RETAINED_BYTES),
            "publication exceeds remaining native retention reservation"
        );
        let inputs = self.inputs.clone();
        let expected = inputs
            .commands
            .get()
            .context("publication arrived before independent command selection")?;
        let intents = self
            .dependencies
            .as_ref()
            .context("publication has no original dependency ledger")?
            .publication_intents(expected, &selection)?;
        let mut operation = self.begin_local(Kind::PublishFresh, None, intents)?;
        let result = self
            .dependencies
            .as_ref()
            .context("publication lost its original dependency ledger")?
            .publish_unit(expected, &selection, &inputs.sources, &mut operation);
        let (pending, completed) = self.finish_local(operation, result)?;
        let published = pending.complete(completed)?;
        let footprint = published.retained_bytes();
        let capacity = self.publications.capacity();
        // Retain genuine sources, destination originals and the one-use native
        // completion BEFORE accounting or delivery can fail. A path set alone
        // cannot construct this owner or cause the child's skip-write branch.
        self.publications.push(published);
        let bytes = footprint
            .and_then(|bytes| bytes.checked_sub(std::mem::size_of::<PublishedUnit>()))
            .and_then(|bytes| {
                self.publications
                    .capacity()
                    .checked_sub(capacity)
                    .and_then(|slots| slots.checked_mul(std::mem::size_of::<PublishedUnit>()))
                    .and_then(|population| bytes.checked_add(population))
            })
            .context("published unit retained footprint overflow")?;
        self.retained_bytes = self
            .retained_bytes
            .checked_add(bytes)
            .filter(|bytes| *bytes <= MAX_RETAINED_BYTES)
            .context("published unit exceeds retained byte budget")?;
        self.publications
            .last_mut()
            .context("actual published unit was not retained")?
            .acknowledge(
                &mut self.server,
                inputs.deadline.min(Instant::now() + REPLY_BUDGET),
            )
    }

    fn finish_graph(&mut self) -> CargoResult<()> {
        ensure!(
            self.active.is_none() && self.graph.is_none(),
            "graph closure overlaps a compiler or was already consumed"
        );
        let inputs = self.inputs.clone();
        let expected = inputs
            .commands
            .get()
            .context("graph closure has no independently selected commands")?;
        let intents = self
            .dependencies
            .as_ref()
            .context("graph closure has no original dependency ledger")?
            .graph_intents(expected, &self.publications)?;
        let mut operation = self.begin_local(Kind::PrepareOutputs, None, intents)?;
        let result = self
            .dependencies
            .as_ref()
            .context("graph closure lost its original dependency ledger")?
            .inspect_graph(
                expected,
                &inputs.sources,
                &self.publications,
                &mut operation,
            );
        let (pending, completed) = self.finish_local(operation, result)?;
        let graph = pending.complete(completed)?;
        let footprint = graph.retained_bytes();
        // The actual complete population/native return outlives transport,
        // quota failure and the coordinator's later physical retirement.
        self.graph = Some(graph);
        self.retained_bytes = footprint
            .and_then(|bytes| bytes.checked_sub(std::mem::size_of::<GraphClosure>()))
            .and_then(|bytes| bytes.checked_add(self.retained_bytes))
            .filter(|bytes| *bytes <= MAX_RETAINED_BYTES)
            .context("graph closure exceeds retained byte budget")?;
        self.graph
            .as_mut()
            .context("actual graph closure was not retained")?
            .acknowledge(
                &mut self.server,
                inputs.deadline.min(Instant::now() + REPLY_BUDGET),
            )
    }
    pub(crate) fn cancel(&self) {
        if let Some(active) = &self.active {
            active.scope.cancel();
        }
    }
    pub(crate) fn is_idle(&self) -> bool {
        self.active.is_none()
    }
    pub(crate) fn require_dependencies(&self) -> CargoResult<()> {
        ensure!(
            self.is_idle(),
            "dependency graph still has an active compiler"
        );
        self.graph
            .as_ref()
            .context("coordinator exited without its live whole-graph closure")?
            .require_inputs(
                &self.inputs.startup,
                &self.inputs.original,
                &self.inputs.selected_output,
                &self.inputs.outputs,
                self.inputs
                    .commands
                    .get()
                    .context("coordinator has no independently selected graph")?,
            )
    }
    /// Pure access to programs captured by the live paid FinishGraph operation
    /// before its acknowledgement. This performs no post-exit filesystem work.
    fn published_programs(&self) -> CargoResult<&[Arc<PublishedProgram>]> {
        self.require_dependencies()?;
        self.graph
            .as_ref()
            .context("coordinator has no original whole-graph closure")?
            .programs()
    }
    /// Move the SAME retained domain between actual coordinator epochs. No
    /// saved Fresh report or filesystem cache can reconstruct this value.
    pub(crate) fn take_dependencies(&mut self) -> CargoResult<Option<Ledger>> {
        ensure!(
            self.is_idle(),
            "cannot move a ledger with an active compiler"
        );
        Ok(self.dependencies.take())
    }
    /// Counts only the complete actual independently selected graph. Query
    /// processes remain separate; omitted/failed graphs report no counts.
    pub(crate) fn compilation_counts(&self) -> CargoResult<(usize, usize)> {
        self.require_dependencies()?;
        let complete = self
            .inputs
            .commands
            .get()
            .context("coordinator omitted expected graph")?
            .entries()
            .len();
        let executed = self
            .executions
            .iter()
            .filter(|execution| !crate::resource_v3::is_coordinator_query(&execution.command.args))
            .count();
        let reused = complete
            .checked_sub(executed)
            .context("coordinator executed more producing units than its complete graph")?;
        Ok((executed, reused))
    }
}

fn stream_end(end: CaptureStreamEnd) -> StreamEnd {
    match end {
        CaptureStreamEnd::Eof => StreamEnd::Eof,
        CaptureStreamEnd::LeaderExitDrained => StreamEnd::LeaderExitDrained,
        CaptureStreamEnd::Incomplete => StreamEnd::ReadFailed,
    }
}
fn failure(capture: &CapturedProcess) -> Option<String> {
    let mut reasons = Vec::new();
    if let Some(error) = &capture.failure {
        reasons.push(format!("execution: {error:#}"));
    }
    if let Some(error) = &capture.read_error {
        reasons.push(format!("read: {error:#}"));
    }
    if let Some(error) = &capture.cleanup_error {
        reasons.push(format!("cleanup: {error:#}"));
    }
    (!reasons.is_empty()).then(|| bounded_reason(&reasons.join("; ")))
}
fn bounded_reason(reason: &str) -> String {
    let mut end = reason.len().min(4096);
    while !reason.is_char_boundary(end) {
        end -= 1;
    }
    reason[..end].replace('\0', "?")
}
fn relay_data(native: &CoordinatorCompilerCapture, elapsed: Duration) -> BrokerCaptureData {
    let capture = native.capture();
    BrokerCaptureData {
        started: capture.started,
        status: native.native_status().cloned(),
        accounting: native
            .accounting()
            .copied()
            .unwrap_or_else(Observation::uncollected),
        stdout: Vec::new(),
        stderr: Vec::new(),
        stdout_end: stream_end(capture.stdout_end),
        stderr_end: stream_end(capture.stderr_end),
        truncated: capture.stdout_truncated || capture.stderr_truncated,
        failure: failure(capture),
        elapsed_ns: u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX),
    }
}
