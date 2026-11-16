//! Retained consumer workload observations under the original dependency owner.
//!
//! The producer owns actual admission, compilation/output capsules and running
//! processes. This consumer never reconstructs them from captured reports.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::{Component, Path, PathBuf};
use std::time::Duration;

use serde::Serialize;
use serde_json::{Value, json};
use trust_resource_controller::CompletionCause;
use trust_resource_controller::accounting::{Observation, Scope};
use trust_test_execution::workload::{Action, Inventory, MAX_REPETITIONS, TARGETS};

use crate::dependencies::{DependencyAttempt, ResolverOutcome, Side};
use crate::pair::{FileIdentity, file_identity};
use crate::{Git, Result, refusal, tree};

mod evidence;

#[derive(Clone, Debug, Serialize)]
pub struct Options {
    /// New, exclusively owned result/build directory, outside every input.
    pub output: PathBuf,
    pub repetitions: u32,
    /// Per-phase target budget, started by the actual owning native executor.
    pub timeout: Duration,
}

#[derive(Clone, Debug, Serialize)]
pub struct Request {
    pub side: Side,
    pub sdk_root: PathBuf,
    pub program: FileIdentity,
    pub compiler: FileIdentity,
    pub cwd: PathBuf,
    pub target_directory: PathBuf,
    pub cargo_home: PathBuf,
    pub proof_fixtures: BTreeMap<String, FileIdentity>,
    pub trust_spec_source: FileIdentity,
    pub repetitions: u32,
    pub timeout_ns: u64,
}

/// From the same owning wait, not the outer orchestration process. Root and
/// separately admitted member observations remain separate; never sum them.
#[derive(Clone, Copy, Debug)]
pub struct Measurement {
    pub target_runtime_ns: Option<u64>,
    pub accounting: Observation,
}
impl Measurement {
    fn complete(&self) -> bool {
        self.target_runtime_ns.is_some()
            && self.accounting.scope == Scope::ChildAndWaitedDescendantsV1
            && self.accounting.cpu_times.is_some()
            && self.accounting.peak_rss_bytes.is_some()
    }
    fn report(&self) -> Value {
        json!({"target_runtime_ns":self.target_runtime_ns,
            "accounting":{"scope":"child-and-waited-descendants-v1",
                "cpu_times":self.accounting.cpu_times.map(|cpu|json!({"user_ns":cpu.user_ns,"system_ns":cpu.system_ns})),
                "peak_rss_bytes":self.accounting.peak_rss_bytes}})
    }
}

/// Raw observations only. Live execution eligibility stays with WorkloadRun.
pub struct Capture {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub outcome: ResolverOutcome,
    pub cause: Option<CompletionCause>,
    pub retirement_confirmed: bool,
    pub stdout_eof: bool,
    pub stderr_eof: bool,
    pub output_limit_exceeded: bool,
    pub failure: Option<String>,
    pub measurement: Option<Measurement>,
    pub producer_observation: Value,
}
impl Capture {
    fn terminal(&self) -> bool {
        self.retirement_confirmed
            && self.stdout_eof
            && self.stderr_eof
            && !self.output_limit_exceeded
            && self.failure.is_none()
            && self.cause == Some(CompletionCause::Exited)
            && matches!(self.outcome, ResolverOutcome::Exit(_) | ResolverOutcome::Signal(_))
    }
    fn passed(&self) -> bool {
        self.terminal() && self.outcome == ResolverOutcome::Exit(0)
    }
}

#[derive(Serialize)]
pub struct Artifact {
    pub target: String,
    pub input: FileIdentity,
}

/// Actual compiler graph completion, not an invented exit of the still-live
/// Targo root. Compiler/member process outcomes stay in their own observations.
pub struct Compilation {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub succeeded: bool,
    pub workers_retired: bool,
    pub output_complete: bool,
    pub artifacts: Vec<Artifact>,
    pub unit_observations: Value,
}

pub enum Event {
    Compiled(Compilation),
    Harness { target: String, action: Action, capture: Capture },
    Finished { capture: Capture },
}

/// Starting returns the original live native root at its first checkpoint.
/// The implementation must refuse old/unsupported custody before project work.
pub trait Producer {
    fn start(&mut self, request: &Request) -> Result<Box<dyn Run>>;
    fn start_observation(&self) -> Option<Value> {
        None
    }
}

/// NonClone actual root/graph/output ownership. advance resumes that same
/// graph after the caller's full input check; it must never compile again.
/// stop settles/cancels the original root, never retries another route. Report
/// data cannot implement its production custody or grant execution authority.
pub trait Run {
    fn advance(&mut self) -> Result<Event>;
    fn stop(&mut self) -> Result<Capture>;
    fn observation(&self) -> Value;
}

/// Retained input observation of one actual published executable. This cannot
/// create a produced-artifact execution owner or authenticated PreparedTests.
pub struct ArtifactInput {
    identity: FileIdentity,
    descriptor: File,
    stamp: tree::Fingerprint,
    file_key: (u64, u64),
}
impl ArtifactInput {
    pub fn bind(input: FileIdentity, target_root: &Path) -> Result<Self> {
        if input.link_text.is_some()
            || input.path != input.resolved_path
            || !input.path.starts_with(target_root)
        {
            return Err(refusal("native artifact escapes its own actual target outputs"));
        }
        let before = fs::symlink_metadata(&input.path)?;
        if !before.is_file() || before.mode() & 0o111 == 0 {
            return Err(refusal("native artifact is not an executable regular file"));
        }
        let descriptor = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&input.path)?;
        let actual = descriptor.metadata()?;
        if tree::Fingerprint::of(&before) != tree::Fingerprint::of(&actual)
            || file_identity(&input.path)? != input
        {
            return Err(refusal("native artifact changed while retaining its input"));
        }
        Ok(Self {
            identity: input,
            stamp: tree::Fingerprint::of(&actual),
            file_key: (actual.dev(), actual.ino()),
            descriptor,
        })
    }
    pub fn check(&self) -> Result<()> {
        if tree::Fingerprint::of(&self.descriptor.metadata()?) != self.stamp
            || tree::Fingerprint::of(&fs::symlink_metadata(&self.identity.path)?) != self.stamp
            || file_identity(&self.identity.path)? != self.identity
        {
            return Err(refusal("original native test artifact changed"));
        }
        Ok(())
    }
}

struct SideRun {
    request: Request,
    attempted: bool,
    owner: Option<Box<dyn Run>>,
    start: Option<Value>,
    owner_observation: Option<Value>,
    artifacts: BTreeMap<String, ArtifactInput>,
    inventories: BTreeMap<String, Inventory>,
    records: Vec<Value>,
    compiled: bool,
    finished: bool,
    samples: BTreeSet<(String, u32)>,
}

/// Original inputs and live native producer owners survive every outcome.
/// There is no constructor from saved plan/capture/measurement bytes.
pub struct WorkloadAttempt {
    dependencies: DependencyAttempt,
    options: Options,
    sides: Vec<SideRun>,
    errors: Vec<String>,
    failures: Vec<String>,
    evidence: evidence::Budget,
}

impl DependencyAttempt {
    pub fn execute_workloads(
        self,
        git: &impl Git,
        producer: &mut impl Producer,
        options: Options,
    ) -> WorkloadAttempt {
        WorkloadAttempt::run(self, git, producer, options)
    }
}

impl WorkloadAttempt {
    fn run(
        dependencies: DependencyAttempt,
        git: &impl Git,
        producer: &mut impl Producer,
        options: Options,
    ) -> Self {
        let mut result = Self {
            dependencies,
            options: options.clone(),
            sides: Vec::new(),
            errors: Vec::new(),
            failures: Vec::new(),
            evidence: Default::default(),
        };
        if !result.dependencies.consistent() {
            result.errors.push("original compiler probes/dependency resolution refused; workload producer not called".into());
        }
        let plan = (|| -> Result<Vec<Request>> {
            let timeout_ns = u64::try_from(options.timeout.as_nanos())
                .map_err(|_| refusal("workload target timeout exceeds native bound"))?;
            if options.repetitions == 0
                || options.repetitions > MAX_REPETITIONS
                || timeout_ns == 0
                || !options.output.is_absolute()
                || options
                    .output
                    .components()
                    .any(|c| matches!(c, Component::ParentDir | Component::CurDir))
            {
                return Err(refusal("invalid finite workload options/output path"));
            }
            if fs::symlink_metadata(&options.output).is_ok() {
                return Err(refusal("workload result directory must be new"));
            }
            let parent = options
                .output
                .parent()
                .ok_or_else(|| refusal("workload output has no parent"))?
                .canonicalize()?;
            let output = parent.join(
                options.output.file_name().ok_or_else(|| refusal("workload output has no name"))?,
            );
            let snapshot = result.dependencies.snapshot();
            let cargo_home = result.dependencies.requested_inputs().cargo_home.canonicalize()?;
            for input in snapshot
                .sources
                .values()
                .map(|s| &s.path)
                .chain([&snapshot.control.path, &snapshot.candidate.path])
                .map(PathBuf::as_path)
                .chain(std::iter::once(cargo_home.as_path()))
                .chain(result.dependencies.dependency_input_roots())
            {
                if output.starts_with(input) || input.starts_with(&output) {
                    return Err(refusal("workload output aliases a frozen input"));
                }
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
                    target_directory: output.join(name),
                    cargo_home: result.dependencies.requested_inputs().cargo_home.clone(),
                    proof_fixtures: snapshot.proof_fixtures.clone(),
                    trust_spec_source: snapshot.trust_spec_source.clone(),
                    repetitions: options.repetitions,
                    timeout_ns,
                });
            }
            Ok(requests)
        })();
        match plan {
            Ok(requests) => {
                result.sides = requests
                    .into_iter()
                    .map(|request| SideRun {
                        request,
                        attempted: false,
                        owner: None,
                        start: None,
                        owner_observation: None,
                        artifacts: BTreeMap::new(),
                        inventories: BTreeMap::new(),
                        records: Vec::new(),
                        compiled: false,
                        finished: false,
                        samples: BTreeSet::new(),
                    })
                    .collect()
            }
            Err(e) => result.errors.push(e.to_string()),
        }
        result.check_inputs(git);
        for side in 0..result.sides.len() {
            if !result.errors.is_empty() {
                break;
            }
            result.sides[side].attempted = true;
            let started = producer.start(&result.sides[side].request);
            if let Some(observation) = producer.start_observation() {
                let stored = result.evidence.value(&observation);
                result.sides[side].start = Some(stored.value);
                if !stored.complete {
                    result
                        .errors
                        .push("workload start observation exceeds finite evidence bounds".into());
                }
            }
            match started {
                Ok(owner) => result.sides[side].owner = Some(owner),
                Err(e) => result.producer_error(side, "start", e),
            }
            result.check_inputs(git);
            while result.errors.is_empty() && !result.sides[side].finished {
                result.check_inputs(git);
                if !result.errors.is_empty() {
                    break;
                }
                let event = result.sides[side].owner.as_mut().expect("started owner").advance();
                match event {
                    Ok(event) => {
                        if let Err(e) = result.consume(side, event) {
                            result.errors.push(e.to_string())
                        }
                    }
                    Err(e) => result.producer_error(side, "advance", e),
                }
                result.check_inputs(git);
            }
            if !result.sides[side].finished {
                if let Some(owner) = result.sides[side].owner.as_mut() {
                    let stopped = owner.stop();
                    match stopped {
                        Ok(capture) => {
                            let (stored, complete) = result.capture_report(&capture);
                            result.sides[side]
                                .records
                                .push(json!({"stage":"original-root-stop","capture":stored}));
                            if !complete {
                                result.errors.push(
                                    "workload stop capture exceeds finite evidence bounds".into(),
                                );
                            }
                            if !capture.retirement_confirmed
                                || !capture.stdout_eof
                                || !capture.stderr_eof
                                || capture.failure.is_some()
                                || capture.output_limit_exceeded
                            {
                                result.errors.push("original workload root stop did not establish positive retirement/drain".into());
                            }
                        }
                        Err(e) => result.producer_error(side, "stop", e),
                    }
                }
                result.check_inputs(git);
            }
            if let Some(observation) =
                result.sides[side].owner.as_ref().map(|owner| owner.observation())
            {
                let stored = result.evidence.value(&observation);
                result.sides[side].owner_observation = Some(stored.value);
                if !stored.complete {
                    result
                        .errors
                        .push("workload owner observation exceeds finite evidence bounds".into());
                }
                result.check_inputs(git);
            }
        }
        result.check_inputs(git);
        result
    }

    fn check_inputs(&mut self, git: &impl Git) {
        if let Err(e) = self.dependencies.check_unchanged(git) {
            self.errors.push(e.to_string())
        }
        for side in &self.sides {
            for artifact in side.artifacts.values() {
                if let Err(e) = artifact.check() {
                    self.errors.push(e.to_string())
                }
            }
        }
    }

    fn producer_error(&mut self, index: usize, stage: &str, error: crate::Refusal) {
        let stored = self.evidence.serialize(&error.0);
        self.sides[index]
            .records
            .push(json!({"stage":"producer-error","operation":stage,"error":stored.value}));
        self.errors.push(format!(
            "original workload producer {stage} refused{}",
            if stored.complete { "" } else { "; error evidence exceeded finite bounds" }
        ));
    }

    fn capture_report(&mut self, capture: &Capture) -> (Value, bool) {
        let raw = self.evidence.raw(&capture.stdout, &capture.stderr);
        let observation = self.evidence.value(&capture.producer_observation);
        let failure = self.evidence.serialize(&capture.failure);
        let mut record = json!({"outcome":capture.outcome,"cause":capture.cause.map(|cause|match cause {
            CompletionCause::Exited=>"exited",CompletionCause::Timeout=>"timeout",
            CompletionCause::Cancelled=>"cancelled",CompletionCause::ResourceLimit=>"resource_limit",
            CompletionCause::HostFault=>"host_fault"}),
            "retirement_confirmed":capture.retirement_confirmed,"stdout_eof":capture.stdout_eof,
            "stderr_eof":capture.stderr_eof,"output_limit_exceeded":capture.output_limit_exceeded,
            "measurement":capture.measurement.as_ref().map(Measurement::report)});
        if let Value::Object(fields) = raw.value {
            record.as_object_mut().expect("record").extend(fields);
        }
        record["failure"] = failure.value;
        record["producer_observation"] = observation.value;
        (record, raw.complete && failure.complete && observation.complete)
    }

    fn consume(&mut self, index: usize, event: Event) -> Result<()> {
        match event {
            Event::Compiled(compilation) => {
                let Compilation {
                    stdout,
                    stderr,
                    succeeded,
                    workers_retired,
                    output_complete,
                    artifacts,
                    unit_observations,
                } = compilation;
                let raw = self.evidence.raw(&stdout, &stderr);
                let observations = self.evidence.value(&unit_observations);
                let population = self
                    .evidence
                    .serialize(&artifacts.iter().take(TARGETS.len() + 1).collect::<Vec<_>>());
                let mut record = json!({"stage":"compilation","succeeded":succeeded,
                    "workers_retired":workers_retired,"output_complete":output_complete,
                    "reported_artifact_count":artifacts.len()});
                if let Value::Object(fields) = raw.value {
                    record.as_object_mut().expect("record").extend(fields);
                }
                record["artifacts"] = population.value;
                record["unit_observations"] = observations.value;
                self.sides[index].records.push(record);
                if !raw.complete || !observations.complete || !population.complete {
                    return Err(refusal("compiler capture exceeds finite workload bounds"));
                }
                let side = &mut self.sides[index];
                if side.compiled
                    || !succeeded
                    || !workers_retired
                    || !output_complete
                    || artifacts.len() != TARGETS.len()
                {
                    return Err(refusal(
                        "workload compilation did not produce its one complete artifact population",
                    ));
                }
                let root = side.request.target_directory.canonicalize()?;
                if root != side.request.target_directory {
                    return Err(refusal(
                        "native target output directory is an alias outside its original run",
                    ));
                }
                let mut keys = BTreeSet::new();
                for artifact in artifacts {
                    if !TARGETS.contains(&artifact.target.as_str())
                        || side.artifacts.contains_key(&artifact.target)
                    {
                        return Err(refusal("missing, duplicate or unsupported native target"));
                    }
                    let input = ArtifactInput::bind(artifact.input, &root)?;
                    if !keys.insert(input.file_key) {
                        return Err(refusal(
                            "distinct native test targets alias one actual executable",
                        ));
                    }
                    side.artifacts.insert(artifact.target, input);
                }
                side.compiled = true;
            }
            Event::Harness { target, action, capture } => {
                let (stored, complete) = self.capture_report(&capture);
                let target_record = self.evidence.serialize(&target);
                self.sides[index].records.push(json!({"stage":"harness","target":target_record.value,"action":action,"capture":stored}));
                if !complete || !target_record.complete {
                    return Err(refusal("workload action exceeds finite evidence bounds"));
                }
                if !capture.terminal() {
                    return Err(refusal(
                        "workload action has no positively retired/drained normal outcome",
                    ));
                }
                if !self.sides[index].compiled || !self.sides[index].artifacts.contains_key(&target)
                {
                    return Err(refusal(
                        "native harness is outside its original compiled population",
                    ));
                }
                match action {
                    Action::Inventory => {
                        if !capture.passed()
                            || !self.sides[index].samples.is_empty()
                            || self.sides[index].inventories.contains_key(&target)
                        {
                            return Err(refusal(
                                "missing, failed, duplicate or late native inventory",
                            ));
                        }
                        let inventory = Inventory::parse(&capture.stdout).map_err(refusal)?;
                        if index == 1 && self.sides[0].inventories.get(&target) != Some(&inventory)
                        {
                            return Err(refusal(
                                "control/candidate complete native test denominator differs",
                            ));
                        }
                        self.sides[index].inventories.insert(target, inventory);
                    }
                    Action::Sample { repetition } => {
                        let side = &mut self.sides[index];
                        if side.inventories.len() != TARGETS.len()
                            || repetition == 0
                            || repetition > side.request.repetitions
                            || (repetition > 1
                                && !side.samples.contains(&(target.clone(), repetition - 1)))
                            || !side.samples.insert((target.clone(), repetition))
                        {
                            return Err(refusal(
                                "native sample omits the full inventory barrier or repeats/skips an action",
                            ));
                        }
                        if !capture.measurement.as_ref().is_some_and(Measurement::complete) {
                            self.failures.push(format!(
                                "{:?}/{target}/{repetition}: native target accounting incomplete",
                                side.request.side
                            ))
                        }
                        if capture.passed() {
                            if let Err(e) = side.inventories[&target]
                                .validate_sample(&capture.stdout, &capture.stderr)
                            {
                                self.failures.push(format!(
                                    "{:?}/{target}/{repetition}: {e}",
                                    side.request.side
                                ))
                            }
                        } else {
                            self.failures.push(format!(
                                "{:?}/{target}/{repetition}: actual failed native outcome {:?}",
                                side.request.side, capture.outcome
                            ))
                        }
                    }
                }
            }
            Event::Finished { capture } => {
                let (stored, complete) = self.capture_report(&capture);
                self.sides[index]
                    .records
                    .push(json!({"stage":"original-root-retirement","capture":stored}));
                if !complete {
                    return Err(refusal("workload terminal exceeds finite evidence bounds"));
                }
                if !capture.terminal() {
                    return Err(refusal(
                        "workload action has no positively retired/drained normal outcome",
                    ));
                }
                if !capture.passed() {
                    self.failures.push(format!(
                        "{:?}: actual workload root failed {:?}",
                        self.sides[index].request.side, capture.outcome
                    ))
                }
                let side = &mut self.sides[index];
                if !side.compiled
                    || side.inventories.len() != TARGETS.len()
                    || side.samples.len() != TARGETS.len() * side.request.repetitions as usize
                {
                    return Err(refusal(
                        "native workload root finished with missing planned actions",
                    ));
                }
                side.finished = true;
            }
        }
        Ok(())
    }

    pub fn consistent(&self) -> bool {
        self.errors.is_empty()
            && self.failures.is_empty()
            && self.sides.len() == 2
            && self.sides.iter().all(|s| s.finished)
    }

    pub fn check_unchanged(&self, git: &impl Git) -> Result<()> {
        let mut errors = Vec::new();
        if let Err(e) = self.dependencies.check_unchanged(git) {
            errors.push(e.to_string())
        }
        for side in &self.sides {
            for artifact in side.artifacts.values() {
                if let Err(e) = artifact.check() {
                    errors.push(e.to_string())
                }
            }
        }
        if errors.is_empty() { Ok(()) } else { Err(refusal(errors.join("; "))) }
    }

    pub fn report(&self) -> Value {
        json!({"schema":"trust.paired-qualification.v1","stage":"native-consumer-workload",
            "status":if self.consistent(){"consumer-workload-observations-checked"}else if self.errors.is_empty(){"consumer-workload-observed-with-failures"}else{"refused"},
            "claim_scope":"native consumer observations; root/member metrics retain separate owning-wait scopes; no source/build/proof/authentication, admission or publication grant",
            "requested_options":self.options,
            "dependencies":self.dependencies.report(),"errors":self.errors,"failures":self.failures,
            "pending_stages":["native-AY-census-production","source-bound-census-comparison","remaining-lock-and-writer-policy","all-active-callers-and-helper-retirement","whole-paired-workload-qualification"],
            "sides":self.sides.iter().map(|side|json!({"request":side.request,"attempted":side.attempted,
                "start":side.start,"compiled":side.compiled,"finished":side.finished,"inventories":side.inventories,
                "artifacts":side.artifacts.iter().map(|(name,a)|(name,&a.identity)).collect::<BTreeMap<_,_>>(),
                "planned_samples":TARGETS.len()*side.request.repetitions as usize,"observed_samples":side.samples,
                "planned_actions":side.planned_actions(),
                "records":side.records,"live_owner_observation":side.owner_observation})).collect::<Vec<_>>()})
    }
}

impl SideRun {
    fn planned_actions(&self) -> Vec<Value> {
        let status = |observed: bool| {
            if observed {
                "observed"
            } else if self.attempted {
                // A missing event after possible delivery is not proof that the
                // target did not execute. Keep uncertainty visible in the census.
                "unobserved-possibly-started"
            } else {
                "not-started"
            }
        };
        let mut actions = vec![
            json!({"stage":"compilation","status":status(self.records.iter().any(|r|r["stage"]=="compilation"))}),
        ];
        for target in TARGETS {
            let observed = |action: Action| {
                self.records.iter().any(|r| {
                    r["stage"] == "harness"
                        && r["target"] == target
                        && r["action"] == serde_json::to_value(action).expect("bounded action")
                })
            };
            actions.push(json!({"stage":"harness","target":target,"action":Action::Inventory,
                "status":status(observed(Action::Inventory))}));
        }
        for target in TARGETS {
            for repetition in 1..=self.request.repetitions {
                let action = Action::Sample { repetition };
                let observed = self.records.iter().any(|r| {
                    r["stage"] == "harness"
                        && r["target"] == target
                        && r["action"] == serde_json::to_value(action).expect("bounded action")
                });
                actions.push(json!({"stage":"harness","target":target,"action":action,"status":status(observed)}));
            }
        }
        actions.push(json!({"stage":"original-root-retirement",
            "status":status(self.records.iter().any(|r|r["stage"]=="original-root-retirement"))}));
        actions
    }
}

#[cfg(test)]
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests;
