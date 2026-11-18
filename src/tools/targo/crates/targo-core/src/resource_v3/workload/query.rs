//! Closed non-producing queries on the SAME original workload bank. Old
//! metadata/resolver roles never enter this owner and no local spawn exists.
use std::io;
use std::os::unix::{ffi::OsStrExt as _, process::ExitStatusExt as _};
use std::process::{ExitStatus, Output};
use std::sync::{Arc, atomic::Ordering};
use std::time::{Duration, Instant};

use super::ProcessInputs;
use crate::native_query_profile::{self, Profile};
use crate::ops::cargo_test::workload::evidence::{Binding, Kind};
use crate::resource_v3::Startup;
use cargo_util::{ExecStats, ProcessBuilder, ProcessExecutor, StreamingOutputLimits};
use trust_resource_controller::{
    CommandSpec, CompletionCause, Outcome, Request, Role, Status,
    client::{MetadataError, MetadataIo, MetadataMember, MetadataOutputStream},
    resolver::private_environment_channel,
    workload::host::{CompilerQuery, MAX_QUERY_NS, MAX_QUERY_OUTPUT},
};

pub(super) fn install(startup: Arc<Startup>) -> io::Result<()> {
    let inputs = startup
        .workload_process
        .as_ref()
        .ok_or_else(|| io::Error::other("workload queries lost original process inputs"))?
        .clone();
    if startup.workload_evidence.is_none() || startup.workload_bank.is_none() {
        return Err(io::Error::other(
            "workload queries lost original bank/evidence custody",
        ));
    }
    cargo_util::install_process_executor(Arc::new(Queries { startup, inputs }))
}
enum NativeRequest {
    Workload(CompilerQuery),
    Paired(trust_resource_controller::paired_qualification::query::CompilerQuery),
    NativeJob(trust_resource_controller::native_job::query::CompilerQuery),
}
impl NativeRequest {
    fn member(&self) -> &Request {
        match self {
            Self::Workload(query) => &query.member,
            Self::Paired(query) => &query.member,
            Self::NativeJob(query) => &query.member,
        }
    }
    fn validate(&self) -> io::Result<()> {
        match self {
            Self::Workload(query) => query.validate(),
            Self::Paired(query) => query.validate(),
            Self::NativeJob(query) => query.validate(),
        }
    }
    fn start(
        &self,
        client: &trust_resource_controller::client::Client,
        io: MetadataIo,
        deadline: Instant,
    ) -> Result<MetadataMember, MetadataError> {
        match self {
            Self::Workload(query) => client.workload_query(query, io, deadline),
            Self::Paired(query) => client.paired_qualification_query(query, io, deadline),
            Self::NativeJob(query) => client.native_job_query(query, io, deadline),
        }
    }
    fn has_completion(&self, member: &MetadataMember) -> bool {
        match self {
            Self::Workload(_) => member.workload_completion().is_some(),
            Self::Paired(_) => member.paired_completion().is_some(),
            Self::NativeJob(_) => member.native_job_completion().is_some(),
        }
    }
}
struct Queries {
    startup: Arc<Startup>,
    inputs: Arc<ProcessInputs>,
}
fn error(reason: impl Into<String>) -> io::Error {
    io::Error::other(reason.into())
}
impl Queries {
    fn command(&self, process: &ProcessBuilder) -> io::Result<(CommandSpec, CommandSpec)> {
        let actual = process.build_command();
        let invocation = self.inputs.invocation.header();
        let environment = process
            .get_effective_envs()?
            .into_iter()
            .filter(|(name, _)| !private_environment_channel(name.as_os_str().as_bytes()))
            .map(|(name, value)| {
                (
                    name.as_os_str().as_bytes().to_vec(),
                    value.as_os_str().as_bytes().to_vec(),
                )
            })
            .collect::<Vec<_>>();
        let observed = CommandSpec {
            program: actual.get_program().as_bytes().to_vec(),
            arg0: process.get_arg0().map(|value| value.as_bytes().to_vec()),
            args: actual
                .get_args()
                .map(|arg| arg.as_bytes().to_vec())
                .collect(),
            cwd: process
                .get_cwd()
                .map(|path| path.as_os_str().as_bytes().to_vec())
                .unwrap_or_else(|| invocation.cwd.to_vec()),
            environment,
        };
        let profile = match &self.inputs.invocation {
            super::ProcessPlan::NativeJob(plan) => Profile::native_job(plan),
            super::ProcessPlan::Workload(invocation) => {
                match self.startup.paired_invocation.as_deref() {
                    Some(plan) => Profile::paired(plan),
                    None => Profile::workload(invocation),
                }
            }
        };
        native_query_profile::validate_process_profile(&profile, process, &observed)?;
        let environment = native_query_profile::forwarded_environment(
            &profile,
            &observed.environment,
            &self.inputs.compiler.runtime_environment()?,
        )?;
        let mut command = observed.clone();
        command.environment = environment;
        Ok((command, observed))
    }

    fn execute(&self, process: &ProcessBuilder) -> io::Result<Output> {
        if self.inputs.cancelled.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "original workload stopped before query delivery",
            ));
        }
        if self.inputs.poisoned.load(Ordering::Acquire) {
            return Err(error(
                "workload query owner is poisoned; no further delivery",
            ));
        }
        let outcome = self.execute_inner(process);
        if outcome.is_err() {
            self.inputs.poisoned.store(true, Ordering::Release);
        }
        outcome
    }
    fn execute_inner(&self, process: &ProcessBuilder) -> io::Result<Output> {
        let (command, observed) = self.command(process)?;
        self.inputs.sysroot.validate(self.inputs.deadline)?;
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .expect("checked original bank");
        let loan = loop {
            if Instant::now() >= self.inputs.deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            if let Some(loan) = bank.try_query()? {
                break loan;
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        let (delegations, descriptions) = super::super::gnu::cpu_only(&loan.lease())?;
        let member_request = Request {
            binding: self.startup.query.binding.clone(),
            member_attempt: super::super::call_attempt(self.startup.query.binding.root_attempt)?,
            role: Role::WorkloadQuery,
            command,
            delegations,
            timeout_ns: Some(MAX_QUERY_NS),
        };
        let request = if let Some(plan) = &self.startup.native_job_plan {
            NativeRequest::NativeJob(
                trust_resource_controller::native_job::query::CompilerQuery {
                    member: member_request,
                    plan_sha256: self
                        .startup
                        .workload_evidence
                        .as_ref()
                        .ok_or_else(|| error("native job lost original evidence binding"))?
                        .invocation_sha256(),
                    sdk_root: plan.inputs.sdk_root.clone(),
                    compiler: plan.inputs.compiler.clone(),
                },
            )
        } else {
            match self.startup.paired_invocation.as_deref() {
                Some(plan) => NativeRequest::Paired(
                    trust_resource_controller::paired_qualification::query::CompilerQuery {
                        member: member_request,
                        invocation: plan.clone(),
                    },
                ),
                None => NativeRequest::Workload(CompilerQuery {
                    member: member_request,
                    root: self.inputs.invocation.header().root.to_vec(),
                    program_sha256: self.inputs.invocation.header().compiler.sha256,
                }),
            }
        };
        request.validate()?;
        let sink = self
            .startup
            .workload_evidence
            .as_ref()
            .expect("checked original evidence");
        let evidence = sink.action(
            Binding {
                member: request.member().member_attempt,
                kind: Kind::CompilerQuery,
                description_sha256: super::super::executor::command_description(&observed),
            },
            MAX_QUERY_OUTPUT as u64,
            MAX_QUERY_OUTPUT as u64,
        )?;
        let mut observe = |stream, bytes: &[u8]| match stream {
            MetadataOutputStream::Stdout => evidence.stdout.append(bytes),
            MetadataOutputStream::Stderr => evidence.stderr.append(bytes),
        };
        loan.begin_query(request.member().member_attempt)?;
        let setup = self
            .inputs
            .deadline
            .min(Instant::now() + Duration::from_secs(30));
        let mut member =
            match request.start(&self.startup.client, MetadataIo { descriptions }, setup) {
                Ok(member) => member,
                Err(MetadataError::BeforeRequest(error)) => {
                    loan.before_request()
                        .unwrap_or_else(|_| super::abort_unknown());
                    self.inputs.sysroot.validate(self.inputs.deadline)?;
                    return Err(error);
                }
                Err(MetadataError::Refused) => {
                    // Explicitly before descriptor attachment/launch. It is not an
                    // ambiguous request error or a fabricated target retirement.
                    loan.before_request()
                        .unwrap_or_else(|_| super::abort_unknown());
                    self.inputs.sysroot.validate(self.inputs.deadline)?;
                    return Err(error("original host refused workload compiler query"));
                }
                Err(MetadataError::Unknown { mut member, .. }) => {
                    fail_unknown(&mut member, &mut observe, sink);
                }
            };
        let mut cancelled = false;
        loop {
            if Instant::now() >= self.inputs.deadline {
                let _ = member.cancel(self.inputs.deadline);
                fail_unknown(&mut member, &mut observe, sink);
            }
            let until = self
                .inputs
                .deadline
                .min(Instant::now() + Duration::from_millis(250));
            if !cancelled && self.inputs.cancelled.load(Ordering::Acquire) {
                cancelled = true;
                if member.cancel(until).is_err() {
                    fail_unknown(&mut member, &mut observe, sink);
                }
            }
            match member.poll_with_observer(until, &mut observe) {
                Ok(Some(result)) => {
                    if !request.has_completion(&member) {
                        fail_unknown(&mut member, &mut observe, sink);
                    }
                    loan.retired().unwrap_or_else(|_| super::abort_unknown());
                    self.inputs.sysroot.validate(self.inputs.deadline)?;
                    if result.output_limit_exceeded || result.completion.inputs_unchanged.is_err() {
                        return Err(error(
                            "workload query changed inputs or exceeded its byte bound",
                        ));
                    }
                    let Status::Finished {
                        outcome,
                        cause: CompletionCause::Exited,
                        ..
                    } = result.completion.finished.status
                    else {
                        return Err(error("workload query has no normal retired exit"));
                    };
                    let status = match outcome {
                        Outcome::Exit(code) => ExitStatus::from_raw(
                            code.checked_mul(256)
                                .ok_or_else(|| error("invalid workload query exit status"))?,
                        ),
                        Outcome::Signal(signal) => ExitStatus::from_raw(signal),
                    };
                    return Ok(Output {
                        status,
                        stdout: result.stdout,
                        stderr: result.stderr,
                    });
                }
                Ok(None) => std::thread::sleep(Duration::from_millis(1)),
                Err(poll_error) => {
                    // Never infer positive Refused from PermissionDenied: a
                    // lost pin can produce the same io kind. This getter uses
                    // the SAME actual retained frame/pin/physical EOF owner.
                    match member.workload_refusal(until) {
                        Ok(Some(_)) => {
                            let observation = member
                                .take_failure_observation_with_observer(&mut observe)?
                                .ok_or_else(|| error("missing actual refused workload capture"))?;
                            sink.publish_failure(&observation)?;
                            loan.retired().unwrap_or_else(|_| super::abort_unknown());
                            self.inputs.sysroot.validate(self.inputs.deadline)?;
                            return Err(poll_error);
                        }
                        _ => fail_unknown(&mut member, &mut observe, sink),
                    }
                }
            }
        }
    }
}
fn fail_unknown(
    member: &mut MetadataMember,
    observer: &mut dyn FnMut(MetadataOutputStream, &[u8]) -> io::Result<()>,
    sink: &Arc<crate::ops::cargo_test::workload::evidence::Evidence>,
) -> ! {
    // Preserve actually received prefixes before the existing unconditional
    // Unknown abort; no catch/resume, retry or logical loan return is possible.
    if let Ok(Some(observation)) = member.take_failure_observation_with_observer(observer) {
        let _ = sink.publish_failure(&observation);
    }
    super::abort_unknown()
}
impl ProcessExecutor for Queries {
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.execute(process)
            .and_then(|output| process.report_captured_status(output))
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        self.execute(process)
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        (
            ExecStats::default(),
            Err(anyhow::anyhow!(
                "workload producing commands require their actual queue dispatch owner"
            )),
        )
    }
}
