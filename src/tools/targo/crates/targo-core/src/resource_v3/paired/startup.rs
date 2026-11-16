//! Consume the authenticated SAME original full-domain startup. The canonical
//! domain is independently opened; neither60/49 nor the store chooses a pool.
//! Only the distinct opaque paired adopter supplies its SAME actual LeaseVec.
use super::super::workload::{
    ProcessInputs,
    bank::{RootCreditBank, broker::Broker},
};
use super::super::{STARTUP, Startup};
use crate::ops::cargo_test::workload::{
    Inputs,
    evidence::{self, Evidence},
};
use crate::util::CargoResult;
use crate::workload_service::Bootstrap;
use anyhow::Context as _;
use std::ffi::OsString;
use std::num::NonZeroU64;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::path::PathBuf;
use std::sync::{Arc, Mutex, atomic::AtomicBool};
use std::time::{Duration, Instant};
use trust_build_cpu::{ExternalDebt, HostPolicy, NativeDomain, NativeUsage};
use trust_resource_controller::{
    BirthKind, ContextQuery, Cpu, Identity, JobBinding, Subject, TelemetryQuery,
    client::sdk::validate_sdk_keeper,
    paired_qualification::{
        PAIRED_PROTOCOL_MARKER, PairedInvocation, budget,
        host::{ReadyReply, ReadyRequest},
    },
    resolver::private_environment_channel,
    workload::WORKLOAD_MEMBER_PROTOCOL_MARKER,
};
use trust_resource_provenance::{
    process,
    program::{HeldProgram, produced::HeldOutputRoot},
};

pub(crate) struct Prepared {
    pub(crate) startup: Arc<Startup>,
    pub(crate) inputs: Inputs,
    pub(crate) ready: ReadyReply,
    pub(crate) deadline: Instant,
}
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
fn actual_identity() -> CargoResult<Identity> {
    let actual = process::read_identity(std::process::id())?;
    Ok(Identity {
        pid: actual.pid,
        birth: actual.birth,
        birth_kind: if cfg!(target_os = "macos") {
            BirthKind::MacosWallMicroseconds
        } else {
            BirthKind::LinuxStartTicks
        },
    })
}

#[expect(
    clippy::disallowed_methods,
    reason = "authenticate original private root binding before configuration"
)]
pub(crate) fn prepare(
    plan: PairedInvocation,
    bootstrap: Bootstrap,
    entered: Instant,
) -> CargoResult<Prepared> {
    anyhow::ensure!(
        super::super::current().is_none(),
        "native root was already initialized"
    );
    plan.validate()?;
    let invocation = &plan.consumer;
    let budget = budget::Budget::new(invocation.repetitions, invocation.timeout_ns)?;
    let deadline = entered
        .checked_add(budget.root_duration())
        .context("paired qualification root deadline is unrepresentable")?;
    let startup_deadline = entered
        .checked_add(Duration::from_nanos(
            trust_resource_controller::workload::budget::STARTUP_NS,
        ))
        .context("paired qualification startup deadline is unrepresentable")?
        .min(deadline);
    anyhow::ensure!(
        bootstrap.cpus.is_present(),
        "paired qualification root has no original inherited CPU set"
    );
    super::super::workload::startup::root_environment(invocation)?;
    let client = bootstrap.store.discover(startup_deadline)?;
    if let Some(observed) = &invocation.observed_host_store {
        anyhow::ensure!(
            client.original_store_path().as_os_str().as_bytes() == observed,
            "workload observed store differs from independently selected original host"
        );
    }
    let binding = JobBinding::from_locator(
        &std::env::var("ATERM_RESOURCE_JOB_V3")
            .context("paired qualification root lacks original private binding")?,
    )?;
    let query = ContextQuery {
        call_attempt: super::super::call_attempt(binding.root_attempt)?,
        binding,
    };
    let request = ReadyRequest {
        query: query.clone(),
        invocation: plan.clone(),
    };
    let actual = actual_identity()?;
    let authenticated =
        client.paired_qualification_ready(&request, bootstrap.cpus, startup_deadline)?;
    let ready = authenticated.observation();
    let context = &ready.context.context;
    anyhow::ensure!(
        context.original_root == actual
            && context.subject == (Subject::Root { identity: actual })
            && matches!(context.cpu, Cpu::CooperativeShared { .. }),
        "workload requires its actual original cooperative root"
    );
    validate_sdk_keeper(context)?;
    anyhow::ensure!(
        context
            .sdk
            .as_ref()
            .is_some_and(|sdk| sdk.execution == invocation.root)
            && std::env::current_exe()?.canonicalize()? == path(&invocation.program.path),
        "workload cannot substitute its original selected SDK/Targo"
    );
    // No path supplied by60/49 or the store selects this independently ready
    // canonical domain. Opening it never retires/repairs/creates a pool.
    let domain = NativeDomain::open_canonical()?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .context("workload canonical CPU debt domain is unavailable")?,
    );
    let (ready, originals, control) = debt.adopt_paired_qualification_startup(authenticated)?;
    let context = ready.context.context.clone();
    let plan = Arc::new(plan);
    let invocation = Arc::new(plan.consumer.clone());
    let targo = Arc::new(HeldProgram::open(
        &path(&invocation.root),
        &path(&invocation.program.path),
        &invocation.program.sha256,
        startup_deadline,
    )?);
    targo.require_paired_protocol_marker(&PAIRED_PROTOCOL_MARKER, startup_deadline)?;
    targo.validate_loaded(
        process::read_identity(std::process::id())?,
        startup_deadline,
    )?;
    let compiler = Arc::new(HeldProgram::open(
        &path(&invocation.root),
        &path(&invocation.compiler.path),
        &invocation.compiler.sha256,
        startup_deadline,
    )?);
    // Even a wholly warm graph cannot stand in for an actually supported SDK.
    compiler.require_workload_member_protocol_marker(
        &WORKLOAD_MEMBER_PROTOCOL_MARKER,
        startup_deadline,
    )?;
    let per_worker = NonZeroU64::new(2 * 1024 * 1024 * 1024).expect("fixed worker memory");
    let local_ceiling =
        super::super::worker_ceiling(originals.len() as u32, context.memory.bytes, per_worker);
    anyhow::ensure!(
        local_ceiling > 0,
        "workload memory cannot cover one original worker envelope"
    );
    let target_plan = trust_resource_provenance::program::HeldRustTargetSysroot::plan(
        compiler.clone(),
        startup_deadline,
    )?;
    let descriptor_budget =
        trust_resource_controller::descriptors::DescriptorBudget::for_preparation(
            local_ceiling as usize,
            0,
        )?;
    let sysroot = descriptor_budget.capture_target(target_plan, startup_deadline)?;
    let environment = std::env::vars_os()
        .filter(|(name, _)| !private_environment_channel(name.as_bytes()))
        .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
        .collect::<Vec<_>>();
    crate::native_query_profile::validate_effective_environment(
        &crate::native_query_profile::Profile::paired_root(&plan),
        &environment,
        &targo.runtime_environment()?,
    )?;
    let (output, writer) = HeldOutputRoot::open_with_evidence(
        &path(&invocation.output_root),
        &targo,
        context.root_attempt,
        1024 * 1024 * 1024,
        4096,
        startup_deadline,
    )?;
    let evidence = Evidence::new(
        writer,
        targo.clone(),
        context.root_attempt,
        ready.invocation_sha256,
        deadline,
    )?;
    evidence::install_abort_evidence(evidence.clone())?;
    let inputs =
        Inputs::from_paired_opened(&plan, &descriptor_budget, output, targo, evidence.clone())?;
    let usage = Arc::new(NativeUsage::new(pool.clone())?);
    let initial = client.telemetry(
        &TelemetryQuery {
            query: ContextQuery {
                binding: query.binding.clone(),
                call_attempt: super::super::call_attempt(context.root_attempt)?,
            },
        },
        startup_deadline,
    )?;
    let monitor = trust_build_cpu::NativeHostObservation::start_with_abort_observer(
        client.clone(),
        query.binding.clone(),
        context.clone(),
        usage.clone(),
        initial,
        deadline,
        evidence::synchronize_abort,
    )?;
    let memory = usage.clone();
    let cpu = usage.clone();
    let policy = Arc::new(
        HostPolicy::new(
            pool.clone(),
            None,
            per_worker,
            trust_build_cpu::default_memory_reserve(),
            Arc::new(move || memory.available_memory()),
        )
        .with_native_cpu(Arc::new(move || cpu.millicores()))
        .with_observation_source(monitor.clone()),
    );
    let policy_for_bank = policy.clone();
    // OWN49/v2 has been authenticated/validated by its opaque adopter. Never
    // construct a v1 Ready or replace FULL60 with the consumer40 digest.
    ready.encode()?;
    let bank = RootCreditBank::from_observed_originals(
        &ready.context,
        ready.invocation_sha256,
        ready.cpu_set().cloned(),
        originals,
        local_ceiling,
        Arc::new(move |busy| policy_for_bank.limit_for(busy)),
    )?;
    let implicit = bank.original_implicit()?;
    let broker = Broker::start(bank.clone(), control, debt.clone(), deadline)?;
    let startup = Arc::new(Startup {
        candidate: None,
        client,
        query,
        _context: context,
        _pool: pool,
        debt,
        policy,
        implicit,
        implicit_busy: Arc::new(AtomicBool::new(false)),
        workload_bank: Some(bank),
        workload_control: Some(Arc::new(Mutex::new(Some(broker)))),
        workload_evidence: Some(evidence),
        workload_process: Some(Arc::new(ProcessInputs {
            invocation: crate::resource_v3::workload::ProcessPlan::Workload(invocation),
            compiler,
            sysroot,
            deadline,
            poisoned: AtomicBool::new(false),
            cancelled: Arc::new(AtomicBool::new(false)),
            _program_reservation: None,
        })),
        descriptor_budget: Some(descriptor_budget),
        paired_invocation: Some(plan),
        native_job_plan: None,
        native_outputs: std::sync::OnceLock::new(),
        local_ceiling,
        original_root: true,
        _usage: usage,
        _monitor: monitor,
        _domain: domain,
    });
    STARTUP
        .set(startup.clone())
        .map_err(|_| anyhow::anyhow!("native root initialized twice"))?;
    // No ordinary v3 initialization/fresh CPU acquisition is performed here.
    crate::set_resource_worker_v3(true, true)?;
    super::super::executor::install(startup.clone())?;
    Ok(Prepared {
        startup,
        inputs,
        ready,
        deadline,
    })
}
