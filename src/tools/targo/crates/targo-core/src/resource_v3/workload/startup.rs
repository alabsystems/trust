//! Consume the authenticated SAME original full-domain startup. The canonical
//! domain is independently opened; neither40/49 nor the store chooses a pool.
use super::super::{STARTUP, Startup};
use super::{
    ProcessInputs,
    bank::{RootCreditBank, broker::Broker},
};
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
    resolver::private_environment_channel,
    workload::{
        WORKLOAD_MEMBER_PROTOCOL_MARKER, WORKLOAD_PROTOCOL_MARKER, WorkloadInvocation, budget,
        host::{ReadyReply, ReadyRequest},
    },
};
use trust_resource_provenance::{
    process,
    program::{HeldProgram, produced::HeldOutputRoot},
};

pub(crate) struct Prepared {
    pub(crate) startup: Arc<Startup>,
    pub(crate) inputs: Inputs,
    pub(crate) ready: ReadyEvidence,
    pub(crate) deadline: Instant,
}
pub(crate) enum ReadyEvidence {
    Full(ReadyReply),
    Initial(trust_resource_controller::workload::host::initial::ReadyReply),
}
impl ReadyEvidence {
    pub(crate) fn context(&self) -> &trust_resource_controller::Context {
        match self {
            Self::Full(ready) => &ready.context.context,
            Self::Initial(ready) => &ready.context.context,
        }
    }
    pub(crate) fn invocation_sha256(&self) -> [u8; 32] {
        match self {
            Self::Full(ready) => ready.invocation_sha256,
            Self::Initial(ready) => ready.invocation_sha256,
        }
    }
    pub(crate) fn funded_width(&self) -> usize {
        match self {
            Self::Full(ready) => ready.cpu_set().count(),
            Self::Initial(_) => 1,
        }
    }
}
enum Authenticated {
    Full(trust_resource_controller::client::workload::AuthenticatedWorkloadStartup),
    Initial(trust_resource_controller::client::workload::AuthenticatedInitialStartup),
}
impl Authenticated {
    fn context(&self) -> &trust_resource_controller::Context {
        match self {
            Self::Full(owner) => &owner.observation().context.context,
            Self::Initial(owner) => &owner.observation().context.context,
        }
    }
}
enum OriginalFunding {
    Full(
        ReadyReply,
        Vec<trust_build_cpu::Lease>,
        trust_resource_controller::client::workload::WorkloadControl,
    ),
    Initial(trust_build_cpu::InitialNativeOriginals),
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
    reason = "validate exact inherited root semantics before project/configuration"
)]
pub(crate) fn root_environment(invocation: &WorkloadInvocation) -> CargoResult<()> {
    for (name, value) in [
        ("LANG", b"C".as_slice()),
        ("LC_ALL", b"C"),
        ("CARGO", invocation.program.path.as_slice()),
        ("RUSTC", invocation.compiler.path.as_slice()),
        ("CARGO_HOME", invocation.cargo_home.as_slice()),
        ("CARGO_CACHE_RUSTC_INFO", b"0"),
    ] {
        anyhow::ensure!(
            std::env::var_os(name).as_deref().map(|v| v.as_bytes()) == Some(value),
            "workload root lacks exact request-bound {name}"
        );
    }
    anyhow::ensure!(
        std::env::current_dir()?
            .canonicalize()?
            .as_os_str()
            .as_bytes()
            == invocation.cwd,
        "workload root cwd differs from original invocation"
    );
    for name in [
        "MAKEFLAGS",
        "MFLAGS",
        "CARGO_MAKEFLAGS",
        "CARGO_JOBSERVER_HANDOFF",
        "TRUST_CPU_HANDOFF",
        "BUILD_SLOT_IMPLICIT_FD",
        "TRUST_JOBSERVER_HANDOFF",
        "BUILD_SLOT_HELD",
    ] {
        anyhow::ensure!(
            std::env::var_os(name).is_none(),
            "workload root cannot import another CPU/GNU context: {name}"
        );
    }
    Ok(())
}

#[expect(
    clippy::disallowed_methods,
    reason = "authenticate original private root binding before configuration"
)]
pub(crate) fn prepare(
    invocation: WorkloadInvocation,
    bootstrap: Bootstrap,
    entered: Instant,
    mode: crate::workload_service::StartupMode,
) -> CargoResult<Prepared> {
    anyhow::ensure!(
        super::super::current().is_none(),
        "native root was already initialized"
    );
    invocation.validate()?;
    let plan = budget::Budget::new(invocation.repetitions, invocation.timeout_ns)?;
    let deadline = entered
        .checked_add(plan.root_duration())
        .context("workload root deadline is unrepresentable")?;
    let startup_deadline = entered
        .checked_add(Duration::from_nanos(budget::STARTUP_NS))
        .context("workload startup deadline is unrepresentable")?
        .min(deadline);
    anyhow::ensure!(
        bootstrap.cpus.is_present(),
        "workload root has no original inherited CPU set"
    );
    root_environment(&invocation)?;
    let client = bootstrap.store.discover(startup_deadline)?;
    if let Some(observed) = &invocation.observed_host_store {
        anyhow::ensure!(
            client.original_store_path().as_os_str().as_bytes() == observed,
            "workload observed store differs from independently selected original host"
        );
    }
    let binding = JobBinding::from_locator(
        &std::env::var("ATERM_RESOURCE_JOB_V3")
            .context("workload root lacks original private binding")?,
    )?;
    let query = ContextQuery {
        call_attempt: super::super::call_attempt(binding.root_attempt)?,
        binding,
    };
    let request = ReadyRequest {
        query: query.clone(),
        invocation: invocation.clone(),
    };
    let actual = actual_identity()?;
    let mut initial_binding = None;
    let authenticated = match mode {
        crate::workload_service::StartupMode::Full => {
            anyhow::ensure!(
                bootstrap.initial.is_none(),
                "Initial keeper cannot downgrade to full V1"
            );
            Authenticated::Full(client.workload_ready(
                &request,
                bootstrap.cpus,
                startup_deadline,
            )?)
        }
        crate::workload_service::StartupMode::Initial => {
            let request = trust_resource_controller::workload::host::initial::ReadyRequest {
                query: query.clone(),
                invocation: invocation.clone(),
                phase: super::super::call_attempt(query.binding.root_attempt)?,
            };
            initial_binding = Some(request.clone());
            Authenticated::Initial(
                client.workload_initial_ready(
                    &request,
                    bootstrap.cpus,
                    bootstrap
                        .initial
                        .context("Initial startup lacks original inherited keeper custody")?,
                    startup_deadline,
                )?,
            )
        }
    };
    let context = authenticated.context();
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
    // No path supplied by40/49 or the store selects this independently ready
    // canonical domain. Opening it never retires/repairs/creates a pool.
    let domain = NativeDomain::open_canonical()
        .context("workload requires its independently ready canonical native CPU domain")?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .context("workload canonical CPU debt domain is unavailable")?,
    );
    let (ready, funding) = match authenticated {
        Authenticated::Full(owner) => {
            let (ready, originals, control) = debt.adopt_workload_startup(owner)?;
            (
                ReadyEvidence::Full(ready.clone()),
                OriginalFunding::Full(ready, originals, control),
            )
        }
        Authenticated::Initial(owner) => {
            let originals = debt.adopt_initial_workload_startup(owner)?;
            (
                ReadyEvidence::Initial(originals.observation().clone()),
                OriginalFunding::Initial(originals),
            )
        }
    };
    let context = ready.context().clone();
    let invocation = Arc::new(invocation);
    let targo = Arc::new(HeldProgram::open(
        &path(&invocation.root),
        &path(&invocation.program.path),
        &invocation.program.sha256,
        startup_deadline,
    )?);
    targo.require_workload_protocol_marker(&WORKLOAD_PROTOCOL_MARKER, startup_deadline)?;
    if matches!(mode, crate::workload_service::StartupMode::Initial) {
        targo.require_initial_cpu_protocol(
            &trust_resource_controller::workload::INITIAL_CPU_PROTOCOL_MARKER,
            startup_deadline,
        )?;
    }
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
    let Cpu::CooperativeShared {
        ceiling: original_ceiling,
        ..
    } = context.cpu
    else {
        anyhow::bail!("workload original cooperative maximum disappeared")
    };
    // This is an upper bound, not funded width: Initial retains only its
    // actual first pair until the same original bank captures further units.
    let local_ceiling =
        super::super::worker_ceiling(original_ceiling, context.memory.bytes, per_worker);
    anyhow::ensure!(
        local_ceiling > 0,
        "workload memory cannot cover one original worker envelope"
    );
    let plan = trust_resource_provenance::program::HeldRustTargetSysroot::plan(
        compiler.clone(),
        startup_deadline,
    )?;
    let descriptor_budget =
        trust_resource_controller::descriptors::DescriptorBudget::for_preparation(
            local_ceiling as usize,
            0,
        )?;
    let sysroot = descriptor_budget.capture_target(plan, startup_deadline)?;
    let environment = std::env::vars_os()
        .filter(|(name, _)| !private_environment_channel(name.as_bytes()))
        .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
        .collect::<Vec<_>>();
    crate::native_query_profile::validate_effective_environment(
        &crate::native_query_profile::Profile::workload(&invocation),
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
        ready.invocation_sha256(),
        deadline,
    )?;
    evidence::install_abort_evidence(evidence.clone())?;
    let inputs = match initial_binding {
        Some(request) => Inputs::from_initial_opened(&request, output, targo, evidence.clone())?,
        None => Inputs::from_opened((*invocation).clone(), output, targo, evidence.clone())?,
    };
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
    let live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync> =
        Arc::new(move |busy| policy_for_bank.limit_for(busy));
    let (bank, control) = match funding {
        OriginalFunding::Full(ready, originals, control) => (
            RootCreditBank::from_originals(&ready, originals, local_ceiling, live_limit)?,
            control,
        ),
        OriginalFunding::Initial(originals) => {
            let (bank, _, control) =
                RootCreditBank::from_initial_originals(originals, local_ceiling, live_limit)?;
            (bank, control)
        }
    };
    bank.bind_descriptor_budget(descriptor_budget.clone())?;
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
        paired_invocation: None,
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
