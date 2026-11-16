//! Consume the authenticated SAME original full-domain startup. The canonical
//! domain is independently opened; neither40/49 nor the store chooses a pool.
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
    native_job::{
        PROTOCOL_MARKER, Plan,
        host::{ReadyReply, ReadyRequest},
    },
    resolver::private_environment_channel,
    workload::{WORKLOAD_MEMBER_PROTOCOL_MARKER, budget},
};
use trust_resource_provenance::{
    process,
    program::{HeldProgram, produced::HeldOutputRoot},
};

pub(crate) struct Prepared {
    pub(crate) startup: Arc<Startup>,
    pub(crate) inputs: Arc<Inputs>,
    // Keep the SAME admitted source capsules throughout root preparation.
    pub(crate) _sources: Vec<Arc<trust_resource_controller::descriptors::AdmittedPackageSource>>,
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
    reason = "validate exact inherited root semantics before project/configuration"
)]
pub(crate) fn root_environment(plan: &Plan) -> CargoResult<()> {
    let invocation = plan.header();
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
pub(crate) fn prepare(plan: Plan, bootstrap: Bootstrap, entered: Instant) -> CargoResult<Prepared> {
    anyhow::ensure!(
        super::super::current().is_none(),
        "native root was already initialized"
    );
    plan.validate()?;
    let deadline = entered
        .checked_add(Duration::from_nanos(plan.timeout_ns))
        .context("native job deadline is unrepresentable")?;
    let startup_deadline = entered
        .checked_add(Duration::from_nanos(budget::STARTUP_NS))
        .context("native job startup deadline is unrepresentable")?
        .min(deadline);
    let invocation = plan.header();
    anyhow::ensure!(
        bootstrap.cpus.is_present(),
        "workload root has no original inherited CPU set"
    );
    root_environment(&plan)?;
    let client = bootstrap.store.discover(startup_deadline)?;
    if let Some(observed) = &plan.inputs.observed_host_store {
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
        plan: plan.clone(),
    };
    let actual = actual_identity()?;
    // Native process capacity is reserved before receiving original SCM
    // descriptions or materializing SDK/runtime inputs. This grants no CPU.
    let descriptor_budget =
        trust_resource_controller::descriptors::DescriptorBudget::for_preparation(7, 0)?;
    let authenticated = client.native_job_ready(
        &request,
        bootstrap.cpus,
        &descriptor_budget,
        startup_deadline,
    )?;
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
            .is_some_and(|sdk| &sdk.execution == invocation.root)
            && std::env::current_exe()?.canonicalize()? == path(&invocation.program.path),
        "workload cannot substitute its original selected SDK/Targo"
    );
    // No path supplied by40/49 or the store selects this independently ready
    // canonical domain. Opening it never retires/repairs/creates a pool.
    let domain = NativeDomain::open_canonical()?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .context("workload canonical CPU debt domain is unavailable")?,
    );
    let mut originals = debt.adopt_native_job_startup(authenticated)?;
    let ready = originals.observation().clone();
    let control = originals.take_control()?;
    let context = ready.context.context.clone();
    let plan = Arc::new(plan);
    let invocation = plan.header();
    let per_worker = NonZeroU64::new(2 * 1024 * 1024 * 1024).expect("fixed worker memory");
    let local_ceiling = super::super::worker_ceiling(
        ready.cpu_set().count() as u32,
        context.memory.bytes,
        per_worker,
    );
    anyhow::ensure!(
        local_ceiling > 0,
        "workload memory cannot cover one original worker envelope"
    );
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
    let bank = RootCreditBank::from_native_job_originals(
        originals,
        local_ceiling,
        Arc::new(move |busy| policy_for_bank.limit_for(busy)),
    )?;
    let implicit = bank.original_implicit()?;
    let preparation = bank
        .try_primary()?
        .context("native job original preparation primary unavailable")?;
    preparation.require_preparation(&implicit)?;
    let program_reservation = Arc::new(
        descriptor_budget.reserve_original_inputs(
            HeldProgram::capture_descriptor_bound()?
                .checked_mul(2)
                .and_then(|n| n.checked_add(16))
                .context("native job program descriptor envelope overflow")?,
        )?,
    );
    let targo = Arc::new(HeldProgram::open(
        &path(&invocation.root),
        &path(&invocation.program.path),
        &invocation.program.sha256,
        startup_deadline,
    )?);
    targo.require_native_job_protocol_marker(&PROTOCOL_MARKER, startup_deadline)?;
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
    let target_plan = trust_resource_provenance::program::HeldRustTargetSysroot::plan(
        compiler.clone(),
        startup_deadline,
    )?;

    let sysroot = descriptor_budget.capture_target(target_plan, startup_deadline)?;
    let environment = std::env::vars_os()
        .filter(|(name, _)| !private_environment_channel(name.as_bytes()))
        .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
        .collect::<Vec<_>>();
    crate::native_query_profile::validate_effective_environment(
        &crate::native_query_profile::Profile::native_job(&plan),
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
    let mut sources = Vec::new();
    for source in &plan.sources {
        let held = descriptor_budget.capture_source(&path(&source.root), startup_deadline)?;
        anyhow::ensure!(
            held.content_digest() == &source.namespace_sha256,
            "native job source namespace differs from its actual original"
        );
        let relative = path(&source.manifest.path)
            .strip_prefix(held.path())?
            .to_owned();
        let bytes = held.read(&relative, startup_deadline)?;
        let mut digest = cargo_util::Sha256::new();
        digest.update(&bytes);
        anyhow::ensure!(
            digest.finish() == source.manifest.sha256,
            "native job manifest differs from its original namespace"
        );
        sources.push(held);
    }
    let inputs = Arc::new(Inputs::from_native_job_opened(
        plan.clone(),
        output,
        targo,
        evidence.clone(),
        program_reservation.clone(),
        sources.clone(),
    )?);
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
            invocation: crate::resource_v3::workload::ProcessPlan::NativeJob(plan.clone()),
            compiler,
            sysroot,
            deadline,
            poisoned: AtomicBool::new(false),
            cancelled: Arc::new(AtomicBool::new(false)),
            _program_reservation: Some(program_reservation),
        })),
        descriptor_budget: Some(descriptor_budget),
        paired_invocation: None,
        native_job_plan: Some(plan),
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
    drop(preparation);
    // No ordinary v3 initialization/fresh CPU acquisition is performed here.
    crate::set_resource_worker_v3(true, true)?;
    super::super::executor::install(startup.clone())?;
    let outputs = super::outputs::Outputs::prepare(&startup, inputs.clone())?;
    startup
        .native_outputs
        .set(outputs)
        .map_err(|_| anyhow::anyhow!("native job output registry initialized twice"))?;
    Ok(Prepared {
        startup,
        inputs,
        _sources: sources,
        ready,
        deadline,
    })
}
