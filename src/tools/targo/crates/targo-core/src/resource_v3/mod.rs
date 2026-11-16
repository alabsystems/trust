//! Authenticated native-v3 startup, before any CPU admission wait or build work.
//! This module never creates/repairs the canonical memory/CPU domain.

use std::ffi::OsStr;
use std::fs::File;
use std::io::Read;
use std::num::NonZeroU64;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use anyhow::{Context as _, bail};
use jobserver_utils::{CPU_HANDOFF_ENV, DESCENDANT_HANDOFF_ENV, recover_cpu_resources};
use trust_build_cpu::{ExternalDebt, HostPolicy, Lease, NativeUsage, Pool, process_cpu};
use trust_resource_controller::{
    BirthKind, Context, ContextQuery, Cpu, Identity, JobBinding, TelemetryQuery, client::Client,
};
use trust_resource_provenance::process;

use crate::util::{CargoResult, GlobalContext};

pub(crate) mod candidate_coordinator;
mod executor;
pub(crate) use executor::ExecutionLoan;
pub(crate) use executor::{CoordinatorCompilerCapture, CoordinatorCompilerFactory};
mod gnu;
mod monitor;
pub(crate) mod native_job;
pub(crate) mod paired;
pub(crate) mod workload;

static STARTUP: OnceLock<Arc<Startup>> = OnceLock::new();
const GIB: u64 = 1024 * 1024 * 1024;

/// A local policy bound, never a CPU grant. Actual original custody, live
/// host policy and descriptor admission still constrain every worker.
fn worker_ceiling(original_ceiling: u32, memory: u64, per_worker: NonZeroU64) -> u32 {
    original_ceiling.min((memory / per_worker.get()).min(u64::from(u32::MAX)) as u32)
}

#[cfg(test)]
mod worker_ceiling_tests {
    use super::*;

    #[test]
    fn large_machine_uses_original_entitlement_and_memory_envelopes() {
        let envelope = NonZeroU64::new(2 * GIB).unwrap();
        assert_eq!(worker_ceiling(28, 80 * GIB, envelope), 28);
        assert_eq!(worker_ceiling(28, 20 * GIB, envelope), 10);
        assert_eq!(worker_ceiling(3, 80 * GIB, envelope), 3);
        assert_eq!(worker_ceiling(28, 2 * GIB - 1, envelope), 0);
        assert_eq!(worker_ceiling(0, u64::MAX, envelope), 0);
        assert_eq!(worker_ceiling(u32::MAX, u64::MAX, envelope), u32::MAX);
    }
}

/// One original or borrowed implicit credit. Child dispatch must retain this
/// context through positive host retirement; uncertain execution poisons it.
pub(crate) struct Startup {
    pub(crate) client: Client,
    pub(crate) query: ContextQuery,
    // Retain the startup snapshot and pool for the original startup lifetime.
    _context: Context,
    _pool: Pool,
    pub(crate) debt: Arc<ExternalDebt>,
    pub(crate) policy: Arc<HostPolicy>,
    pub(crate) implicit: Arc<Lease>,
    pub(crate) implicit_busy: Arc<std::sync::atomic::AtomicBool>,
    // The candidate's original/copy descriptor reservations outlive the
    // adopted implicit lease as well as its compiler/output descriptions.
    pub(crate) candidate: Option<Arc<candidate_coordinator::Original>>,
    // Present ONLY after distinct authenticated workload startup adopts the
    // actual original full set. Ordinary native build/check never selects it.
    pub(crate) workload_bank: Option<Arc<workload::bank::RootCreditBank>>,
    // The ONE live native control owner. Only final graph settlement may take
    // it out for immutable census/finish; ordinary startup has no such owner.
    pub(crate) workload_control:
        Option<Arc<std::sync::Mutex<Option<workload::bank::broker::Broker>>>>,
    pub(crate) workload_evidence: Option<Arc<crate::ops::cargo_test::workload::evidence::Evidence>>,
    pub(crate) workload_process: Option<Arc<workload::ProcessInputs>>,
    pub(crate) descriptor_budget:
        Option<Arc<trust_resource_controller::descriptors::DescriptorBudget>>,
    // Present ONLY after distinct48/49v2 startup authenticates the full60 plan.
    // A v1/40 root or a decoded plan cannot enter native AY verification.
    pub(crate) paired_invocation:
        Option<Arc<trust_resource_controller::paired_qualification::PairedInvocation>>,
    pub(crate) native_job_plan: Option<Arc<trust_resource_controller::native_job::Plan>>,
    pub(crate) native_outputs: OnceLock<Arc<native_job::outputs::Outputs>>,
    pub(crate) local_ceiling: u32,
    pub(crate) original_root: bool,
    _usage: Arc<NativeUsage>,
    _monitor: Arc<monitor::NativeMonitor>,
    _domain: trust_build_cpu::NativeDomain,
}

pub(crate) fn current() -> Option<Arc<Startup>> {
    STARTUP.get().cloned()
}

pub(crate) fn initialize(gctx: &GlobalContext, command: &str) -> CargoResult<()> {
    if !crate::resource_worker_v3() {
        return Ok(());
    }
    if current().is_some() {
        bail!("native v3 startup already initialized");
    }
    if crate::trust_verified_targo()
        || !crate::trust_no_verify_fast()
        || !matches!(command, "build" | "check")
    {
        bail!("native v3 requires an explicit unverified build/check invocation");
    }
    let locator = gctx
        .get_env_os("ATERM_RESOURCE_JOB_V3")
        .and_then(OsStr::to_str)
        .context("native v3 has no private original-job locator")?;
    let binding =
        JobBinding::from_locator(locator).context("invalid private native job locator")?;
    let deadline = Instant::now() + Duration::from_secs(8);
    let client =
        Client::discover(deadline).context("native v3 has no validated ancestor custodian")?;
    let call_attempt = call_attempt(binding.root_attempt)?;
    let query = ContextQuery {
        binding,
        call_attempt,
    };
    // Authenticate live host/capability/claim/scope BEFORE opening any CPU wait.
    let initial = client
        .telemetry(
            &TelemetryQuery {
                query: query.clone(),
            },
            deadline,
        )
        .context("native v3 context and telemetry lookup failed")?;
    let context = initial.reply.context.context.clone();
    let actual = process::read_identity(std::process::id())?;
    let own = Identity {
        pid: actual.pid,
        birth: actual.birth,
        #[cfg(target_os = "macos")]
        birth_kind: BirthKind::MacosWallMicroseconds,
        #[cfg(target_os = "linux")]
        birth_kind: BirthKind::LinuxStartTicks,
    };
    let (ceiling, manifest) = match context.cpu {
        Cpu::CooperativeShared {
            ceiling,
            native_manifest,
        } => (ceiling, native_manifest),
        Cpu::RetainedFixed { .. } => {
            bail!("native workers cannot enter a retained-fixed external phase")
        }
    };
    trust_resource_controller::client::sdk::validate_sdk_keeper(&context)
        .context("native v3 has no original managed SDK retention guard")?;
    let domain = trust_build_cpu::NativeDomain::open_canonical()
        .context("native v3 CPU domain is not retired and ready")?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .context("native v3 requires the activated shared CPU debt domain")?,
    );
    if debt.native_manifest_identity()? != (manifest.device, manifest.inode)
        || ceiling > pool.slots().get()
    {
        bail!("native v3 context and actual CPU domain disagree");
    }
    let per_worker = match gctx.get_env_os("TARGO_JOB_MEMORY_BYTES") {
        Some(value) => value
            .to_str()
            .and_then(|v| v.parse::<u64>().ok())
            .and_then(NonZeroU64::new)
            .context("invalid native worker memory envelope")?,
        None => NonZeroU64::new(2 * GIB).context("empty native worker envelope")?,
    };
    let local_ceiling = worker_ceiling(ceiling, context.memory.bytes, per_worker);
    if local_ceiling == 0 {
        bail!("native root memory entitlement cannot cover one worker envelope");
    }
    let reserve = match gctx.get_env_os("TARGO_MEMORY_RESERVE_BYTES") {
        Some(value) => value
            .to_str()
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|value| *value > 0)
            .context("invalid native memory reserve")?,
        None => trust_build_cpu::default_memory_reserve(),
    };
    let usage = Arc::new(NativeUsage::new(pool.clone())?);
    let memory = Arc::clone(&usage);
    let cpu = Arc::clone(&usage);
    let monitor = monitor::NativeMonitor::start(
        client.clone(),
        query.binding.clone(),
        context.clone(),
        usage.clone(),
        initial,
    )?;
    // Require the actual custodian's cached native observations. Independent
    // stricter kernel memory bounds them; raw telemetry never enlarges it.
    let policy = Arc::new(
        HostPolicy::new(
            pool.clone(),
            None,
            per_worker,
            reserve,
            Arc::new(move || memory.available_memory()),
        )
        .with_native_cpu(Arc::new(move || cpu.millicores()))
        .with_observation_source(monitor.clone()),
    );
    let new_root = context.may_acquire_initial_cpu(own);
    let inherited = gctx.get_env_os(CPU_HANDOFF_ENV);
    let borrowed = if new_root {
        if inherited.is_some()
            || gctx.get_env_os(DESCENDANT_HANDOFF_ENV).is_some()
            || gctx.jobserver_from_env()?.is_some()
        {
            bail!("original native root cannot also inherit a different worker context");
        }
        None
    } else {
        let ad = inherited
            .context("nested/member native execution requires the existing implicit credit")?;
        if gctx.get_env_os(DESCENDANT_HANDOFF_ENV).is_none() {
            bail!("nested native execution requires the shared GNU context");
        }
        let (primary, fences) = recover_cpu_resources(ad)?;
        if !fences.is_empty() {
            bail!("native v3 refuses legacy epoch fences");
        }
        Some(File::from(primary))
    };
    let owner = process_cpu::read(std::process::id())
        .context("native CPU owner unavailable")?
        .owner;
    let implicit = loop {
        let credit = if let Some(file) = &borrowed {
            // This is already charged to an authenticated parent. Applying a
            // smaller fresh-worker ceiling can strand every continuation while
            // parents retain their credits waiting for these children. Keep
            // the zero veto, then let checked adoption conserve occupancy under
            // the physical/debt bound; NEW workers still use the live ceiling.
            debt.try_adopt_inherited(file, |held| {
                if policy.limit_for(held) == 0 {
                    0
                } else {
                    pool.slots().get()
                }
            })?
        } else {
            debt.try_acquire_observed(owner, |held| policy.limit_for(held))?
        };
        if let Some(credit) = credit {
            break Arc::new(credit);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    STARTUP
        .set(Arc::new(Startup {
            candidate: None,
            client,
            query,
            _context: context,
            _pool: pool,
            debt,
            policy,
            implicit,
            implicit_busy: Arc::new(std::sync::atomic::AtomicBool::new(false)),
            workload_bank: None,
            workload_control: None,
            workload_evidence: None,
            workload_process: None,
            descriptor_budget: None,
            paired_invocation: None,
            native_job_plan: None,
            native_outputs: OnceLock::new(),
            local_ceiling,
            original_root: new_root,
            _usage: usage,
            _monitor: monitor,
            _domain: domain,
        }))
        .map_err(|_| anyhow::anyhow!("native v3 startup already initialized"))?;
    executor::install(current().context("native startup context missing")?)?;
    Ok(())
}
pub(crate) fn compiler_executor(
    startup: Arc<Startup>,
    lease: Arc<Lease>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    workload_loan: Option<Arc<workload::bank::PrimaryLoan>>,
) -> Arc<dyn cargo_util::ProcessExecutor> {
    executor::compiler(startup, lease, jobserver, owner, workload_loan)
}
pub(crate) use executor::NativeVerificationCapture;
pub(crate) fn verification_capture(
    startup: Arc<Startup>,
    lease: Arc<Lease>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    loan: Arc<workload::bank::PrimaryLoan>,
    command: &cargo_util::ProcessBuilder,
    limits: cargo_util::StreamingOutputLimits,
) -> NativeVerificationCapture {
    executor::verification_capture(startup, lease, jobserver, owner, loan, command, limits)
}
pub(crate) fn coordinator_compiler_factory(
    startup: Arc<Startup>,
    coordinator: Arc<workload::bank::PrimaryLoan>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    coordinator_attempt: [u8; 16],
    deadline: Instant,
) -> Arc<CoordinatorCompilerFactory> {
    executor::coordinator_factory(
        startup,
        coordinator,
        jobserver,
        owner,
        coordinator_attempt,
        deadline,
    )
}
pub(crate) fn is_coordinator_query(args: &[Vec<u8>]) -> bool {
    candidate_coordinator::executor::is_query(args)
}
pub(crate) fn call_attempt(root: [u8; 16]) -> std::io::Result<[u8; 16]> {
    let mut random = File::open("/dev/urandom")?;
    loop {
        let mut value = [0; 16];
        random.read_exact(&mut value)?;
        if value != [0; 16] && value != root {
            return Ok(value);
        }
    }
}
