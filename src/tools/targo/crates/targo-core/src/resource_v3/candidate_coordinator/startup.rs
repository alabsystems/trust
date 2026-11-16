//! Authenticate the live registered candidate before project configuration.
//! No original Root Ready, full-domain bank or fresh admission is constructed.
use super::Original;
use crate::{
    resource_v3::{STARTUP, Startup},
    util::CargoResult,
    workload_service::Bootstrap,
};
use anyhow::Context as _;
use std::ffi::OsString;
use std::num::NonZeroU64;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::path::PathBuf;
use std::sync::{Arc, atomic::AtomicBool};
use std::time::{Duration, Instant};
use trust_build_cpu::{ExternalDebt, HostPolicy, NativeDomain, NativeUsage};
use trust_resource_controller::client::sdk::validate_sdk_keeper;
use trust_resource_controller::descriptors::DescriptorBudget;
use trust_resource_controller::workload::host::coordinator::{OriginalRequest, Plan};
use trust_resource_controller::{ContextQuery, JobBinding, Subject, TelemetryQuery};
use trust_resource_provenance::{
    process,
    program::{HeldProgram, HeldRustTargetSysroot},
};

pub(super) fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}

fn deadline(
    entered: Instant,
    original_observed: Instant,
    timeout_ns: u64,
    remaining_ns: u64,
) -> CargoResult<Instant> {
    anyhow::ensure!(
        timeout_ns != 0 && remaining_ns != 0,
        "candidate original deadline is exhausted"
    );
    Ok(entered
        .checked_add(Duration::from_nanos(timeout_ns))
        .context("candidate deadline overflow")?
        .min(
            original_observed
                .checked_add(Duration::from_nanos(remaining_ns))
                .context("candidate remaining Root deadline overflow")?,
        ))
}

#[expect(
    clippy::disallowed_methods,
    reason = "authenticate original candidate before any project/configuration work"
)]
pub(crate) fn prepare(
    plan: Plan,
    bootstrap: Bootstrap,
    entered: Instant,
) -> CargoResult<Arc<Startup>> {
    anyhow::ensure!(
        super::super::current().is_none(),
        "candidate startup already initialized"
    );
    plan.validate()?;
    anyhow::ensure!(
        !bootstrap.cpus.is_present(),
        "candidate cannot import a full Root CPU set"
    );
    let until = entered
        .checked_add(Duration::from_nanos(plan.timeout_ns))
        .context("candidate original deadline overflow")?;
    let connect = until.min(entered + Duration::from_secs(8));
    let client = bootstrap.store.discover(connect)?;
    let binding = JobBinding::from_locator(
        &std::env::var("ATERM_RESOURCE_JOB_V3")
            .context("candidate has no original private job locator")?,
    )?;
    let query = ContextQuery {
        call_attempt: super::super::call_attempt(binding.root_attempt)?,
        binding,
    };
    let initial = client.telemetry(
        &TelemetryQuery {
            query: query.clone(),
        },
        connect,
    )?;
    let actual = process::read_identity(std::process::id())?;
    let Subject::RegisteredMember {
        attempt, identity, ..
    } = initial.reply.context.context.subject
    else {
        anyhow::bail!("candidate requires its actual registered produced member");
    };
    anyhow::ensure!(
        (identity.pid, identity.birth) == (actual.pid, actual.birth),
        "candidate is not the original live registered image"
    );
    let observed = Instant::now();
    // The SAME receiver budget must exist before the client can receive any
    // SCM_RIGHTS originals. The opaque response retains that reservation.
    let descriptor_budget = DescriptorBudget::for_preparation(1, 0)?;
    let authenticated = client.coordinator_original(
        &OriginalRequest {
            query: query.clone(),
            member_attempt: attempt,
        },
        &descriptor_budget,
        connect,
    )?;
    authenticated.validate(connect)?;
    anyhow::ensure!(
        authenticated.observation().plan == plan,
        "candidate startup arguments differ from the SAME Host operation"
    );
    let deadline = deadline(
        entered,
        observed,
        plan.timeout_ns,
        authenticated.observation().remaining_root_ns,
    )?;
    let originals = authenticated
        .into_parts(deadline)
        .map_err(|(error, owner)| {
            // A failed/ambiguous adoption cannot turn the received originals into
            // an apparently unused local CPU or unlock the parent output guards.
            std::mem::forget(owner);
            error
        })?;
    let context = originals.observation().context.context.clone();
    validate_sdk_keeper(&context)?;
    anyhow::ensure!(
        context
            .sdk
            .as_ref()
            .is_some_and(|sdk| sdk.execution == plan.sdk_root),
        "candidate cannot replace the original compiler SDK"
    );
    for (name, expected) in [
        ("RUSTC", plan.compiler.path.as_slice()),
        ("CARGO_HOME", plan.cargo_home.as_slice()),
    ] {
        anyhow::ensure!(
            std::env::var_os(name)
                .as_deref()
                .map(|value| value.as_bytes())
                == Some(expected),
            "candidate lacks original request-bound {name}"
        );
    }
    let domain = NativeDomain::open_canonical()?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .context("candidate original CPU debt domain is unavailable")?,
    );
    // Additional copies/adoption handles are separate from the originals
    // already charged by the receiver before SCM_RIGHTS delivery.
    let compiler_demand = HeldProgram::capture_descriptor_bound()?;
    let input_demand = originals
        .outputs()
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(32))
        .and_then(|count| count.checked_add(compiler_demand))
        .context("candidate original descriptor demand overflow")?;
    // Keep a preparation owner until every local adoption handle has moved
    // into Startup. On any earlier error, implicit closes before this local.
    let input_permit = Arc::new(descriptor_budget.reserve_original_inputs(input_demand)?);
    let implicit = Arc::new(debt.adopt_coordinator_original(&originals, deadline)?);
    let compiler = Arc::new(HeldProgram::open(
        &path(&plan.sdk_root),
        &path(&plan.compiler.path),
        &plan.compiler.sha256,
        deadline,
    )?);
    let sysroot = descriptor_budget.capture_target(
        HeldRustTargetSysroot::plan(compiler.clone(), deadline)?,
        deadline,
    )?;
    let mut sources = Vec::new();
    for selected in &plan.sources {
        let source = descriptor_budget.capture_source(&path(&selected.root), deadline)?;
        anyhow::ensure!(
            source.content_digest() == &selected.sha256,
            "candidate package source differs from the original selected population"
        );
        sources.push(source);
    }
    let manifest_path = path(&plan.manifest.path);
    let selected = sources
        .iter()
        .find(|source| manifest_path.starts_with(source.path()))
        .context("candidate manifest is outside its original source population")?;
    let bytes = selected.read(manifest_path.strip_prefix(selected.path())?, deadline)?;
    let mut digest = cargo_util::Sha256::new();
    digest.update(&bytes);
    anyhow::ensure!(
        digest.finish_hex() == hex::encode(plan.manifest.sha256),
        "candidate manifest bytes changed"
    );
    let outputs = Arc::new(
        crate::compiler::build_runner::OriginalOutputLeases::from_coordinator_originals(
            &originals, deadline,
        )?,
    );
    let originals = Arc::new(originals);
    let broker = originals.broker(&descriptor_budget, deadline)?;
    let candidate = Arc::new(Original {
        broker: std::sync::Mutex::new(broker),
        originals,
        compiler,
        sysroot,
        sources,
        outputs,
        _input_permit: input_permit.clone(),
        deadline,
        busy: Arc::new(AtomicBool::new(false)),
        failed: AtomicBool::new(false),
    });
    candidate.check()?;
    let usage = Arc::new(NativeUsage::new(pool.clone())?);
    let memory = usage.clone();
    let cpu = usage.clone();
    let monitor = super::super::monitor::NativeMonitor::start(
        client.clone(),
        query.binding.clone(),
        context.clone(),
        usage.clone(),
        initial,
    )?;
    let policy = Arc::new(
        HostPolicy::new(
            pool.clone(),
            None,
            NonZeroU64::new(2 * 1024 * 1024 * 1024).expect("fixed worker memory"),
            trust_build_cpu::default_memory_reserve(),
            Arc::new(move || memory.available_memory()),
        )
        .with_native_cpu(Arc::new(move || cpu.millicores()))
        .with_observation_source(monitor.clone()),
    );
    let startup = Arc::new(Startup {
        client,
        query,
        _context: context,
        _pool: pool,
        debt,
        policy,
        implicit,
        implicit_busy: Arc::new(AtomicBool::new(false)),
        workload_bank: None,
        workload_control: None,
        workload_evidence: None,
        workload_process: None,
        descriptor_budget: Some(descriptor_budget),
        paired_invocation: None,
        native_job_plan: None,
        native_outputs: std::sync::OnceLock::new(),
        candidate: Some(candidate),
        local_ceiling: 1,
        original_root: false,
        _usage: usage,
        _monitor: monitor,
        _domain: domain,
    });
    STARTUP
        .set(startup.clone())
        .map_err(|_| anyhow::anyhow!("candidate startup initialized twice"))?;
    crate::set_resource_worker_v3(true, true)?;
    super::super::executor::install(startup.clone())?;
    Ok(startup)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn original_remaining_time_and_initial_invocation_both_bound_candidate() {
        let entered = Instant::now();
        let exchange_started = entered + Duration::from_secs(4);
        assert_eq!(
            deadline(entered, exchange_started, 20_000_000_000, 3_000_000_000).unwrap(),
            entered + Duration::from_secs(7)
        );
        assert_eq!(
            deadline(entered, exchange_started, 5_000_000_000, 30_000_000_000).unwrap(),
            entered + Duration::from_secs(5)
        );
        assert!(deadline(entered, exchange_started, 5_000_000_000, 0).is_err());
        assert!(deadline(entered, exchange_started, 0, 5_000_000_000).is_err());
    }
}
