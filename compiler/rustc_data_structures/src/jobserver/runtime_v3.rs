//! Borrowed native compiler custody. Authentication precedes CPU admission;
//! this route can never create an original-root credit or a private GNU pool.

use std::ffi::OsStr;
use std::fs::File;
use std::io::{self, Read};
use std::num::NonZeroU64;
use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_build_cpu::{
    ExternalDebt, HostPolicy, Lease, NativeDomain, NativeHostObservation, NativeUsage, WorkerClient,
};
use trust_resource_controller::client::Client as Controller;
use trust_resource_controller::{
    BirthKind, Context, ContextQuery, Cpu, FileIdentity, Identity, JobBinding, Subject,
    TelemetryQuery,
};
use trust_resource_provenance::process;

use super::admission::Client;

/// Original authenticated host binding and retained compiler worker custody.
/// Getters are observations/transport access, never constructors of a grant.
pub struct NativeV3 {
    controller: Controller,
    binding: JobBinding,
    context: Context,
    registry: Arc<super::native_park::Registry>,
    workers: WorkerClient,
    _implicit: Arc<Lease>,
    // Ordinary fresh-domain admission retains its original validators. Workload
    // admission is instead owned by the SAME Host/Root bank and opaque member
    // originals retained by WorkerClient; no second child policy is created.
    owners: RuntimeOwners,
}
enum RuntimeOwners {
    Ordinary { _original: OrdinaryRuntime },
    Workload,
}
struct OrdinaryRuntime {
    _domain: NativeDomain,
    _debt: Arc<ExternalDebt>,
    _policy: Arc<HostPolicy>,
    _usage: Arc<NativeUsage>,
    _observer: Arc<NativeHostObservation>,
}
impl NativeV3 {
    pub(super) fn registry(&self) -> &Arc<super::native_park::Registry> {
        &self.registry
    }
    pub(super) fn workers(&self) -> &WorkerClient {
        &self.workers
    }
    /// Admission exclusion only; the caller must separately join producing work.
    pub fn try_pause(self: &Arc<Self>) -> io::Result<Option<super::CompilerPause>> {
        super::CompilerPause::acquire(self)
    }
    pub fn controller(&self) -> &Controller {
        &self.controller
    }
    pub fn binding(&self) -> &JobBinding {
        &self.binding
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    /// The fixed early route after authenticated original-member adoption.
    /// This observation is not a constructor of a workload capability.
    pub fn is_workload(&self) -> bool {
        matches!(self.owners, RuntimeOwners::Workload)
    }
}

fn refused(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message)
}

// Call ONLY on the actual authenticated telemetry response. This comparison
// does not authenticate arbitrary Context data or acquire any execution grant.
fn member(context: &Context, own: Identity) -> io::Result<(u32, FileIdentity)> {
    if !matches!(context.subject,Subject::RegisteredMember {identity,..} if identity==own) {
        return Err(refused(
            "native compiler must be the exact registered member, never an original root",
        ));
    }
    match context.cpu {
        Cpu::CooperativeShared { ceiling, native_manifest } if ceiling > 0 => {
            Ok((ceiling, native_manifest))
        }
        _ => Err(refused("native compiler cannot enter a retained-fixed external phase")),
    }
}

fn positive(value: Option<&OsStr>, default: u64) -> io::Result<NonZeroU64> {
    value
        .map_or_else(
            || NonZeroU64::new(default),
            |value| value.to_str()?.parse::<u64>().ok().and_then(NonZeroU64::new),
        )
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "native compiler memory settings require positive integers",
            )
        })
}

fn continuation_limit(observed: u32, physical: u32) -> u32 {
    if observed == 0 { 0 } else { physical }
}

fn attempt(root: [u8; 16]) -> io::Result<[u8; 16]> {
    let mut value = [0; 16];
    File::open("/dev/urandom")?.read_exact(&mut value)?;
    if value == [0; 16] || value == root {
        return Err(refused("native compiler observation nonce unavailable"));
    }
    Ok(value)
}

fn worker_parameters(local: &jobserver_crate::Client) -> io::Result<(NonZeroU64, NonZeroU64)> {
    // Probe only actual inherited transport support, never manufacture a
    // serial substitute. An empty valid nonblocking FIFO remains acceptable.
    local.try_acquire().map(drop).map_err(|error| {
        if error.kind() == io::ErrorKind::Unsupported {
            io::Error::new(
                io::ErrorKind::Unsupported,
                "native compiler requires nonblocking inherited GNU transport",
            )
        } else {
            error
        }
    })?;
    let per_worker = positive(std::env::var_os("TARGO_JOB_MEMORY_BYTES").as_deref(), 2 << 30)?;
    let reserve = positive(
        std::env::var_os("TARGO_MEMORY_RESERVE_BYTES").as_deref(),
        trust_build_cpu::default_memory_reserve(),
    )?;
    Ok((per_worker, reserve))
}

pub(super) fn activate(local: jobserver_crate::Client) -> io::Result<Client> {
    let workload_cpu = super::early::take_workload_cpu().map_err(io::Error::other)?;
    let locator = std::env::var_os("ATERM_RESOURCE_JOB_V3")
        .ok_or_else(|| refused("native compiler job locator missing"))?;
    let binding = JobBinding::from_locator(
        locator.to_str().ok_or_else(|| refused("native compiler job locator is not UTF-8"))?,
    )?;
    let deadline = Instant::now() + Duration::from_secs(8);
    let controller = super::early::take_host_controller(deadline).map_err(io::Error::other)?;
    let initial = controller
        .telemetry(
            &TelemetryQuery {
                query: ContextQuery {
                    binding: binding.clone(),
                    call_attempt: attempt(binding.root_attempt)?,
                },
            },
            deadline,
        )
        .map_err(|error| io::Error::other(error.to_string()))?;
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
    let (ceiling, manifest) = member(&context, own)?;
    trust_resource_controller::client::sdk::validate_sdk_keeper(&context)?;
    if let Some(early) = workload_cpu {
        let _parameters = worker_parameters(&local)?;
        use trust_resource_controller::workload::host::MemberOriginalRequest;
        let Subject::RegisteredMember { attempt: member_attempt, .. } = context.subject else {
            return Err(refused("workload compiler is not a registered member"));
        };
        let original = MemberOriginalRequest {
            query: ContextQuery {
                binding: binding.clone(),
                call_attempt: attempt(binding.root_attempt)?,
            },
            member_attempt,
        };
        // Authenticate/consume the SAME original primary BEFORE any canonical
        // domain/census/debt/policy open. Those remain held and enforced by the
        // actual parent Root/Host. No unsupported route retries fresh admission.
        let received = controller
            .workload_member_original(&original, early, deadline)
            .map_err(io::Error::other)?;
        if received.observation().context.context != context {
            return Err(refused("workload primary changed its authenticated compiler context"));
        }
        let owner = trust_build_cpu::process_cpu::read(std::process::id())
            .ok_or_else(|| refused("native compiler CPU owner unavailable"))?
            .owner;
        let global = WorkerClient::new_workload(local.clone(), received, owner, deadline)?;
        let implicit = global.implicit().clone();
        implicit.report_owner(owner)?;
        let custody = Arc::new(NativeV3 {
            controller,
            binding,
            context,
            registry: super::native_park::Registry::new(),
            workers: global.clone(),
            _implicit: implicit,
            owners: RuntimeOwners::Workload,
        });
        return Ok(Client::with_native_v3(local, global, custody));
    }
    let domain = NativeDomain::open_canonical()?;
    let pool = domain.pool().clone();
    let debt = Arc::new(
        ExternalDebt::open(&pool, domain.legacy())?
            .ok_or_else(|| refused("native compiler shared CPU debt domain is absent"))?,
    );
    if debt.native_manifest_identity()? != (manifest.device, manifest.inode)
        || ceiling > pool.slots().get()
    {
        return Err(refused(
            "native compiler host context disagrees with the canonical CPU domain",
        ));
    }
    let (per_worker, reserve) = worker_parameters(&local)?;
    let usage = Arc::new(NativeUsage::new(pool.clone())?);
    let observer = NativeHostObservation::start(
        controller.clone(),
        binding.clone(),
        context.clone(),
        usage.clone(),
        initial,
    )?;
    let memory = usage.clone();
    let cpu = usage.clone();
    let physical = pool.slots().get();
    let policy = Arc::new(
        HostPolicy::new(
            pool,
            None,
            per_worker,
            reserve.get(),
            Arc::new(move || memory.available_memory()),
        )
        .with_native_cpu(Arc::new(move || cpu.millicores()))
        .with_observation_source(observer.clone()),
    );
    // Context memory is ONE common root claim, not one new budget per
    // compiler. Shared GNU and real compiler limits enforce the local cap;
    // global policy must see the actual global held count without a root clamp.
    let implicit = {
        let advertisement = std::env::var_os(jobserver_utils::CPU_HANDOFF_ENV)
            .ok_or_else(|| refused("native compiler scoped CPU handoff missing"))?;
        let (primary, fences) = jobserver_utils::recover_cpu_resources(&advertisement)?;
        if !fences.is_empty() {
            return Err(refused("native compiler refuses legacy epoch fences"));
        }
        let primary = File::from(primary);
        let implicit = loop {
            // Ordinary scoped continuation preserves its existing policy and
            // retained-debt transaction. It never enters the workload bank.
            if let Some(lease) = debt.try_adopt_inherited(&primary, |held| {
                continuation_limit(policy.limit_for(held), physical)
            })? {
                break Arc::new(lease);
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        implicit
    };
    // Core CPU birth is a separate Mach/starttick identity used ONLY for CPU
    // accounting. It is never compared to the authenticated BSD member birth.
    let owner = trust_build_cpu::process_cpu::read(std::process::id())
        .ok_or_else(|| refused("native compiler CPU owner unavailable"))?
        .owner;
    implicit.report_owner(owner)?;
    let global = WorkerClient::new_shared(
        local.clone(),
        debt.clone(),
        implicit.clone(),
        {
            let policy = policy.clone();
            Arc::new(move |held| policy.limit_for(held))
        },
        owner,
    )?;
    let custody = Arc::new(NativeV3 {
        controller,
        binding,
        context,
        registry: super::native_park::Registry::new(),
        workers: global.clone(),
        _implicit: implicit,
        owners: RuntimeOwners::Ordinary {
            _original: OrdinaryRuntime {
                _domain: domain,
                _debt: debt,
                _policy: policy,
                _usage: usage,
                _observer: observer,
            },
        },
    });
    Ok(Client::with_native_v3(local, global, custody))
}

#[cfg(test)]
#[path = "runtime_v3/tests.rs"]
mod tests;
