//! Trust: lifetime-owned native CPU admission for a Targo build.

use std::ffi::OsStr;
use std::fs::File;
use std::num::{NonZeroU32, NonZeroU64};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use anyhow::{Context as _, bail};
use cargo_util::{Jobserver, ProcessBuilder};
use jobserver_utils::{CPU_HANDOFF_ENV, recover_cpu_resources};
use trust_build_cpu::{
    HostPolicy, IMPLICIT_FD_ENV, Lease, LegacyFence, MemberScheduling, Monitor, NativeUsage, Pool,
    duplicate_descriptor, duplicate_descriptors, process_cpu,
};

use super::resource_descriptors::{DescriptorBudget, RootPermit};
use super::resource_fifo::PrivateFifo;
use super::{BuildContext, UserIntent};
use crate::util::{CargoResult, GlobalContext};

const GIB: u64 = 1024 * 1024 * 1024;

/// The explicit mode and inherited checked handoff select the same executor.
/// Selection is not admission: construction still validates the epoch, lease,
/// fences, platform and policy before any native root can be dispatched.
pub(super) fn requested(gctx: &GlobalContext) -> bool {
    crate::resource_worker_v2()
        || (gctx.get_env_os(CPU_HANDOFF_ENV).is_some()
            && gctx.get_env_os("BUILD_SLOT_CPU_PROTOCOL") == Some(OsStr::new("2")))
}

fn admitted_intent(verified: bool, retained: bool, intent: UserIntent) -> bool {
    // Check's test bit selects test-target compilation, never test execution.
    // Keep both compile-only forms behind the same unverified boundary.
    (verified && retained && matches!(intent, UserIntent::Test))
        || (!verified
            && matches!(
                intent,
                UserIntent::Build | UserIntent::Check { .. } | UserIntent::Test
            ))
}

#[derive(Clone)]
struct Epoch {
    legacy: PathBuf,
    slots: u32,
    per_worker: NonZeroU64,
    reserve: u64,
}

/// A build owns its policy sampler, FIFO and original borrowed credit.
pub(super) struct ResourceRuntime {
    pool: Pool,
    fence: Arc<LegacyFence>,
    policy: Arc<HostPolicy>,
    _usage: Arc<NativeUsage>,
    jobserver: Jobserver,
    _fifo: Option<Arc<PrivateFifo>>,
    borrowed: Option<Arc<Lease>>,
    borrowed_busy: Arc<AtomicBool>,
    epoch: Epoch,
    owner: trust_build_cpu::Owner,
    descriptors: Arc<DescriptorBudget>,
}

impl ResourceRuntime {
    pub(super) fn new(bcx: &BuildContext<'_, '_>) -> CargoResult<Option<Arc<Self>>> {
        let gctx = bcx.gctx;
        if !requested(gctx) {
            return Ok(None);
        }
        if !admitted_intent(
            crate::trust_verified_targo(),
            gctx.has_retained_test(),
            bcx.build_config.intent,
        ) {
            bail!("native worker CPU admission supports only unverified build/check/test");
        }
        let epoch = Epoch::read(bcx)?;
        DescriptorBudget::prepare(bcx.jobs() as usize)?;
        let physical = std::thread::available_parallelism()
            .context("native CPU admission cannot measure host parallelism")?
            .get();
        let width = NonZeroU32::new(u32::try_from(physical)?).context("empty native CPU pool")?;
        let (pool, fence, borrowed) = inherited_resources(gctx, &epoch, width)?;
        let descriptors = DescriptorBudget::new(bcx.jobs() as usize, fence.files().len())?;
        let owner = process_cpu::read(std::process::id())
            .context("native CPU admission cannot establish its process birth identity")?
            .owner;
        let usage = Arc::new(NativeUsage::new(pool.clone())?);
        let monitor = find_aterm(gctx).and_then(|program| {
            Monitor::spawn(
                program,
                Duration::from_millis(750),
                Duration::from_millis(750),
            )
            .ok()
            .map(Arc::new)
        });
        let memory = Arc::clone(&usage);
        let cpu = Arc::clone(&usage);
        let policy = Arc::new(
            HostPolicy::new(
                pool.clone(),
                monitor,
                epoch.per_worker,
                epoch.reserve,
                Arc::new(move || memory.available_memory()),
            )
            .with_native_cpu(Arc::new(move || cpu.millicores())),
        );
        let (jobserver, fifo) = match gctx.jobserver_from_env()? {
            Some(inherited) if gctx.has_retained_test() => {
                // The retained queue supports an interruptible ready-only
                // waiter on this original checked GNU pipe. Preserve its real
                // capacity rather than replacing an unsupported polling
                // transport with a one-credit nested scheduler.
                (inherited.clone(), None)
            }
            Some(inherited) => {
                super::resource_inherited::scheduler(inherited, borrowed.as_deref())?
            }
            None => {
                // Losing an ancestor's local transport must not enlarge its
                // one borrowed implicit credit into independent local tokens.
                let ceiling = if borrowed.is_some() { 1 } else { bcx.jobs() };
                let fifo = Arc::new(PrivateFifo::new(ceiling)?);
                (fifo.jobserver.clone(), Some(fifo))
            }
        };
        Ok(Some(Arc::new(Self {
            pool,
            fence,
            policy,
            _usage: usage,
            jobserver,
            _fifo: fifo,
            borrowed,
            borrowed_busy: Arc::new(AtomicBool::new(false)),
            epoch,
            owner,
            descriptors,
        })))
    }

    pub(super) fn jobserver(&self) -> Jobserver {
        self.jobserver.clone()
    }

    /// Reserve only at an actual dispatch boundary. A refusal holds nothing
    /// new and never waits while retaining a local scheduling semaphore.
    pub(super) fn try_root(
        self: &Arc<Self>,
        external_serial: bool,
    ) -> CargoResult<Option<Arc<RootContext>>> {
        let Some(descriptors) = self.descriptors.try_root()? else {
            return Ok(None);
        };
        let (lease, borrowed) = if let Some(lease) = &self.borrowed {
            if self
                .borrowed_busy
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                let release = BorrowRelease(Arc::clone(&self.borrowed_busy));
                // Borrowing changes the executor, not the credit count, but
                // critical/unavailable memory still vetoes starting new work.
                if self.policy.limit() == 0 {
                    return Ok(None);
                }
                (Arc::clone(lease), Some(release))
            } else {
                let Some(lease) = self
                    .pool
                    .try_acquire_observed(self.owner, |held| self.policy.limit_for(held))?
                else {
                    return Ok(None);
                };
                (Arc::new(lease), None)
            }
        } else {
            let Some(lease) = self
                .pool
                .try_acquire_observed(self.owner, |held| self.policy.limit_for(held))?
            else {
                return Ok(None);
            };
            (Arc::new(lease), None)
        };
        let jobserver = if external_serial {
            super::resource_serial::jobserver()?
        } else {
            self.jobserver.clone()
        };
        let scheduling = Arc::new(MemberScheduling::retain(
            lease,
            Arc::clone(&self.fence),
            jobserver,
        )?);
        Ok(Some(Arc::new(RootContext {
            _runtime: Arc::clone(self),
            scheduling,
            external_serial,
            epoch: self.epoch.clone(),
            _borrowed: borrowed,
            _descriptors: descriptors,
        })))
    }
}

impl Epoch {
    fn read(bcx: &BuildContext<'_, '_>) -> CargoResult<Self> {
        let gctx = bcx.gctx;
        if gctx.get_env_os("BUILD_SLOT_CPU_PROTOCOL") != Some(OsStr::new("2")) {
            bail!("native CPU admission requires the version-two epoch protocol");
        }
        let legacy = gctx
            .get_env_os("BUILD_SLOT_LEGACY_DIR")
            .or_else(|| gctx.get_env_os("BUILD_SLOT_DIR"))
            .map(PathBuf::from)
            .context("native CPU admission has no legacy namespace")?;
        if !legacy.is_absolute() {
            bail!("native CPU legacy namespace is not absolute");
        }
        if let Some(base) = gctx.get_env_os("BUILD_SLOT_DIR")
            && Path::new(base) != legacy
        {
            bail!("native CPU namespaces disagree");
        }
        if let Some(v2) = gctx.get_env_os("BUILD_SLOT_V2_DIR")
            && Path::new(v2) != legacy.join("runtime-v2")
        {
            bail!("native CPU v2 namespace disagrees");
        }
        let slots = gctx
            .get_env_os("BUILD_SLOT_POOL_SLOTS")
            .and_then(OsStr::to_str)
            .and_then(|value| value.parse::<u32>().ok())
            .filter(|slots| (1..=126).contains(slots))
            .context("invalid native CPU legacy pool width")?;
        let memory = &bcx.build_config.resource_intent.memory;
        let per_worker = NonZeroU64::new(memory.as_ref().map_or(2 * GIB, |p| p.per_worker_bytes))
            .context("native CPU worker memory estimate is zero")?;
        let reserve = memory
            .as_ref()
            .map_or_else(trust_build_cpu::default_memory_reserve, |p| p.reserve_bytes);
        Ok(Self {
            legacy,
            slots,
            per_worker,
            reserve,
        })
    }
}

/// Owns one exec's CPU and legacy fence until its actual completion.
pub(super) struct RootContext {
    _runtime: Arc<ResourceRuntime>,
    scheduling: Arc<MemberScheduling>,
    external_serial: bool,
    epoch: Epoch,
    // Declared last: only make the borrowed credit reusable after the old
    // handoff endpoint, CPU descriptors and child transport have been dropped.
    _borrowed: Option<BorrowRelease>,
    // Release descriptor admission only after all command backing closes.
    _descriptors: RootPermit,
}

impl RootContext {
    pub(super) fn authenticated_test_handoff(
        self: &Arc<Self>,
    ) -> CargoResult<crate::ops::cargo_test::auth_scheduling::OwnedSchedulingHandoff> {
        let mut command = ProcessBuilder::new("retained-test-scheduling");
        self.configure(&mut command, false)?;
        let mut handoff = crate::ops::cargo_test::auth_scheduling::OwnedSchedulingHandoff::new(
            self.scheduling.jobserver(),
            self.scheduling.descriptors().cloned().collect(),
            &command,
        )?;
        // Keep the actual dispatch owner as well as the descriptor copies.
        // Its logical borrowed-credit/descriptor permits must not return to
        // dispatch while an authenticated executor still holds this capsule.
        handoff.retain_origin(Arc::clone(self));
        Ok(handoff)
    }

    pub(super) fn configure(
        &self,
        command: &mut ProcessBuilder,
        compiler: bool,
    ) -> CargoResult<()> {
        command.inherit_jobserver(self.scheduling.jobserver());
        for file in self.scheduling.descriptors() {
            command.inherit_fd_for_exec(Arc::clone(file))?;
        }
        for (name, value) in self.scheduling.environment() {
            command.env(name, value);
        }
        command.env("BUILD_SLOT_CPU_PROTOCOL", "2");
        command.env("BUILD_SLOT_CPU_MODE", "workers-v1");
        command.env("BUILD_SLOT_DIR", &self.epoch.legacy);
        command.env("BUILD_SLOT_LEGACY_DIR", &self.epoch.legacy);
        command.env("BUILD_SLOT_V2_DIR", self.epoch.legacy.join("runtime-v2"));
        command.env("BUILD_SLOT_POOL_SLOTS", self.epoch.slots.to_string());
        command.env(
            "TARGO_JOB_MEMORY_BYTES",
            self.epoch.per_worker.get().to_string(),
        );
        command.env("TARGO_MEMORY_RESERVE_BYTES", self.epoch.reserve.to_string());
        if self.external_serial {
            for name in ["NUM_JOBS", "CARGO_BUILD_JOBS", "TARGO_PLANNED_JOBS"] {
                command.env(name, "1");
            }
        }
        if compiler {
            command.arg("-Zunstable-options");
        }
        if compiler
            && !command
                .get_args()
                .any(|arg| arg == OsStr::new("--resource-worker-v2"))
        {
            command.arg("--resource-worker-v2");
        }
        Ok(())
    }
}

struct BorrowRelease(Arc<AtomicBool>);
impl Drop for BorrowRelease {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

fn inherited_resources(
    gctx: &GlobalContext,
    epoch: &Epoch,
    width: NonZeroU32,
) -> CargoResult<(Pool, Arc<LegacyFence>, Option<Arc<Lease>>)> {
    let validate = |root: Option<File>, files: Vec<File>| -> CargoResult<_> {
        let fence = Arc::new(
            LegacyFence::from_inherited(&epoch.legacy, epoch.slots, files)
                .context("invalid native epoch fence")?,
        );
        let pool = Pool::for_current_user(width)?;
        let borrowed = root
            .map(|file| {
                pool.adopt_inherited_until(
                    &file,
                    std::time::Instant::now() + Duration::from_secs(1),
                )
                .map(Arc::new)
            })
            .transpose()
            .context("invalid inherited implicit CPU credit")?;
        Ok((pool, fence, borrowed))
    };
    let direct = (|| -> CargoResult<_> {
        let fence = gctx
            .get_env_os("BUILD_SLOT_FENCE_FDS")
            .ok_or_else(|| std::io::Error::other("missing native epoch fence descriptors"))?;
        let files = duplicate_descriptors(fence)?;
        let root = gctx
            .get_env_os(IMPLICIT_FD_ENV)
            .map(duplicate_descriptor)
            .transpose()?;
        if root.is_none() && gctx.get_env_os(CPU_HANDOFF_ENV).is_some() {
            bail!("ancestor CPU descriptor must be recovered");
        }
        validate(root, files)
    })();
    match direct {
        Ok(resources) => Ok(resources),
        Err(original) => {
            let Some(advertisement) = gctx.get_env_os(CPU_HANDOFF_ENV) else {
                return Err(original);
            };
            let (root, fences) = recover_cpu_resources(advertisement)
                .context("native CPU ancestor resource recovery failed")?;
            validate(
                Some(File::from(root)),
                fences.into_iter().map(File::from).collect(),
            )
        }
    }
}

fn find_aterm(gctx: &GlobalContext) -> Option<PathBuf> {
    std::env::split_paths(gctx.get_env_os("PATH")?)
        .map(|directory| directory.join("aterm"))
        .map(|path| {
            if path.is_absolute() {
                path
            } else {
                gctx.cwd().join(path)
            }
        })
        .find(|path| {
            path.metadata()
                .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
        })
}

#[cfg(test)]
mod tests {
    use super::{UserIntent, admitted_intent};

    #[test]
    fn authenticated_capsule_retains_actual_dispatch_credit_until_final_drop() {
        use super::*;
        use std::fs::OpenOptions;
        use std::os::unix::fs::OpenOptionsExt as _;

        let directory = tempfile::tempdir().unwrap();
        let legacy = directory.path().join("legacy");
        std::fs::create_dir(&legacy).unwrap();
        let files = ["slot-0", "admission.lock"]
            .into_iter()
            .map(|name| {
                let file = OpenOptions::new()
                    .create_new(true)
                    .read(true)
                    .write(true)
                    .mode(0o600)
                    .open(legacy.join(name))
                    .unwrap();
                crate::util::flock::lock_shared(&file).unwrap();
                file
            })
            .collect();
        let fence = Arc::new(LegacyFence::from_inherited(&legacy, 1, files).unwrap());
        let pool =
            Pool::open_in(&directory.path().join("pool"), NonZeroU32::new(1).unwrap()).unwrap();
        let owner = process_cpu::read(std::process::id()).unwrap().owner;
        let lease = Arc::new(pool.try_acquire(owner).unwrap().unwrap());
        let runtime = Arc::new(ResourceRuntime {
            policy: Arc::new(HostPolicy::new(
                pool.clone(),
                None,
                NonZeroU64::new(GIB).unwrap(),
                0,
                Arc::new(|| Some(8 * GIB)),
            )),
            _usage: Arc::new(NativeUsage::new(pool.clone()).unwrap()),
            pool,
            fence,
            jobserver: Jobserver::new(1).unwrap(),
            _fifo: None,
            borrowed: Some(lease),
            borrowed_busy: Arc::new(AtomicBool::new(false)),
            epoch: Epoch {
                legacy,
                slots: 1,
                per_worker: NonZeroU64::new(GIB).unwrap(),
                reserve: 0,
            },
            owner,
            descriptors: DescriptorBudget::new(1, 2).unwrap(),
        });
        let root = runtime.try_root(false).unwrap().unwrap();
        let weak = Arc::downgrade(&root);
        let capsule = root.authenticated_test_handoff().unwrap();
        drop(root);
        assert!(
            weak.upgrade().is_some(),
            "capsule lost actual dispatch owner"
        );
        assert!(runtime.borrowed_busy.load(Ordering::Acquire));
        assert!(
            runtime.descriptors.try_root().unwrap().is_none(),
            "descriptor permit returned before drain"
        );
        assert!(runtime.try_root(false).unwrap().is_none());
        drop(capsule);
        assert!(weak.upgrade().is_none());
        assert!(!runtime.borrowed_busy.load(Ordering::Acquire));
        assert!(runtime.try_root(false).unwrap().is_some());
    }

    #[test]
    fn only_retained_verified_test_intent_can_retain_native_runtime() {
        assert!(admitted_intent(true, true, UserIntent::Test));
        for intent in [
            UserIntent::Build,
            UserIntent::Check { test: false },
            UserIntent::Bench,
            UserIntent::Check { test: true },
            UserIntent::Doctest,
        ] {
            assert!(!admitted_intent(true, true, intent));
        }
    }

    #[test]
    fn native_compile_intents_include_test_checks_without_verified_execution() {
        for intent in [
            UserIntent::Build,
            UserIntent::Check { test: false },
            UserIntent::Check { test: true },
            UserIntent::Test,
        ] {
            assert!(admitted_intent(false, false, intent));
            assert!(!admitted_intent(true, false, intent));
        }
        for intent in [
            UserIntent::Bench,
            UserIntent::Doc {
                deps: true,
                json: false,
            },
            UserIntent::Doctest,
        ] {
            assert!(!admitted_intent(false, false, intent));
            assert!(!admitted_intent(true, false, intent));
        }
    }
}
