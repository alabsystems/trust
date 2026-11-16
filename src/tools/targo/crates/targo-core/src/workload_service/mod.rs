//! Native retained workload entry. Bootstrap objects contain only actual
//! inherited descriptions; fields, paths and decoded records cannot mint them.
use std::io;

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod session;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;

pub const PROTOCOL_MARKER: [u8; 64] = trust_resource_controller::workload::WORKLOAD_PROTOCOL_MARKER;

pub fn run(
    args: &[std::ffi::OsString],
    bootstrap: Bootstrap,
    configure_lane: impl FnOnce() -> crate::util::CargoResult<()>,
) -> crate::util::CargoResult<()> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        supported::run(args, bootstrap, configure_lane)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = (args, bootstrap, configure_lane);
        anyhow::bail!("native workload entry is unsupported on this platform")
    }
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod transport;

#[cfg(any(target_os = "linux", target_os = "macos"))]
use trust_resource_controller::client::workload::{
    EarlyCpuSet, EarlyHostStore, PendingCpuSet, PendingHostStore,
};

pub struct PendingBootstrap {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    entered: std::time::Instant,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    cpus: PendingCpuSet,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    store: PendingHostStore,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    initial: Option<trust_resource_controller::client::workload::PendingInitialKeeper>,
}
pub struct Bootstrap {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) entered: std::time::Instant,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) cpus: EarlyCpuSet,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) store: EarlyHostStore,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) initial: Option<trust_resource_controller::client::workload::EarlyInitialKeeper>,
}
impl Bootstrap {
    pub fn is_present(&self) -> bool {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.cpus.is_present() || self.store.is_present() || self.initial.is_some()
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            false
        }
    }
}
/// Snapshot beside the SDK snapshot, before any GNU/FD allocation or threads.
/// Nothing is opened, acquired or authenticated by these locator observations.
pub fn snapshot_bootstrap(first: Option<&std::ffi::OsStr>) -> io::Result<PendingBootstrap> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let entered = std::time::Instant::now();
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        let cpus = trust_resource_controller::client::workload::snapshot_cpu_set()?;
        let initial = match first {
            Some(arg)
                if arg == trust_resource_controller::workload::host::initial::STARTUP_ARGUMENT =>
            {
                Some(trust_resource_controller::client::workload::snapshot_initial_keeper(&cpus)?)
            }
            _ => None,
        };
        Ok(PendingBootstrap {
            entered,
            cpus,
            store: trust_resource_controller::client::workload::snapshot_host_store()?,
            initial,
        })
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = first;
        Ok(PendingBootstrap {})
    }
}
/// # Safety
/// Snapshot all original mapped bootstrap descriptors before allocation;
/// between snapshot and capture only the fixed early GNU/SDK importers may
/// run. Mapped CPU/store slots are original, exclusive and disjoint. No logger,
/// config, callback, thread or child may reuse a slot or read environment while
/// the fixed importer consumes its locator. Actual live49/SDK remains mandatory.
pub unsafe fn capture_bootstrap(pending: PendingBootstrap) -> io::Result<Bootstrap> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        Ok(Bootstrap {
            entered: pending.entered,
            // SAFETY: caller preserves the fixed native startup order above.
            cpus: unsafe {
                trust_resource_controller::client::workload::capture_cpu_set(pending.cpus)?
            },
            // SAFETY: CPU import cannot close/reuse the disjoint original store.
            store: unsafe {
                trust_resource_controller::client::workload::capture_host_store(pending.store)?
            },
            initial: match pending.initial {
                Some(initial) => {
                    let deadline = pending
                        .entered
                        .checked_add(std::time::Duration::from_nanos(
                            trust_resource_controller::workload::budget::STARTUP_NS,
                        ))
                        .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidInput))?;
                    // SAFETY: the fixed Initial entry preserved both disjoint
                    // original slots through the same early import sequence.
                    Some(unsafe {
                        trust_resource_controller::client::workload::capture_initial_keeper(
                            initial, deadline,
                        )?
                    })
                }
                None => None,
            },
        })
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = pending;
        Ok(Bootstrap {})
    }
}

pub fn requested(args: &[std::ffi::OsString]) -> bool {
    startup_mode(args).is_some()
}
#[derive(Clone, Copy)]
pub(crate) enum StartupMode {
    Full,
    Initial,
}
pub(crate) fn startup_mode(args: &[std::ffi::OsString]) -> Option<StartupMode> {
    let arg = args.first()?;
    if arg == trust_resource_controller::workload::WORKLOAD_STARTUP_ARGUMENT {
        Some(StartupMode::Full)
    } else if arg == trust_resource_controller::workload::host::initial::STARTUP_ARGUMENT {
        Some(StartupMode::Initial)
    } else {
        None
    }
}
