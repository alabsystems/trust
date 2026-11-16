// Trust: validate inherited runtime ownership before any native worker starts.
use std::io;

use super::admission::Client;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn activate(local: jobserver_crate::Client) -> io::Result<Client> {
    use std::fs::File;
    use std::num::NonZeroU64;
    use std::os::fd::OwnedFd;
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::time::Duration;

    use trust_build_cpu::{HostPolicy, LegacyFence, Monitor, NativeUsage, Pool, WorkerClient};

    let required = |name| {
        std::env::var_os(name)
            .ok_or_else(|| io::Error::other(format!("native worker is missing {name}")))
    };
    if required("BUILD_SLOT_CPU_PROTOCOL")? != "2" {
        return Err(io::Error::other("native worker needs the version-two owner protocol"));
    }
    let directory = PathBuf::from(required("BUILD_SLOT_LEGACY_DIR")?);
    let slots = required("BUILD_SLOT_POOL_SLOTS")?
        .to_str()
        .and_then(|s| s.parse::<u32>().ok())
        .ok_or_else(|| io::Error::other("invalid native worker fence width"))?;
    let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?
        .ok_or_else(|| io::Error::other("native worker CPU pool is absent"))?;
    let direct = (|| -> io::Result<_> {
        let cpu =
            trust_build_cpu::duplicate_descriptor(&required(trust_build_cpu::IMPLICIT_FD_ENV)?)?;
        let fences = trust_build_cpu::duplicate_descriptors(&required("BUILD_SLOT_FENCE_FDS")?)?;
        let lease =
            pool.adopt_inherited_until(&cpu, std::time::Instant::now() + Duration::from_secs(1))?;
        let fence = LegacyFence::from_inherited(&directory, slots, fences)?;
        Ok((lease, fence))
    })();
    let (lease, fence) = match direct {
        Ok(pair) => pair,
        Err(_) => {
            let (cpu, fences) = jobserver_utils::recover_cpu_resources(&required(
                jobserver_utils::CPU_HANDOFF_ENV,
            )?)?;
            (
                pool.adopt_inherited_until(
                    &File::from(cpu),
                    std::time::Instant::now() + Duration::from_secs(1),
                )?,
                LegacyFence::from_inherited(
                    &directory,
                    slots,
                    fences.into_iter().map(File::from).collect(),
                )?,
            )
        }
    };
    let lease = Arc::new(lease);
    let fence = Arc::new(fence);
    let owner = trust_build_cpu::process_cpu::read(std::process::id())
        .ok_or_else(|| io::Error::other("native worker process birth is unavailable"))?
        .owner;
    lease.report_owner(owner)?;
    let usage = Arc::new(NativeUsage::new(pool.clone())?);
    let monitor = std::env::var_os("PATH")
        .and_then(|path| {
            std::env::split_paths(&path).map(|dir| dir.join("aterm")).find(|path| path.is_file())
        })
        .and_then(|program| {
            Monitor::spawn(program, Duration::from_secs(1), Duration::from_secs(1)).ok()
        })
        .map(Arc::new);
    let number = |name: &str, default: u64| -> io::Result<u64> {
        std::env::var_os(name).map_or(Ok(default), |raw| {
            raw.to_str()
                .and_then(|raw| raw.parse::<u64>().ok())
                .ok_or_else(|| io::Error::other(format!("invalid {name}")))
        })
    };
    let per_worker = NonZeroU64::new(number("TARGO_JOB_MEMORY_BYTES", 2 << 30)?)
        .ok_or_else(|| io::Error::other("zero worker memory estimate"))?;
    let reserve = number("TARGO_MEMORY_RESERVE_BYTES", trust_build_cpu::default_memory_reserve())?;
    let memory = Arc::clone(&usage);
    let cpu_usage = Arc::clone(&usage);
    let policy = Arc::new(
        HostPolicy::new(
            pool.clone(),
            monitor,
            per_worker,
            reserve,
            Arc::new(move || memory.available_memory()),
        )
        .with_native_cpu(Arc::new(move || cpu_usage.millicores())),
    );
    let global = WorkerClient::new(
        local.clone(),
        pool,
        Arc::clone(&lease),
        Arc::new(move |held| policy.limit_for(held)),
        owner,
    )?
    .with_fence(Arc::clone(&fence));
    let handoff = Arc::new(jobserver_utils::CpuLeaseHandoff::new_bundle(
        OwnedFd::from(lease.try_clone()?.into_file()),
        fence
            .files()
            .iter()
            .map(|file| file.try_clone().map(OwnedFd::from))
            .collect::<io::Result<Vec<_>>>()?,
    )?);
    let mut client = Client::with_global(local, global);
    client.handoff = Some(handoff);
    Ok(client)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(super) fn activate(_local: jobserver_crate::Client) -> io::Result<Client> {
    Err(io::Error::other("native worker protocol is unavailable on this host"))
}
