use std::io;

use super::Host;

pub(super) fn measure() -> io::Result<Host> {
    let cpus = std::thread::available_parallelism()?.get();
    let cpus = u32::try_from(cpus)
        .ok()
        .filter(|cpus| *cpus > 0 && *cpus <= trust_build_cpu::MAX_SLOTS)
        .ok_or_else(|| super::super::invalid("native CPU observation is outside its bound"))?;
    let total = physical_memory()?;
    if total == 0 {
        return Err(super::super::invalid("physical memory observation is unavailable"));
    }
    let available = trust_build_cpu::available_memory()
        .ok_or_else(|| super::super::invalid("native available memory is unavailable"))?;
    let mut load = [0.0_f64];
    // SAFETY: load has space for the single requested native observation.
    let count = unsafe { libc::getloadavg(load.as_mut_ptr(), 1) };
    Ok(Host {
        platform: std::env::consts::OS,
        cpus,
        physical_memory_bytes: total,
        available_memory_bytes: available.min(total),
        available_memory_source: "native_conservative_available_memory",
        load_one: (count == 1 && load[0].is_finite() && load[0] >= 0.0).then_some(load[0]),
    })
}

#[cfg(target_os = "macos")]
fn physical_memory() -> io::Result<u64> {
    let mut bytes = 0_u64;
    let mut length = std::mem::size_of_val(&bytes);
    // SAFETY: constant readonly sysctl, exact writable u64 and size storage.
    let result = unsafe {
        libc::sysctlbyname(
            c"hw.memsize".as_ptr(),
            (&raw mut bytes).cast(),
            &raw mut length,
            std::ptr::null_mut(),
            0,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    if length != std::mem::size_of_val(&bytes) || bytes == 0 {
        return Err(super::super::invalid("native physical-memory response is incomplete"));
    }
    Ok(bytes)
}

#[cfg(target_os = "linux")]
fn physical_memory() -> io::Result<u64> {
    use std::io::Read;
    let file = std::fs::File::open("/proc/meminfo")?;
    let mut text = String::new();
    file.take(65_537).read_to_string(&mut text)?;
    if text.len() > 65_536 {
        return Err(super::super::invalid("native memory population exceeds its bound"));
    }
    physical_from_meminfo(&text)
}

#[cfg(any(target_os = "linux", test))]
pub(super) fn physical_from_meminfo(text: &str) -> io::Result<u64> {
    let mut matches = text.lines().filter_map(|line| line.strip_prefix("MemTotal:"));
    let value = matches.next().ok_or_else(|| super::super::invalid("native MemTotal is absent"))?;
    let mut words = value.split_whitespace();
    let bytes = words
        .next()
        .filter(|word| !word.is_empty() && word.bytes().all(|byte| byte.is_ascii_digit()))
        .and_then(|word| word.parse::<u64>().ok())
        .and_then(|value| value.checked_mul(1024))
        .filter(|bytes| *bytes > 0);
    if words.next() != Some("kB") || words.next().is_some() || matches.next().is_some() {
        return Err(super::super::invalid("native MemTotal is malformed"));
    }
    bytes.ok_or_else(|| super::super::invalid("native MemTotal is unavailable"))
}
