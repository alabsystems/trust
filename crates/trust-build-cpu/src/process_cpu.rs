// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Explicit-process lifetime CPU counters, with kernel process-birth identity.

/// A process identity and its own user plus system CPU time; no child-time sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProcessCpu {
    /// Kernel PID and birth identity, for detecting exit or PID reuse.
    pub owner: crate::Owner,
    /// Cumulative CPU nanoseconds, never a sampled utilization estimate.
    pub total_ns: u64,
}

/// Read one same-user process without spawning commands or enumerating the host.
/// Unknown, inaccessible, foreign or malformed process information returns none.
pub fn read(pid: u32) -> Option<ProcessCpu> {
    if pid == 0 || pid > i32::MAX as u32 {
        return None;
    }
    #[cfg(target_os = "macos")]
    return macos(pid);
    #[cfg(target_os = "linux")]
    return linux(pid);
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    None
}

fn nanoseconds(user: u64, system: u64, numerator: u64, denominator: u64) -> Option<u64> {
    if numerator == 0 || denominator == 0 {
        return None;
    }
    let ticks = user.checked_add(system)?;
    u64::try_from(u128::from(ticks).checked_mul(u128::from(numerator))? / u128::from(denominator))
        .ok()
}

#[cfg(target_os = "macos")]
fn kernel_timebase() -> Option<(u64, u64)> {
    #[repr(C)]
    struct MachTimebase {
        numer: u32,
        denom: u32,
    }
    unsafe extern "C" {
        fn mach_timebase_info(info: *mut MachTimebase) -> libc::kern_return_t;
    }
    static BASIS: std::sync::OnceLock<Option<(u64, u64)>> = std::sync::OnceLock::new();
    *BASIS.get_or_init(|| {
        let mut hz = 0u64;
        let mut length = std::mem::size_of_val(&hz);
        // SAFETY: the sysctl has a constant NUL-terminated name, writable u64
        // storage and a correct size pointer; null new-value arguments only read.
        let result = unsafe {
            libc::sysctlbyname(
                c"hw.tbfrequency".as_ptr(),
                (&raw mut hz).cast(),
                &raw mut length,
                std::ptr::null_mut(),
                0,
            )
        };
        if result == 0 && matches!(length, 4 | 8) && hz != 0 {
            return Some((1_000_000_000, hz));
        }
        // Kernel counters retain the hardware tick frequency under Rosetta;
        // use the process-local Mach timebase only when that frequency is absent.
        let mut basis = MachTimebase { numer: 0, denom: 0 };
        // SAFETY: basis is writable storage for the complete timebase result.
        let result = unsafe { mach_timebase_info(&raw mut basis) };
        (result == 0 && basis.numer != 0 && basis.denom != 0)
            .then_some((u64::from(basis.numer), u64::from(basis.denom)))
    })
}

#[cfg(target_os = "macos")]
fn bsd_identity(pid: u32) -> Option<(u64, u64)> {
    // SAFETY: all-zero is valid for this integer/array ABI record.
    let mut info: libc::proc_bsdinfo = unsafe { std::mem::zeroed() };
    // SAFETY: pid was range-checked; info has exactly the size passed, and the
    // selected read-only flavor writes a proc_bsdinfo record.
    let count = unsafe {
        libc::proc_pidinfo(
            pid as i32,
            libc::PROC_PIDTBSDINFO,
            0,
            (&raw mut info).cast(),
            std::mem::size_of_val(&info) as i32,
        )
    };
    // SAFETY: geteuid reads this process's effective user identity.
    if count != std::mem::size_of_val(&info) as i32 || info.pbi_uid != unsafe { libc::geteuid() } {
        return None;
    }
    Some((info.pbi_start_tvsec, info.pbi_start_tvusec))
}

#[cfg(target_os = "macos")]
fn macos(pid: u32) -> Option<ProcessCpu> {
    let identity = bsd_identity(pid)?;
    // SAFETY: the ABI record consists of integer/array fields valid when zero.
    let mut usage: libc::rusage_info_v4 = unsafe { std::mem::zeroed() };
    // SAFETY: usage has space for the selected RUSAGE_INFO_V4 ABI record.
    let result =
        unsafe { libc::proc_pid_rusage(pid as i32, libc::RUSAGE_INFO_V4, (&raw mut usage).cast()) };
    if result != 0 || usage.ri_proc_start_abstime == 0 || bsd_identity(pid)? != identity {
        return None;
    }
    let (numerator, denominator) = kernel_timebase()?;
    Some(ProcessCpu {
        owner: crate::Owner { pid, birth: Some(usage.ri_proc_start_abstime) },
        total_ns: nanoseconds(usage.ri_user_time, usage.ri_system_time, numerator, denominator)?,
    })
}

#[cfg(target_os = "linux")]
fn linux(pid: u32) -> Option<ProcessCpu> {
    use std::io::Read;
    use std::os::fd::{AsRawFd, FromRawFd};
    use std::os::unix::fs::MetadataExt;
    let directory = std::fs::File::open(format!("/proc/{pid}")).ok()?;
    // SAFETY: geteuid only reads this process's user ID.
    let uid = unsafe { libc::geteuid() };
    if directory.metadata().ok()?.uid() != uid {
        return None;
    }
    // SAFETY: directory is live; the fixed leaf has no traversal. A successful
    // open returns a new descriptor which is taken into File exactly once.
    let raw = unsafe {
        libc::openat(
            directory.as_raw_fd(),
            c"stat".as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        )
    };
    if raw < 0 {
        return None;
    }
    // SAFETY: raw is the successful openat's newly owned descriptor.
    let mut file = unsafe { std::fs::File::from_raw_fd(raw) };
    let mut text = String::new();
    Read::by_ref(&mut file).take(16_385).read_to_string(&mut text).ok()?;
    if text.len() > 16_384 || directory.metadata().ok()?.uid() != uid {
        return None;
    }
    // SAFETY: sysconf reads the fixed kernel clock-tick parameter.
    let hz = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
    linux_stat(pid, &text, u64::try_from(hz).ok()?)
}

#[cfg(any(target_os = "linux", test))]
fn linux_stat(pid: u32, text: &str, hz: u64) -> Option<ProcessCpu> {
    let (head, tail) = text.rsplit_once(')')?;
    let (record_pid, _comm) = head.split_once(" (")?;
    if record_pid.parse::<u32>().ok()? != pid {
        return None;
    }
    let fields: Vec<_> = tail.split_whitespace().collect();
    if fields.first()?.len() != 1 {
        return None;
    }
    let number = |at: usize| -> Option<u64> {
        let value = *fields.get(at)?;
        if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        value.parse().ok()
    };
    Some(ProcessCpu {
        owner: crate::Owner { pid, birth: Some(number(19)?) },
        total_ns: nanoseconds(number(11)?, number(12)?, 1_000_000_000, hz)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kernel_ticks_use_the_hardware_frequency_and_checked_arithmetic() {
        assert_eq!(
            nanoseconds(24_000_000, 12_000_000, 1_000_000_000, 24_000_000),
            Some(1_500_000_000)
        );
        assert_eq!(nanoseconds(u64::MAX, 1, 1, 1), None);
        assert_eq!(nanoseconds(u64::MAX, 0, 2, 1), None);
        assert_eq!(nanoseconds(1, 0, 1, 0), None);
    }

    #[test]
    fn linux_stat_handles_comm_spaces_parentheses_and_rejects_bad_counters() {
        let mut fields = vec!["0"; 20];
        fields[0] = "R";
        fields[11] = "125";
        fields[12] = "25";
        fields[19] = "456";
        let record = format!("123 (name (with) spaces)) {}", fields.join(" "));
        let reading = linux_stat(123, &record, 100).unwrap();
        assert_eq!(reading.owner, crate::Owner { pid: 123, birth: Some(456) });
        assert_eq!(reading.total_ns, 1_500_000_000);
        assert!(linux_stat(124, &record, 100).is_none());
        assert!(linux_stat(123, &record, 0).is_none());
        fields[12] = "-1";
        assert!(linux_stat(123, &format!("123 (name) {}", fields.join(" ")), 100).is_none());
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn own_process_has_stable_birth_and_monotonic_lifetime_cpu() {
        let pid = std::process::id();
        let before = read(pid).unwrap();
        let after = read(pid).unwrap();
        assert_eq!(before.owner, after.owner);
        assert!(after.owner.birth.is_some());
        assert!(after.total_ns >= before.total_ns);
        assert!(read(0).is_none());
        assert!(read(u32::MAX).is_none());
    }
}
