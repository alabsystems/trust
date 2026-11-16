//! Trust: this host's memory, read by Targo itself.
//!
//! Test admission counts each running test executable against a budget of
//! memory (`ops::cargo_test::graph`): what is available now, less a reserve.
//! The figures are the ones the retired script lane read with `vm_stat` and
//! `sysctl`: on macOS the free, speculative, inactive and purgeable pages of
//! `host_statistics64`, on Linux `MemAvailable`.

/// Bytes of physical memory and bytes available now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostMemory {
    pub total: u64,
    pub available: u64,
}

const MIB: u64 = 1024 * 1024;

impl HostMemory {
    /// What is held back from tests: an eighth of the host, and never less
    /// than a gibibyte.
    pub fn reserve_mib(&self) -> usize {
        ((self.total / 8).max(1024 * MIB) / MIB) as usize
    }

    /// Mebibytes running test executables may be counted for together.
    pub fn test_budget_mib(&self) -> usize {
        ((self.available / MIB) as usize).saturating_sub(self.reserve_mib())
    }
}

/// Measures the host, or returns `None` where it cannot be measured.
#[cfg(target_os = "macos")]
pub fn measure() -> Option<HostMemory> {
    let mut total: u64 = 0;
    let mut len = std::mem::size_of::<u64>();
    // SAFETY: the name is a NUL-terminated string, `total` and `len` are
    // exclusively borrowed locals of the types `sysctlbyname` writes for
    // `hw.memsize`, and no new value is set.
    let read = unsafe {
        libc::sysctlbyname(
            c"hw.memsize".as_ptr(),
            std::ptr::addr_of_mut!(total).cast::<libc::c_void>(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if read != 0 || total == 0 {
        return None;
    }
    // SAFETY: `stats` is a zeroed `vm_statistics64` of `count` integers, the
    // layout `host_statistics64` fills for `HOST_VM_INFO64`; both are
    // exclusively borrowed locals. `mach_host_self` returns a send right
    // the task already holds.
    let (stats, page) = unsafe {
        let mut stats: libc::vm_statistics64 = std::mem::zeroed();
        let mut count = libc::HOST_VM_INFO64_COUNT;
        #[allow(deprecated)]
        let host = libc::mach_host_self();
        let read = libc::host_statistics64(
            host,
            libc::HOST_VM_INFO64,
            std::ptr::addr_of_mut!(stats).cast(),
            &raw mut count,
        );
        if read != libc::KERN_SUCCESS {
            return None;
        }
        (stats, libc::sysconf(libc::_SC_PAGESIZE))
    };
    if page <= 0 {
        return None;
    }
    let pages = u64::from(stats.free_count)
        + u64::from(stats.speculative_count)
        + u64::from(stats.inactive_count)
        + u64::from(stats.purgeable_count);
    Some(HostMemory {
        total,
        available: pages.saturating_mul(page as u64),
    })
}

#[cfg(target_os = "linux")]
pub fn measure() -> Option<HostMemory> {
    parse_meminfo(&std::fs::read_to_string("/proc/meminfo").ok()?)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn measure() -> Option<HostMemory> {
    None
}

/// `MemTotal` and `MemAvailable` of `/proc/meminfo`, which are in kibibytes.
#[cfg_attr(not(any(target_os = "linux", test)), allow(dead_code))]
fn parse_meminfo(text: &str) -> Option<HostMemory> {
    let field = |name: &str| {
        text.lines()
            .find_map(|line| line.strip_prefix(name)?.strip_prefix(':'))?
            .trim()
            .strip_suffix("kB")?
            .trim()
            .parse::<u64>()
            .ok()
            .map(|kib| kib * 1024)
    };
    Some(HostMemory {
        total: field("MemTotal")?,
        available: field("MemAvailable")?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_budget_is_what_is_available_less_an_eighth_of_the_host() {
        let gib = 1024 * MIB;
        let host = HostMemory {
            total: 128 * gib,
            available: 80 * gib,
        };
        assert_eq!(host.reserve_mib(), 16 * 1024);
        assert_eq!(host.test_budget_mib(), 64 * 1024);
        // A small host keeps a gibibyte, and a full one has no budget.
        let small = HostMemory {
            total: 4 * gib,
            available: gib / 2,
        };
        assert_eq!(small.reserve_mib(), 1024);
        assert_eq!(small.test_budget_mib(), 0);
    }

    #[test]
    fn meminfo_is_read_in_kibibytes() {
        let text = "MemTotal:       16000000 kB\nMemFree:  1 kB\nMemAvailable:    8000000 kB\n";
        assert_eq!(
            parse_meminfo(text),
            Some(HostMemory {
                total: 16_000_000 * 1024,
                available: 8_000_000 * 1024,
            })
        );
        assert_eq!(parse_meminfo("MemTotal: 1 kB\n"), None);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn this_host_is_measured() {
        let host = measure().expect("this host's memory can be read");
        assert!(host.total >= 1024 * MIB, "{host:?}");
        assert!(host.available > 0 && host.available <= host.total, "{host:?}");
    }
}
