// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Conservative raw kernel memory availability. This is not a reservation.

/// Read memory available to this process without spawning a command.
///
/// macOS counts free, speculative and purgeable pages only. Linux uses
/// MemAvailable, capped by each readable applicable cgroup memory constraint.
/// Missing or malformed required observations produce no estimate.
pub fn available_memory() -> Option<u64> {
    #[cfg(target_os = "macos")]
    return macos();
    #[cfg(target_os = "linux")]
    return linux(&read_optional);
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    None
}

/// Choose a default reserve from the conservative startup reading. Explicit
/// caller reserves remain exact. This estimates a margin, never free capacity;
/// admission still requires its own current memory observation.
pub fn default_memory_reserve() -> u64 {
    reserve_from_available(available_memory())
}

fn reserve_from_available(available: Option<u64>) -> u64 {
    const FLOOR: u64 = 256 * 1024 * 1024;
    const CEILING: u64 = 8 * 1024 * 1024 * 1024;
    available.map_or(FLOOR, |bytes| (bytes / 8).clamp(FLOOR, CEILING))
}

#[cfg(any(target_os = "macos", test))]
fn available_pages(free: u64, speculative: u64, purgeable: u64, page_size: u64) -> Option<u64> {
    if page_size == 0 {
        return None;
    }
    free.checked_add(speculative)?.checked_add(purgeable)?.checked_mul(page_size)
}

#[cfg(target_os = "macos")]
fn macos() -> Option<u64> {
    unsafe extern "C" {
        fn mach_host_self() -> libc::mach_port_t;
        static mach_task_self_: libc::mach_port_t;
        fn mach_port_deallocate(
            task: libc::mach_port_t,
            port: libc::mach_port_t,
        ) -> libc::kern_return_t;
    }
    struct HostPort(libc::mach_port_t);
    impl Drop for HostPort {
        fn drop(&mut self) {
            // SAFETY: this guard owns the send right returned by mach_host_self.
            // Deallocate that one right in this task, including on early returns.
            unsafe { mach_port_deallocate(mach_task_self_, self.0) };
        }
    }
    // SAFETY: these calls read the current task's host port and page-size constant.
    let (port, page_size) = unsafe { (mach_host_self(), libc::sysconf(libc::_SC_PAGESIZE)) };
    if port == 0 || page_size <= 0 {
        if port != 0 {
            drop(HostPort(port));
        }
        return None;
    }
    let port = HostPort(port);
    // SAFETY: vm_statistics64 consists of integer fields for which zero is valid.
    let mut vm: libc::vm_statistics64 = unsafe { std::mem::zeroed() };
    let mut count = libc::HOST_VM_INFO64_COUNT;
    // SAFETY: vm has space for exactly HOST_VM_INFO64_COUNT integer words; count
    // points to the corresponding writable count. The host send right is live.
    let result = unsafe {
        libc::host_statistics64(
            port.0,
            libc::HOST_VM_INFO64,
            (&raw mut vm).cast::<libc::integer_t>(),
            &raw mut count,
        )
    };
    if result != 0 || count < libc::HOST_VM_INFO64_COUNT {
        return None;
    }
    available_pages(
        u64::from(vm.free_count),
        u64::from(vm.speculative_count),
        u64::from(vm.purgeable_count),
        page_size as u64,
    )
}

#[cfg(any(target_os = "linux", test))]
use std::path::{Component, Path, PathBuf};

#[cfg(target_os = "linux")]
fn read_optional(path: &Path) -> Option<Option<String>> {
    use std::io::Read;
    let file = match std::fs::File::open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Some(None),
        Err(_) => return None,
    };
    let mut text = String::new();
    file.take(65_537).read_to_string(&mut text).ok()?;
    (text.len() <= 65_536).then_some(Some(text))
}

#[cfg(any(target_os = "linux", test))]
fn mem_available(text: &str) -> Option<u64> {
    let mut available = None;
    for line in text.lines().filter_map(|line| line.strip_prefix("MemAvailable:")) {
        if available.is_some() {
            return None;
        }
        let mut words = line.split_whitespace();
        let amount = decimal(words.next()?)?;
        if words.next()? != "kB" || words.next().is_some() {
            return None;
        }
        available = Some(amount.checked_mul(1024)?);
    }
    available
}

#[cfg(any(target_os = "linux", test))]
fn decimal(text: &str) -> Option<u64> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

#[cfg(any(target_os = "linux", test))]
fn absolute(text: &str) -> Option<PathBuf> {
    let bytes = text.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut at = 0;
    while at < bytes.len() {
        if bytes[at] == b'\\' {
            let escape = bytes.get(at + 1..at + 4)?;
            decoded.push(match escape {
                b"040" => b' ',
                b"011" => b'\t',
                b"012" => b'\n',
                b"134" => b'\\',
                _ => return None,
            });
            at += 4;
        } else {
            decoded.push(bytes[at]);
            at += 1;
        }
    }
    let path = PathBuf::from(String::from_utf8(decoded).ok()?);
    (path.is_absolute()
        && path.components().all(|part| matches!(part, Component::RootDir | Component::Normal(_))))
    .then_some(path)
}

#[cfg(any(target_os = "linux", test))]
fn linux(read: &impl Fn(&Path) -> Option<Option<String>>) -> Option<u64> {
    let mut available = mem_available(&read(Path::new("/proc/meminfo"))??)?;
    let groups = read(Path::new("/proc/self/cgroup"))??;
    let mounts = read(Path::new("/proc/self/mountinfo"))??;
    for line in groups.lines() {
        let mut words = line.splitn(3, ':');
        let hierarchy = words.next()?;
        let controllers = words.next()?;
        let group = words.next()?;
        let unified = hierarchy == "0" && controllers.is_empty();
        if !unified && !controllers.split(',').any(|name| name == "memory") {
            continue;
        }
        let group = absolute(group)?;
        let (mount, directory) = locate(&mounts, &group, unified)?;
        available = available.min(cgroup_remaining(read, &mount, &directory, unified)?);
    }
    Some(available)
}

#[cfg(any(target_os = "linux", test))]
fn locate(mounts: &str, group: &Path, unified: bool) -> Option<(PathBuf, PathBuf)> {
    let mut selected: Option<(usize, PathBuf, PathBuf)> = None;
    for line in mounts.lines() {
        let (before, after) = line.split_once(" - ")?;
        let mut kind = after.split_whitespace();
        let filesystem = kind.next()?;
        let _source = kind.next()?;
        let options = kind.next()?;
        if if unified {
            filesystem != "cgroup2"
        } else {
            filesystem != "cgroup" || !options.split(',').any(|name| name == "memory")
        } {
            continue;
        }
        let fields: Vec<_> = before.split_whitespace().collect();
        let root = absolute(fields.get(3)?)?;
        let mount = absolute(fields.get(4)?)?;
        if let Ok(relative) = group.strip_prefix(&root) {
            let depth = root.components().count();
            if selected.as_ref().is_none_or(|(old, _, _)| depth > *old) {
                selected = Some((depth, mount.clone(), mount.join(relative)));
            }
        }
    }
    selected.map(|(_, mount, directory)| (mount, directory))
}

#[cfg(any(target_os = "linux", test))]
fn cgroup_remaining(
    read: &impl Fn(&Path) -> Option<Option<String>>,
    mount: &Path,
    directory: &Path,
    unified: bool,
) -> Option<u64> {
    let (maximum, current) = if unified {
        ("memory.max", "memory.current")
    } else {
        ("memory.limit_in_bytes", "memory.usage_in_bytes")
    };
    let mut remaining = u64::MAX;
    let mut at = directory;
    loop {
        match read(&at.join(maximum))? {
            Some(text) if unified && text.trim() == "max" => {}
            Some(text) => {
                let limit = decimal(text.trim())?;
                let used = decimal(read(&at.join(current))??.trim())?;
                remaining = remaining.min(limit.saturating_sub(used));
            }
            // The v2 root and groups without a memory controller have no max.
            None if unified => {}
            None => return None,
        }
        if at == mount {
            return Some(remaining);
        }
        at = at.parent()?;
        if !at.starts_with(mount) {
            return None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_os = "macos")]
    #[test]
    fn native_macos_snapshot_is_available_on_this_host() {
        assert!(available_memory().is_some());
    }

    #[test]
    fn macos_counts_only_known_reclaimable_pages_and_checks_overflow() {
        assert_eq!(available_pages(2, 3, 5, 4096), Some(40960));
        assert_eq!(available_pages(u64::MAX, 1, 0, 4096), None);
        assert_eq!(available_pages(1, 0, 0, 0), None);
    }

    #[test]
    fn linux_meminfo_requires_one_well_formed_available_measurement() {
        assert_eq!(mem_available("MemTotal: 100 kB\nMemAvailable: 12 kB\n"), Some(12288));
        for text in [
            "",
            "MemAvailable: -1 kB",
            "MemAvailable: 12 MB",
            "MemAvailable: 1 kB\nMemAvailable: 2 kB",
            "MemAvailable: 18446744073709551615 kB",
        ] {
            assert_eq!(mem_available(text), None, "{text}");
        }
    }

    fn fixture(unified: bool) -> std::collections::HashMap<PathBuf, String> {
        [
            ("/proc/meminfo", "MemAvailable: 100 kB"),
            (
                "/proc/self/cgroup",
                if unified { "0::/tenant/leaf" } else { "5:cpu,memory:/tenant/leaf" },
            ),
            (
                "/proc/self/mountinfo",
                if unified {
                    "1 2 0:3 / /cg rw - cgroup2 cgroup rw"
                } else {
                    "1 2 0:3 /tenant /cg rw - cgroup cgroup rw,memory"
                },
            ),
        ]
        .into_iter()
        .map(|(path, text)| (PathBuf::from(path), text.to_owned()))
        .collect()
    }

    #[test]
    fn unified_limit_includes_more_restrictive_ancestor_and_refuses_corruption() {
        let mut files = fixture(true);
        for (path, text) in [
            ("/cg/tenant/leaf/memory.max", "90000"),
            ("/cg/tenant/leaf/memory.current", "10000"),
            ("/cg/tenant/memory.max", "40000"),
            ("/cg/tenant/memory.current", "30000"),
        ] {
            files.insert(path.into(), text.into());
        }
        assert_eq!(linux(&|path| Some(files.get(path).cloned())), Some(10000));
        files.insert("/cg/tenant/memory.max".into(), "unknown".into());
        assert_eq!(linux(&|path| Some(files.get(path).cloned())), None);
    }

    #[test]
    fn legacy_mount_root_is_resolved_and_missing_required_usage_is_unknown() {
        let mut files = fixture(false);
        for (path, text) in [
            ("/cg/leaf/memory.limit_in_bytes", "90000"),
            ("/cg/leaf/memory.usage_in_bytes", "10000"),
            ("/cg/memory.limit_in_bytes", "30000"),
            ("/cg/memory.usage_in_bytes", "20000"),
        ] {
            files.insert(path.into(), text.into());
        }
        assert_eq!(linux(&|path| Some(files.get(path).cloned())), Some(10000));
        files.remove(Path::new("/cg/memory.usage_in_bytes"));
        assert_eq!(linux(&|path| Some(files.get(path).cloned())), None);
    }

    #[test]
    fn unavailable_controller_is_not_unlimited_and_paths_cannot_escape() {
        let files = fixture(true);
        assert_eq!(
            linux(&|path| if path == Path::new("/cg/tenant/memory.max") {
                None
            } else {
                Some(files.get(path).cloned())
            }),
            None
        );
        assert_eq!(absolute("/tenant/../escape"), None);
        assert_eq!(absolute("/tenant\\040one/leaf"), Some("/tenant one/leaf".into()));
    }
}

#[cfg(test)]
mod reserve_tests {
    use super::reserve_from_available;
    #[test]
    fn startup_margin_fits_small_hosts_and_bounds_large_hosts() {
        let gib = 1024 * 1024 * 1024;
        assert_eq!(reserve_from_available(Some(6 * gib)), 3 * gib / 4);
        assert_eq!(reserve_from_available(Some(96 * gib)), 8 * gib);
        assert_eq!(reserve_from_available(Some(1024)), gib / 4);
        assert_eq!(reserve_from_available(None), gib / 4);
    }
}
