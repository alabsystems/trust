//! Exec-fixture setup and raw kernel controls for the fixed live-resource role.
//! Setup is trusted, after exec and before the irreversible restriction profile.
use std::sync::atomic::{AtomicUsize, Ordering};

use super::{emit, exit};

static PAGE: AtomicUsize = AtomicUsize::new(0);

pub(super) fn prepare() {
    // The trusted parent fixture opens child statm before exec and passes it at
    // FD6, so the positive control also checks that it follows the new mm. FD7
    // is inherited kernel meminfo. Production role checks authenticate both.
    // SAFETY: trusted startup queries a scalar constant before the filter.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    let Ok(page) = usize::try_from(page) else { exit(70) };
    if page == 0 {
        exit(70);
    }
    PAGE.store(page, Ordering::Relaxed);
}

fn read<const N: usize>(fd: i32, output: &mut [u8; N]) -> usize {
    // SAFETY: complete writable fixed-size buffer and authenticated read-only
    // fixed resource descriptor; pread leaves the shared cursor unchanged.
    let n = unsafe { libc::pread(fd, output.as_mut_ptr().cast(), N, 0) };
    let Ok(n) = usize::try_from(n) else { exit(74) };
    if n == 0 || n >= N {
        exit(74);
    }
    n
}

fn resident_bytes() -> usize {
    let mut output = [0u8; 256];
    let n = read(6, &mut output);
    let Ok(text) = std::str::from_utf8(&output[..n]) else { exit(74) };
    let Some(resident) = text.split_ascii_whitespace().nth(1) else { exit(74) };
    let Ok(resident) = resident.parse::<usize>() else { exit(74) };
    let Some(bytes) = resident.checked_mul(PAGE.load(Ordering::Relaxed)) else { exit(74) };
    bytes
}

fn positive() {
    let before = resident_bytes();
    let mut allocation = vec![0u8; 32 * 1024 * 1024];
    let page = PAGE.load(Ordering::Relaxed);
    for offset in (0..allocation.len()).step_by(page) {
        // SAFETY: every offset is inside this exclusively owned allocation.
        // Volatile stores make the kernel populate actual resident pages.
        unsafe { std::ptr::write_volatile(allocation.as_mut_ptr().add(offset), 1) };
    }
    std::hint::black_box(&allocation);
    let after = resident_bytes();
    if after.saturating_sub(before) < 16 * 1024 * 1024 {
        exit(74);
    }
    let mut output = [0u8; 8192];
    let n = read(7, &mut output);
    let Ok(text) = std::str::from_utf8(&output[..n]) else { exit(74) };
    if !text.lines().any(|line| line.starts_with("MemAvailable:")) {
        exit(74);
    }
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
    // SAFETY: exact admitted self query and complete writable rusage output.
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) } != 0 {
        exit(74);
    }
    let thread = std::thread::Builder::new()
        .name("resource-reader".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(resident_bytes);
    let Ok(thread) = thread else { exit(74) };
    if !matches!(thread.join(), Ok(bytes) if bytes.saturating_sub(before) >= 16 * 1024 * 1024) {
        exit(74);
    }
    drop(allocation);
    emit(1, b"LIVE-RESOURCES\n");
}

pub(super) fn run(mode: &str) {
    if mode == "resource-positive" {
        positive();
        return;
    }
    let mut bytes = [0u8; 8193];
    match mode {
        "resource-read" => {
            // SAFETY: valid writable output; this non-pread operation must die.
            unsafe { libc::read(6, bytes.as_mut_ptr().cast(), 1) };
        }
        "resource-write" => {
            // SAFETY: readable byte input; fixed kernel resources are not writable.
            unsafe { libc::write(6, bytes.as_ptr().cast(), 1) };
        }
        "resource-close" => {
            // SAFETY: a fixture-owned descriptor; the profile must protect it.
            unsafe { libc::close(6) };
        }
        "resource-seek" => {
            // SAFETY: scalar request, deliberately forbidden shared-cursor change.
            unsafe { libc::lseek(6, 0, libc::SEEK_SET) };
        }
        "resource-large" | "resource-offset" => {
            let (size, offset) = if mode == "resource-large" { (8193, 0) } else { (1, 1) };
            // SAFETY: buffer covers requested size; the scalar length/offset is
            // rejected before any read, without relying on an invalid pointer.
            unsafe { libc::pread(7, bytes.as_mut_ptr().cast(), size, offset) };
        }
        "resource-map" => {
            // SAFETY: valid scalar mmap request for a protected readonly FD;
            // no pointer is dereferenced and the filter must deny it first.
            unsafe {
                libc::mmap(std::ptr::null_mut(), 4096, libc::PROT_READ, libc::MAP_PRIVATE, 6, 0)
            };
        }
        "resource-dup" => {
            // SAFETY: deliberate forbidden duplication of fixture-owned FD.
            unsafe { libc::fcntl(6, libc::F_DUPFD_CLOEXEC, 8) };
        }
        "resource-open" => {
            // SAFETY: valid fixed pathname; ambient opens remain disallowed.
            unsafe { libc::open(c"/proc/self/statm".as_ptr(), libc::O_RDONLY) };
        }
        "resource-children" => {
            let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
            // SAFETY: valid output; only RUSAGE_SELF is admitted, not children.
            unsafe { libc::getrusage(libc::RUSAGE_CHILDREN, usage.as_mut_ptr()) };
        }
        _ => exit(70),
    }
    exit(75)
}
