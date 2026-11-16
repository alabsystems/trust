//! Exec-only fixture for the fixed checker thread restriction profile.
//! No solver/proof authority is constructed here. The parent owns all cleanup.
use std::os::fd::IntoRawFd;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Limits};
use trust_worker_linux::{
    KernelLimits, PinnedInput, Profile, install, install_checker_resources, install_checker_threads,
};

#[path = "checker_threads_fixture/resources.rs"]
mod resources;

static ENTERED: AtomicBool = AtomicBool::new(false);
struct Cleanup;
impl Drop for Cleanup {
    fn drop(&mut self) {
        emit(3, b"D");
    }
}
thread_local! { static CLEANUP: Cleanup = const { Cleanup }; }
fn exit(code: i32) -> ! {
    // SAFETY: this terminates the fixture's entire thread group; the parent
    // retains and reaps its unreaped leader before reporting completion.
    unsafe { libc::_exit(code) }
}
fn emit(fd: i32, bytes: &[u8]) {
    // SAFETY: live byte slice and a declared diagnostic/control descriptor.
    let count = unsafe { libc::write(fd, bytes.as_ptr().cast(), bytes.len()) };
    if count < 0 || count as usize != bytes.len() {
        exit(71);
    }
}
fn identity(text: &str) -> Option<[u8; 32]> {
    if text.len() != 64 {
        return None;
    }
    let mut result = [0; 32];
    for (index, byte) in result.iter_mut().enumerate() {
        *byte = u8::from_str_radix(text.get(index * 2..index * 2 + 2)?, 16).ok()?;
    }
    Some(result)
}
fn unavailable(result: libc::c_long) {
    if result != -1 || std::io::Error::last_os_error().raw_os_error() != Some(libc::ENOSYS) {
        exit(74);
    }
}
fn positive() {
    // SAFETY: seccomp returns ENOSYS before dereferencing the deliberately null
    // optional clone3 probe. GNU pthread_create must use the audited fallback.
    unavailable(unsafe { libc::syscall(libc::SYS_clone3, std::ptr::null::<u8>(), 0usize) });
    // SAFETY: both optional probes are intercepted before any pointer access or
    // cross-process affinity observation. No alternate permissive mode exists.
    unsafe {
        unavailable(libc::syscall(libc::SYS_prctl, 0x5356_4d41u32, 0, 0, 0, 0));
        unavailable(libc::syscall(libc::SYS_sched_getaffinity, 0, 0usize, std::ptr::null::<u8>()));
    }
    let thread = std::thread::Builder::new()
        .name("checker-fixture".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            CLEANUP.with(|_| {});
            emit(3, b"T");
            std::thread::sleep(Duration::from_millis(1));
            42
        });
    let Ok(thread) = thread else { exit(74) };
    if thread.join().ok() != Some(42) {
        exit(74);
    }
    emit(3, b"J");
    emit(1, b"PASS\n");
}
fn leader_exit() -> ! {
    let thread = std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
        emit(3, b"T");
        ENTERED.store(true, Ordering::Release);
        let mut byte = 0u8;
        // SAFETY: valid one-byte destination and admitted control socket. The
        // parent deliberately never sends input, then kills the entire group.
        loop {
            // Entry now establishes nonblocking FD3. Preserve this fixture's
            // deliberately live sibling until the outside owner kills it.
            // SAFETY: initialized byte storage and the retained control slot.
            let n = unsafe { libc::read(3, (&mut byte as *mut u8).cast(), 1) };
            if n >= 0 || std::io::Error::last_os_error().raw_os_error() != Some(libc::EAGAIN) {
                exit(74)
            }
            let mut poll = libc::pollfd { fd: 3, events: libc::POLLIN, revents: 0 };
            // SAFETY: one initialized writable record. This deliberately hung
            // negative fixture waits until its outside owner kills the group.
            unsafe { libc::ppoll(&mut poll, 1, std::ptr::null(), std::ptr::null()) };
        }
    });
    let Ok(thread) = thread else { exit(74) };
    drop(thread);
    while !ENTERED.load(Ordering::Acquire) {
        std::thread::yield_now();
    }
    emit(3, b"L");
    // SAFETY: raw Linux exit terminates only this calling leader, deliberately
    // leaving the other fixture thread alive. It cannot execute caller code.
    unsafe { libc::syscall(libc::SYS_exit, 0) };
    exit(75)
}
fn forbidden(mode: &str) {
    let pthread_flags = libc::CLONE_VM
        | libc::CLONE_FS
        | libc::CLONE_FILES
        | libc::CLONE_SIGHAND
        | libc::CLONE_THREAD
        | libc::CLONE_SYSVSEM
        | libc::CLONE_SETTLS
        | libc::CLONE_PARENT_SETTID
        | libc::CLONE_CHILD_CLEARTID;
    let clone_flags = match mode {
        "clone-process" => Some(libc::SIGCHLD as u64),
        "clone-vfork" => Some((libc::CLONE_VM | libc::CLONE_VFORK | libc::SIGCHLD) as u64),
        "clone-untraced" => Some((pthread_flags | libc::CLONE_UNTRACED) as u64),
        "clone-pidfd" => Some((pthread_flags | libc::CLONE_PIDFD) as u64),
        "clone-newuser" => Some((pthread_flags | libc::CLONE_NEWUSER) as u64),
        "clone-newns" => Some((pthread_flags | libc::CLONE_NEWNS) as u64),
        "clone-missing-vm" => Some((pthread_flags & !libc::CLONE_VM) as u64),
        "clone-signal" => Some((pthread_flags | libc::SIGCHLD) as u64),
        "clone-high" => Some(pthread_flags as u64 | (1u64 << 32)),
        _ => None,
    };
    if let Some(flags) = clone_flags {
        // SAFETY: forbidden flags must be killed before kernel use of null
        // argument pointers. A broken filter is observable as non-SIGSYS.
        unsafe { libc::syscall(libc::SYS_clone, flags, 0usize, 0usize, 0usize, 0usize) };
        exit(75);
    }
    match mode {
        "strict-thread" => {
            let _ = std::thread::Builder::new().spawn(|| ());
        }
        "signal-peer" => {
            // SAFETY: forbidden scalar syscall; no unrelated PID is targeted.
            unsafe { libc::syscall(libc::SYS_tgkill, libc::getpid(), libc::gettid(), 0) };
        }
        "shared-wake" => {
            let word = 0u32;
            // SAFETY: readable aligned local word; shared wake is disallowed.
            unsafe { libc::syscall(libc::SYS_futex, &word, libc::FUTEX_WAKE, 1) };
        }
        "robust-shape" => {
            // SAFETY: the rejected size is inspected before the null pointer.
            unsafe { libc::syscall(libc::SYS_set_robust_list, 0usize, 32usize) };
        }
        "rseq-shape" => {
            // SAFETY: the rejected length is inspected before the null pointer.
            unsafe { libc::syscall(libc::SYS_rseq, 0usize, 64u32, 0u32, 0u32) };
        }
        "privilege" => {
            // SAFETY: scalar self request; no privilege relaxation is admitted.
            unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 1, 0, 0, 0) };
        }
        "exec" => {
            // SAFETY: valid path and argv; the profile denies before execution.
            unsafe {
                libc::execl(
                    c"/bin/true".as_ptr(),
                    c"true".as_ptr(),
                    std::ptr::null::<libc::c_char>(),
                );
            }
        }
        _ => exit(70),
    }
    exit(75)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 5 {
        exit(70);
    }
    let Some(hash) = identity(&args[3]) else { exit(70) };
    let Ok(parent) = args[2].parse::<i32>() else { exit(70) };
    if args[1].starts_with("resource-") {
        resources::prepare();
    }
    let Ok(canary) = std::fs::File::open(&args[4]) else { exit(70) };
    let discarded = canary.into_raw_fd();
    let limits = Limits {
        frame_bytes: 65536,
        wire_bytes: 1_000_000,
        allocation_bytes: 1_000_000,
        values: 10000,
        work: 100_000_000,
        calls: 100,
        live_handles: 64,
        depth: 16,
    };
    let Ok(budget) = Budget::new(limits, Instant::now() + Duration::from_secs(10)) else {
        exit(70)
    };
    let inputs = [PinnedInput { fd: 5, sha256: hash, size: 4096, executable: true }];
    let profile = Profile {
        parent_pid: parent,
        inputs: &inputs,
        limits: KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 64,
        },
    };
    if args[1] == "cancelled" {
        budget.cancel();
    }
    let result = if args[1] == "strict-thread" {
        install(&profile, &budget)
    } else if args[1].starts_with("resource-") {
        install_checker_resources(&profile, &budget)
    } else {
        install_checker_threads(&profile, &budget)
    };
    if let Err(error) = result {
        emit(2, format!("REFUSED: {error}\n").as_bytes());
        exit(72);
    }
    emit(1, b"INSTALLED\n");
    // SAFETY: F_GETFD only observes this descriptor discarded at installation.
    if unsafe { libc::fcntl(discarded, libc::F_GETFD) } >= 0 {
        exit(73);
    }
    match args[1].as_str() {
        "positive" => positive(),
        "leader-exit" => leader_exit(),
        "as-limit" => {
            if let Ok(thread) =
                std::thread::Builder::new().stack_size(512 * 1024 * 1024).spawn(|| ())
            {
                let _ = thread.join();
                exit(74);
            }
            emit(1, b"AS-REFUSED\n");
        }
        mode if mode.starts_with("resource-") => resources::run(mode),
        mode => forbidden(mode),
    }
    exit(0)
}
