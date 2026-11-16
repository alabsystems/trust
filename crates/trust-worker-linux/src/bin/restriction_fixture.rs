use std::os::fd::IntoRawFd;
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Limits};
use trust_worker_linux::{KernelLimits, PinnedInput, Profile, install};

fn exit(code: i32) -> ! {
    // SAFETY: the fixture terminates its own process without running destructors
    // on retained descriptors; kernel teardown closes them atomically.
    unsafe { libc::_exit(code) }
}
fn emit(fd: i32, bytes: &[u8]) {
    // SAFETY: bytes remains readable for its length, and the fixture supplies
    // only its declared diagnostic/control descriptor to this scalar syscall.
    let n = unsafe { libc::write(fd, bytes.as_ptr().cast(), bytes.len()) };
    if n < 0 || n as usize != bytes.len() {
        exit(71);
    }
}
fn identity(text: &str) -> Option<[u8; 32]> {
    if text.len() != 64 {
        return None;
    }
    let mut result = [0; 32];
    for (index, item) in result.iter_mut().enumerate() {
        *item = u8::from_str_radix(text.get(index * 2..index * 2 + 2)?, 16).ok()?;
    }
    Some(result)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 5 {
        exit(70);
    }
    let mode = &args[1];
    let Some(hash) = identity(&args[3]) else {
        exit(70);
    };
    let Ok(parent) = args[2].parse::<i32>() else {
        exit(70);
    };
    // A known fixture canary opened by trusted startup must close before the
    // installation token is returned. Its bytes never reach the installed code.
    let Ok(canary) = std::fs::File::open(&args[4]) else {
        exit(70);
    };
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
        exit(70);
    };
    let mut inputs = [PinnedInput { fd: 5, sha256: hash, size: 4096, executable: true }; 27];
    for (index, input) in inputs.iter_mut().enumerate() {
        input.fd = 5 + index as i32;
    }
    let count = if mode == "max-inputs" { 27 } else { 1 };
    let profile = Profile {
        parent_pid: parent,
        inputs: &inputs[..count],
        limits: KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 64,
        },
    };
    if mode == "read-implies-exec" {
        // SAFETY: this trusted adversarial fixture deliberately selects the
        // personality bit that must be rejected before restrictions/loaders.
        if unsafe { libc::personality(0x0400000) } < 0 {
            exit(76);
        }
    }
    if mode == "existing-wx" {
        // SAFETY: a bounded anonymous W+X fixture map is created only before
        // admission to verify that startup rejects this existing mapping.
        let p = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                4096,
                libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        if p == libc::MAP_FAILED {
            exit(76);
        }
    }
    if let Err(error) = install(&profile, &budget) {
        emit(2, format!("REFUSED: {error}\n").as_bytes());
        exit(72);
    }
    emit(1, b"INSTALLED\n");
    // SAFETY: F_GETFD only observes whether the discarded fixture descriptor is
    // still open. The retained input and control descriptors are untouched.
    if unsafe { libc::fcntl(discarded, libc::F_GETFD) } >= 0 {
        exit(73);
    }
    match mode.as_str() {
        "positive" | "max-inputs" => {
            let mut byte = 0u8;
            // SAFETY: the one-byte destination is writable and fd5 was admitted.
            if unsafe { libc::read(5, (&mut byte as *mut u8).cast(), 1) } != 1 || byte != b'p' {
                exit(74);
            }
            // SAFETY: the admitted sealed input has at least 4096 bytes; this
            // read/execute map is never called and is released below.
            let mapped = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    4096,
                    libc::PROT_READ | libc::PROT_EXEC,
                    libc::MAP_PRIVATE,
                    5,
                    0,
                )
            };
            if mapped == libc::MAP_FAILED {
                exit(74);
            }
            // SAFETY: mapped names the exact 4096-byte region just returned.
            if unsafe { libc::munmap(mapped, 4096) } != 0 {
                exit(74);
            }
            emit(3, b"IPC-OK");
            emit(1, b"PASS\n");
        }
        "outside-read" => {
            if std::fs::File::open(&args[4]).is_ok() {
                exit(74);
            }
            emit(1, b"DENIED-OUTSIDE\n");
        }
        "procfd-output-read" | "procfd-input-reopen" | "procfd-control-reopen" => {
            let path = match mode.as_str() {
                "procfd-output-read" => c"/proc/self/fd/1",
                "procfd-input-reopen" => c"/proc/self/fd/5",
                _ => c"/proc/self/fd/3",
            };
            // SAFETY: valid constant absolute path; all ambient opens must die
            // in seccomp, including anonymous-object procfs exceptions.
            unsafe {
                libc::openat(4, path.as_ptr(), libc::O_RDONLY);
            }
            exit(75);
        }
        "input-write" => {
            // SAFETY: valid byte pointer; this operation must die in seccomp
            // before it can write to the protected read-only input descriptor.
            unsafe {
                libc::write(5, b"x".as_ptr().cast(), 1);
            }
            exit(75);
        }
        "input-close" => {
            // SAFETY: test deliberately requests a protected descriptor close;
            // seccomp must terminate the process before descriptor reuse.
            unsafe {
                libc::close(5);
            }
            exit(75);
        }
        "socket" => {
            // SAFETY: scalar valid socket request; seccomp must deny authority.
            unsafe {
                libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0);
            }
            exit(75);
        }
        "exec" => {
            // SAFETY: path and argv are valid C arrays; the syscall is forbidden
            // before kernel path resolution and cannot activate another image.
            unsafe {
                libc::execl(
                    c"/bin/true".as_ptr(),
                    c"true".as_ptr(),
                    std::ptr::null::<libc::c_char>(),
                );
            }
            exit(75);
        }
        "fork" => {
            // SAFETY: no user code or other threads exist. If the filter were
            // broken, both fixture branches terminate immediately; the parent
            // owns and reaps the whole test process group.
            unsafe {
                libc::fork();
            }
            exit(75);
        }
        "wx" => {
            // SAFETY: the anonymous mmap parameters are valid; the filter must
            // terminate before any writable executable region is created.
            unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    4096,
                    libc::PROT_WRITE | libc::PROT_EXEC,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                    -1,
                    0,
                );
            }
            exit(75);
        }
        "mprotect-exec" => {
            // SAFETY: this creates a bounded non-executable anonymous region.
            let p = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    4096,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                    -1,
                    0,
                )
            };
            if p == libc::MAP_FAILED {
                exit(74);
            }
            // SAFETY: p is the exact mapped region; granting execute is denied.
            unsafe {
                libc::mprotect(p, 4096, libc::PROT_READ | libc::PROT_EXEC);
            }
            exit(75);
        }
        "undeclared-exec" => {
            // SAFETY: well-formed mmap request on an undeclared/discarded FD;
            // seccomp must deny it before descriptor validity is considered.
            unsafe {
                libc::mmap(std::ptr::null_mut(), 4096, libc::PROT_EXEC, libc::MAP_PRIVATE, 6, 0);
            }
            exit(75);
        }
        "output-flood" => {
            let block = [b'x'; 4096];
            loop {
                emit(1, &block);
            }
        }
        "stall" => loop {
            std::hint::spin_loop();
        },
        _ => exit(70),
    }
    exit(0);
}
