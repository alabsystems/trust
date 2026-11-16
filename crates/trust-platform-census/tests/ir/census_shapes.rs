#![crate_type = "lib"]
// Census C0 fixture shapes (design 2026-10-01 §2.7): the measurement's
// repro/constructs.rs bodies (aterm's raw-fork strip, pre_exec strip) with
// callers that fix the strip bound, plus the refusal shapes.
use std::os::unix::process::CommandExt;
use std::process::Command;

#[derive(Clone, Copy)]
pub struct Strip {
    bound: i32,
}

// constructs.rs c13_fork, verbatim body: raw fork, the child strips 3..bound with
// a `while`, then execv; _exit(127) if execv returns.
fn fork_strip_exec(
    strip: Strip,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < strip.bound {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// aterm ad35a5d85 `inherited_fd_ceiling`'s CAP: the strip stops at 65 536.
pub fn spawn_capped(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: 1 << 16 }, path, argv)
}

// Every number a descriptor can have.
pub fn spawn_full(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

fn ceiling() -> i32 {
    1 << 16
}

// The bound from a local helper (inlined by the census).
pub fn spawn_ceiling(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: ceiling() }, path, argv)
}

// The bound from sysconf(_SC_OPEN_MAX = 5 on Darwin): an unmodeled call, and a truncating cast.
pub fn spawn_sysconf(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let bound = unsafe { libc::sysconf(5) } as i32;
    fork_strip_exec(Strip { bound }, path, argv)
}

// The child calls a function the platform model names as a gap.
pub fn spawn_setsid(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        unsafe {
            libc::setsid();
        }
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// constructs.rs c3_pre_exec, verbatim closure: a pre_exec strip over 3..bound.
fn install(cmd: &mut Command, strip: Strip) {
    unsafe {
        cmd.pre_exec(move || {
            for fd in 3..strip.bound {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            Ok(())
        });
    }
}

pub fn hook_capped(cmd: &mut Command) {
    install(cmd, Strip { bound: 1 << 16 })
}
pub fn hook_full(cmd: &mut Command) {
    install(cmd, Strip { bound: i32::MAX })
}

// An fd operand the root does not know (an `i32` parameter).
pub fn spawn_close_param(
    fd: i32,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    unsafe {
        libc::close(fd);
    }
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// A non-constant fcntl command.
pub fn spawn_fcntl_cmd(
    cmd: i32,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    unsafe {
        libc::fcntl(3, cmd, 1);
    }
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// A recursive helper on a spawning root's path.
fn depth(n: i32) -> i32 {
    if n > 0 { depth(n - 1) } else { 3 }
}
pub fn spawn_recursive(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: depth(4) }, path, argv)
}

// A std function outside the std table on a spawning root's path.
pub fn spawn_after_id(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let me = std::process::id();
    if me == 0 {
        return -1;
    }
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// A non-std upstream function (libc's Rust `const fn`).
pub fn spawn_upstream(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = fork_strip_exec(Strip { bound: i32::MAX }, path, argv);
    libc::WEXITSTATUS(pid)
}

// An indirect call to fork.
pub fn spawn_indirect() -> i32 {
    let f: unsafe extern "C" fn() -> libc::pid_t = libc::fork;
    unsafe { f() }
}

// The full strip with its own fork site (no other root reaches it).
pub fn spawn_full_inline(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// The full pre_exec strip with its own registration site.
pub fn hook_full_inline(cmd: &mut Command) {
    let bound = i32::MAX;
    unsafe {
        cmd.pre_exec(move || {
            for fd in 3..bound {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            Ok(())
        });
    }
}

// A helper the producer refuses (`?` on io::Result: increment B1a).
fn bound_from_env() -> std::io::Result<i32> {
    let v = std::env::var("ATERM_FD_BOUND").map_err(std::io::Error::other)?;
    Ok(v.len() as i32)
}

pub fn spawn_refused_helper(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let bound = bound_from_env().unwrap_or(1 << 16);
    fork_strip_exec(Strip { bound }, path, argv)
}

// std spawn of a caller's command (Command objects are C4).
pub fn std_spawn(cmd: &mut Command) -> bool {
    cmd.spawn().is_ok()
}

// posix_spawn with a caller's file actions (builder objects are C5), through a
// local declaration as aterm's pspawn.rs does.
mod ffi {
    unsafe extern "C" {
        pub fn posix_spawn(
            pid: *mut i32,
            path: *const u8,
            actions: *const u8,
            attr: *const u8,
            argv: *const *const u8,
            envp: *const *const u8,
        ) -> i32;
        pub fn vfork() -> i32;
        pub fn posix_spawn_file_actions_addclose(actions: *mut u8, fd: i32) -> i32;
        pub fn pthread_create(
            t: *mut u64,
            attr: *const u8,
            f: extern "C" fn(*mut u8) -> *mut u8,
            arg: *mut u8,
        ) -> i32;
    }
}
pub fn pspawn(path: *const u8, actions: *const u8, argv: *const *const u8) -> i32 {
    let mut pid = 0;
    unsafe { ffi::posix_spawn(&mut pid, path, actions, std::ptr::null(), argv, std::ptr::null()) }
}

// vfork: spawn-capable, a named gap of the model.
pub fn spawn_vfork() -> i32 {
    unsafe { ffi::vfork() }
}

// A raw fork whose child returns into the caller.
pub fn fork_returns() -> i32 {
    unsafe { libc::fork() }
}

// An explicit drop of an fd carrier on a spawning root's path.
pub fn spawn_after_drop(
    fd: std::os::fd::OwnedFd,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    drop(fd);
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// A thread spawned on a spawning root's path.
pub fn spawn_with_thread(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let _t = std::thread::spawn(|| {});
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// After a full strip the child duplicates stdout (the copy is not
// close-on-exec) n times. As a `for`, the producer's wave-ER summary erases
// the calls (increment S1): the census must not read the erased body as
// "no leak".
fn dup_stdout_for(n: i32) {
    for _ in 0..n {
        unsafe {
            libc::dup(1);
        }
    }
}
pub fn spawn_erased_leak(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        dup_stdout_for(1);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// The same leak as a `while` (lowered faithfully): refuted.
fn dup_stdout_while(n: i32) {
    let mut i = 0;
    while i < n {
        unsafe {
            libc::dup(1);
        }
        i += 1;
    }
}
pub fn spawn_dup_leak(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        dup_stdout_while(1);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// An fd carrier moved into a container the census does not model.
pub fn spawn_boxed_fd(
    fd: std::os::fd::OwnedFd,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    let held = Box::new(fd);
    let pid = fork_strip_exec(Strip { bound: i32::MAX }, path, argv);
    drop(held);
    pid
}

// A posix_spawn file-actions builder (builder objects are C5).
pub fn spawn_with_actions(
    actions: *mut u8,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    unsafe {
        ffi::posix_spawn_file_actions_addclose(actions, 3);
    }
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

extern "C" fn worker(_: *mut u8) -> *mut u8 {
    std::ptr::null_mut()
}

// A thread started on a spawning root's path.
pub fn spawn_after_pthread(
    t: *mut u64,
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    unsafe {
        ffi::pthread_create(t, std::ptr::null(), worker, std::ptr::null_mut());
    }
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}

// The bound depends on a value the census does not track (getpid): the
// leak is reached only through an over-approximating choice.
pub fn spawn_pid_dependent(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let bound = if unsafe { libc::getpid() } == 1 { i32::MAX } else { 1 << 16 };
    fork_strip_exec(Strip { bound }, path, argv)
}

// The child never execs: the site's non-vacuity check cannot be refuted.
pub fn spawn_never_execs() -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        unsafe { libc::_exit(0) }
    }
    pid
}
