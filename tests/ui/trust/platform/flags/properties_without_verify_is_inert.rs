//@ only-unix
//@ compile-flags: -Ztrust-verify=off --crate-type lib
//@ compile-flags: -Ztrust-platform-properties=fd-inherit -Ztrust-platform-unanalysed=deny
//@ compile-flags: -Ztrust-platform-budget=1 -Ztrust-platform-report=verbose
//@ check-pass
//@ dont-check-compiler-stderr
//@ forbid-output:[platform
//@ forbid-output:not refuted (refutation-only)
//@ forbid-output:PC-
//! Trust (platform protocols, plan L1a; PD-4, OD-1): `-Ztrust-verify=off` is the master
//! off-switch, and it switches the platform pass off too, whatever `-Ztrust-platform-*` asks
//! for: no error, no warning, no note, even under `deny` and even on the raw-fork shape plan L1e
//! refutes (`spawn_capped`: the strip stops at 65 536). The pass and its errors are one
//! predicate, `Session::trust_platform_errors_enabled` (verification on AND a property).

#![feature(rustc_private)]

extern crate libc;

#[derive(Clone, Copy)]
pub struct Strip {
    bound: i32,
}

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

pub fn spawn_capped(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: 1 << 16 }, path, argv)
}

pub fn spawn_full(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    fork_strip_exec(Strip { bound: i32::MAX }, path, argv)
}
