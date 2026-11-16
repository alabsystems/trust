//@ only-unix
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-platform-properties=fd-inherit -Ztrust-platform-unanalysed=deny
//@ compile-flags: -Ztrust-platform-budget=1 -Ztrust-platform-report=verbose
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:[platform
//@ forbid-output:not refuted (refutation-only)
//@ forbid-output:PC-
//! Trust (platform protocols, plan L1a = design PR 8): the `-Ztrust-platform-*` controls parse,
//! validate and are tracked, and this trustc does not run the platform pass yet. With
//! verification on and every control set off its default (`deny` included), a crate whose
//! raw-fork shape plan L1e refutes (`spawn_capped`) still compiles with no platform diagnostic
//! of any kind, and nothing claims the property was checked.
//!
//! This is an INERTNESS pin, and plan L1d replaces it on purpose: from L1d the pass always
//! prints its crate summary note when it runs (`observe/summary_always_printed.rs`), and from
//! L1e `spawn_capped` is an error. Until then an inert flag is held only by aterm's gate
//! (E6, `PLATFORM DID NOT RUN`), never by this compiler's silence.

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
