//@ revisions: env_off announced
//@ only-unix
//@ needs-trust-verify
//@ compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: -Ztrust-platform-properties=fd-inherit -Ztrust-platform-unanalysed=deny
//@ rustc-env:TRUST_NO_VERIFY=1
//@[env_off] unset-rustc-env:TRUST_VANILLA_ANNOUNCED
//@[announced] rustc-env:TRUST_VANILLA_ANNOUNCED=1
//@ check-pass
//@ forbid-output:[platform
//@ forbid-output:not refuted (refutation-only)
//@ forbid-output:PC-
//! Trust (platform protocols, plan L1a; PD-4), adversarial: the ENVIRONMENT route to the master
//! off-switch. `TRUST_NO_VERIFY=1` is applied after option parsing and beats an explicit
//! `-Ztrust-verify=on` wherever it sits in argv (`tests/ui/trust/vanilla_off_note.rs`), so it
//! also switches off a platform property the command line asked for, `deny` included, on the
//! raw-fork shape plan L1e refutes. That is PD-4 (no platform verdict without verification),
//! not an FC-7 spelling hole, and this test pins how loud it is:
//!
//! * `env_off`: with no announcing parent, the compile prints the generic loud-when-off note.
//!   It does not name the platform property it dropped.
//! * `announced`: under `TRUST_VANILLA_ANNOUNCED=1` (bootstrap's marker that a parent already
//!   announced verification off) the dropped property produces NO output at all. The compiler
//!   cannot hold this case; aterm's gate does (plan E6, `PLATFORM DID NOT RUN`), and from L1d a
//!   missing platform summary note is that signal.

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

//[env_off]~? NOTE compiled WITHOUT Trust verification
