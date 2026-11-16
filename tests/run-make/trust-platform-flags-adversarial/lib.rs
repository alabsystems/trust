// Trust (platform protocols, plan L1a; adversarial inertness check): the subject of `rmake.rs`.
// Unlike `trust-platform-flags-inert/lib.rs` this crate HAS a platform policy site: the raw
// `fork` + descriptor strip + `execv` shape plan L1e refutes (`spawn_capped`, strip bound 65 536)
// and its fixed twin (`spawn_full`, bound `i32::MAX`). An inert flag must leave every emitted
// byte of a crate the pass would analyse where it was, not only of a crate with nothing to see.

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

pub fn checksum(bytes: &[u8]) -> u32 {
    let mut acc: u32 = 0x811c_9dc5;
    for &b in bytes {
        acc ^= u32::from(b);
        acc = acc.wrapping_mul(0x0100_0193);
    }
    acc
}
