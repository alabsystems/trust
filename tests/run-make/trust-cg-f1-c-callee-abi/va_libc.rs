//! The VARIADIC `fcntl(fd, cmd, ...)` reached through `libc::`. On aarch64-apple-darwin the two
//! fixed arguments go in `w0`/`w1` and the anonymous one on the stack, so a call that does not
//! know the fixed count passes `fd` and `cmd` where `fcntl` never reads them.
#![crate_name = "va"]
#![feature(rustc_private)]
extern crate libc;

pub fn f1_setfd_cloexec(fd: i32) -> i32 {
    unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) }
}

pub fn f1_getfd(fd: i32) -> i32 {
    unsafe { libc::fcntl(fd, libc::F_GETFD) }
}
