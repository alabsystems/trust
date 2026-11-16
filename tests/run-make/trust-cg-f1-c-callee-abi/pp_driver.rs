//! Built by the DEFAULT backend; calls `pp`'s functions, built by whichever backend is under test.
#![feature(rustc_private)]
extern crate libc;
extern crate pp;

use std::os::fd::AsRawFd;

fn main() {
    let file = std::fs::File::create("pp-scratch.bin").expect("scratch file");
    let fd = file.as_raw_fd();
    let mut actions: *mut core::ffi::c_void = std::ptr::null_mut();
    assert_eq!(unsafe { libc::posix_spawn_file_actions_init(&mut actions) }, 0);
    // 0 only if all three arguments arrived; EBADF (9) names which descriptor was refused.
    let ok = pp::f1_adddup2(&mut actions, fd, 77);
    let bad_fd = pp::f1_adddup2(&mut actions, -1, 77);
    let bad_new = pp::f1_adddup2(&mut actions, fd, -1);
    let destroyed = pp::f1_destroy(&mut actions);
    println!("ok={ok} bad_fd={bad_fd} bad_new={bad_new} destroy={destroyed}");
}
