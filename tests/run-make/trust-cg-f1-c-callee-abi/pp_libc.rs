//! The same pointer-to-pointer NON-variadic callees as `pp_local.rs`, reached through `libc::` (on
//! Darwin `posix_spawn_file_actions_t` is `*mut c_void`).
#![crate_name = "pp"]
#![feature(rustc_private)]
extern crate libc;

use core::ffi::c_void;

pub fn f1_adddup2(actions: *mut *mut c_void, fd: i32, new: i32) -> i32 {
    unsafe { libc::posix_spawn_file_actions_adddup2(actions, fd, new) }
}

pub fn f1_destroy(actions: *mut *mut c_void) -> i32 {
    unsafe { libc::posix_spawn_file_actions_destroy(actions) }
}
