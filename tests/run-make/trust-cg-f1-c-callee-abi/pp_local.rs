//! NON-variadic C callees with a POINTER-TO-POINTER parameter, declared in a LOCAL `extern "C"`
//! block. Until 2026-10-15 the producer would not sign `*mut *mut c_void` (the dropped-borrow
//! guard), so both were published as `(...) -> (i32)`, the same spelling as the variadic `fcntl`;
//! called through that declaration on Apple arm64, every argument would go on the stack. They
//! are signed now (`(ptr, i32, i32) -> (i32)`, `(ptr) -> (i32)`). `adddup2` answers 0 only if
//! `actions` was initialized and both descriptors were valid, and EBADF if either was negative.
#![crate_name = "pp"]

use core::ffi::c_void;

unsafe extern "C" {
    fn posix_spawn_file_actions_adddup2(actions: *mut *mut c_void, fd: i32, new: i32) -> i32;
    fn posix_spawn_file_actions_destroy(actions: *mut *mut c_void) -> i32;
}

pub fn f1_adddup2(actions: *mut *mut c_void, fd: i32, new: i32) -> i32 {
    unsafe { posix_spawn_file_actions_adddup2(actions, fd, new) }
}

pub fn f1_destroy(actions: *mut *mut c_void) -> i32 {
    unsafe { posix_spawn_file_actions_destroy(actions) }
}
