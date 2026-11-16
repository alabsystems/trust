#![crate_type = "lib"]
//! Fixture for `rmake.rs` (the measurement's `repro/ffi.rs`, code verbatim): every callee is a
//! LOCAL `extern "C"` declaration. Measured 2026-10-01 on a stage1 at trust 771983b92
//! (`-Ztrust-verify=off -Ztrust-ir-lower=on`), every callee was read as Rust-ABI: `close` and
//! `flock` were declared `rustcc` (their bodies spliced), and the three bodies whose callee is
//! variadic or takes `*mut *mut c_void` were refused at assembly with
//! `UnsignableRustAbiDeclaration(<callee>)` ("... which declares the Rust calling convention").
unsafe extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
    fn close(fd: i32) -> i32;
    fn posix_spawn_file_actions_destroy(actions: *mut *mut core::ffi::c_void) -> i32;
    fn posix_spawn_file_actions_adddup2(actions: *mut *mut core::ffi::c_void, fd: i32, new: i32) -> i32;
    fn flock(fd: i32, op: i32) -> i32;
}
pub fn local_variadic(fd: i32) -> i32 { unsafe { fcntl(fd, 2, 1) } }
pub fn local_plain(fd: i32) -> i32 { unsafe { close(fd) } }
pub fn local_ptrptr(a: *mut *mut core::ffi::c_void) -> i32 { unsafe { posix_spawn_file_actions_destroy(a) } }
pub fn local_ptrptr_dup2(a: *mut *mut core::ffi::c_void, fd: i32) -> i32 { unsafe { posix_spawn_file_actions_adddup2(a, fd, 3) } }
pub fn local_flock(fd: i32) -> i32 { unsafe { flock(fd, 2) } }
