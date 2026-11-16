//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! A LOCAL `extern "C"` declaration carries the ABI of its `extern` block, so a body that calls
//! a variadic or `*mut *mut T` C function lowers and splices under `-Ztrust-ir-lower=strict`.
//!
//! The producer used to read a local callee's ABI off its own HIR header. A foreign item's header
//! is lowered with `Extern::None` (`rustc_ast_lowering::item::lower_foreign_item`), so every local
//! foreign fn read as Rust-ABI. A variadic (`fcntl`) or `*mut *mut c_void` callee then had no
//! signable Rust-ABI declaration, and its calling body was refused at crate assembly
//! (`UnsignableRustAbiDeclaration`), which strict reports as "this body was REFUSED at crate
//! assembly". Measured 2026-10-01 on this file's bodies (the measurement's `repro/ffi.rs`, run
//! without strict on a stage1 at trust 771983b92): `local_variadic`, `local_ptrptr` and
//! `local_ptrptr_dup2` refused, `local_plain` and `local_flock` spliced. The producer now reads
//! the block's ABI as rustc's own `fn_sig` provider does (`tcx.hir_get_foreign_abi`), the same
//! answer `libc::fcntl` always got through `tcx.fn_sig(def).abi()`, so all five are clean here.
//! `tests/run-make/trust-local-extern-c-abi` checks the emitted declarations and splices.

unsafe extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
    fn close(fd: i32) -> i32;
    fn posix_spawn_file_actions_destroy(actions: *mut *mut core::ffi::c_void) -> i32;
    fn posix_spawn_file_actions_adddup2(
        actions: *mut *mut core::ffi::c_void,
        fd: i32,
        new: i32,
    ) -> i32;
    fn flock(fd: i32, op: i32) -> i32;
}

pub fn local_variadic(fd: i32) -> i32 {
    unsafe { fcntl(fd, 2, 1) }
}

pub fn local_plain(fd: i32) -> i32 {
    unsafe { close(fd) }
}

pub fn local_ptrptr(a: *mut *mut core::ffi::c_void) -> i32 {
    unsafe { posix_spawn_file_actions_destroy(a) }
}

pub fn local_ptrptr_dup2(a: *mut *mut core::ffi::c_void, fd: i32) -> i32 {
    unsafe { posix_spawn_file_actions_adddup2(a, fd, 3) }
}

pub fn local_flock(fd: i32) -> i32 {
    unsafe { flock(fd, 2) }
}
