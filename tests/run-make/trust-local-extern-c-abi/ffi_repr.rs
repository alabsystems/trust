#![crate_type = "lib"]
#![allow(improper_ctypes)]
//! Fixture for `rmake.rs`: the one thing reading a local foreign item's REAL ABI must not do.
//!
//! A bodyless non-`Rust` declaration is an FFI boundary to trust-ir-build, whose
//! `FfiStructReprUnpinned` rule rejects a by-value `repr(Rust)` struct parameter or return on it,
//! and a rejected declaration invalidates the WHOLE crate module (a compile error), not one
//! body. While a local foreign item was read as Rust-ABI it never met that rule. So the producer
//! refuses the CALL to such a declaration (`Callee(foreign-ABI repr(Rust) struct by value)`) and
//! the crate still compiles; `repr(C)` and `repr(transparent)` are not refused by that tag.

pub struct Pair {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
pub struct CPair {
    pub a: u32,
    pub b: u32,
}

#[repr(transparent)]
pub struct Fd(pub i32);

unsafe extern "C" {
    fn mk_pair() -> Pair;
    fn take_pair(p: Pair) -> u32;
    fn mk_cpair() -> CPair;
    fn dup_fd(fd: Fd) -> Fd;
}

/// Returns a `repr(Rust)` struct by value across `extern "C"`: refused.
pub fn drop_pair() {
    unsafe {
        mk_pair();
    }
}

/// Passes a `repr(Rust)` struct by value across `extern "C"`: refused.
pub fn pass_pair(p: Pair) -> u32 {
    unsafe { take_pair(p) }
}

/// `repr(C)`: an FFI-pinned layout, never refused by this tag.
pub fn drop_cpair() {
    unsafe {
        mk_cpair();
    }
}

/// `repr(transparent)`: the layout of its field, never refused by this tag.
pub fn dup(fd: Fd) -> Fd {
    unsafe { dup_fd(fd) }
}
