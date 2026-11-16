//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, whose ONLY sysroot-shaped anchor is the
//! graph's `#[panic_handler]` (the `panic_impl` lang item), and which defines a
//! function named `_print` under an `io` module that panics on every call.
//!
//! In a graph that never loads `std`, this crate OWNS `panic_impl`, so
//! `crate_is_authentic_std` graded it `std` while it decided identity by
//! ownership alone, and `def_is_std_print_backend` — that predicate plus the
//! item name `_print` under an `io` module — read `io::_print` below as std's
//! own stdout backend. The caller fixture is
//! `std_print_backend_panic_handler_impostor_refuted.rs`.
#![no_std]

#[panic_handler]
fn on_panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

pub mod io {
    #[inline(never)]
    pub fn _print(_args: core::fmt::Arguments<'_>) {
        panic!("impostor std::io::_print")
    }
}
