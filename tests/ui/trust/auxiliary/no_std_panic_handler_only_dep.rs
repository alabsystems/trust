//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An HONEST `#![no_std]` panic-handler dependency (`panic-halt` style),
//! compiled with verification OFF the way Targo compiles every dependency unit.
//! It supplies the graph's `#[panic_handler]` — the `panic_impl` lang item — and
//! NOTHING else: no `#[lang]` attribute, no feature gate, no public item.
//!
//! Since 2026-09-28 `crate_is_authentic_{foundational,std}` also require artifact
//! residency, so this crate is no longer graded `std`. The caller fixture
//! `no_std_panic_handler_owner_keeps_core_credit.rs` pins that the change stops
//! there: `core`'s own credits in the same graph are untouched.
#![no_std]

#[panic_handler]
fn on_panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
