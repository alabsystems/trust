//@ needs-trust-verify
//@ aux-build: no_std_panic_handler_only_dep.rs
//@ revisions: dep_handler local_handler
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[dep_handler] check-pass
//@[local_handler] check-fail
//! HONEST CONTROL for the 2026-09-28 residency conjunct on
//! `crate_is_authentic_{foundational,core,std}` (trust_verify.rs).
//!
//! In a `#![no_std]` graph the `panic_impl` lang item is owned by whichever
//! crate declares `#[panic_handler]`. Before the conjunct that crate was graded
//! `std`; now it is not, because it is not the compiler's own resident sysroot
//! crate. That is the intended over-decline. This fixture pins that it stops
//! there: `core`'s own credits in the same graph are untouched, so draining a
//! real `core::slice::Iter` is still statically PROVED, under `certify`, with
//! the handler supplied
//!
//! * `dep_handler` — by an honest panic-handler dependency (`panic-halt` style)
//!   that declares nothing else: the whole crate builds;
//! * `local_handler` — by this crate itself. The handler is `#[trust::skip]`, so
//!   `certify` refuses the handler as a declared gap (its own, unrelated row),
//!   and `drain` must still be proved.
//!
//! MEASURED 2026-09-28: `drain` proved (1 proved, kernel-certified) on stage-1
//! `trustc` at `52113eb46` (origin/main) and with the conjunct, in both shapes.
#![no_std]
#![feature(register_tool)]
#![register_tool(trust)]

#[cfg(dep_handler)]
extern crate no_std_panic_handler_only_dep;

#[cfg(local_handler)]
#[trust::skip]
#[panic_handler]
fn on_panic(_: &core::panic::PanicInfo<'_>) -> ! {
    //[local_handler]~^ ERROR Trust full verification skipped `no_std_panic_handler_owner_keeps_core_credit::on_panic`
    loop {}
}

pub fn drain(xs: &[u32]) {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    for _x in xs.iter() {}
}
