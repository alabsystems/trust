//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! DISCHARGE-NO-EVIDENCE-1 (2026-10-19): non-generic UPSTREAM fns whose bodies the
//! dependent crate never lowers, so a call to one is a generic absent callee there
//! (`[trust-absent-callee-assumption] call to absent callee ...`): `note` is the shape
//! of aterm's `aterm_log::__log` behind `aterm_log::info!`, `take` the shape of
//! `aterm_uds::spawnfd::adopt_startup_bridge_lanes` (an `unsafe fn` in another crate).
//! `#[inline(never)]` keeps their MIR out of the dependent crate (no cross-crate
//! inlining makes either a bundled body).

#[inline(never)]
pub fn note(n: u32) {
    std::hint::black_box(n);
}

/// # Safety
///
/// None needed: `unsafe` only so that a call to it is a call to an `unsafe fn`.
#[inline(never)]
pub unsafe fn take(n: u32) -> u32 {
    std::hint::black_box(n)
}
