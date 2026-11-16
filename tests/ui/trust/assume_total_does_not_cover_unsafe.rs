//@ needs-trust-verify
//@ edition: 2021
//@ revisions: raw_deref transmute_box param_root safe_extern unsafe_fn safe_extern_static
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (D8-P0, 2026-09-23): `#[trust::assume_total]` ASSUMES TOTALITY, NEVER
//! VALIDITY — an `assume_total` body that can perform an unsafe operation is
//! verified in full (`assume_total_cannot_cover_body` in
//! `compiler/rustc_mir_transform/src/trust_verify/validity_transmute.rs`), with a
//! warning that says so.
//!
//! # The defect this pins
//!
//! `verification_decision` skipped an `assume_total` body wholesale, so every
//! validity obligation inside it vanished with its panic obligations. Measured
//! on the stage-1 `trustc` of 2026-09-23 (the D8 critic's `k3`/`k4`/`k5`), each
//! revision below compiled rc=0 — or, for `unsafe_fn`, was refused only at the
//! CALLER's unsafe-call row while the body itself was never examined:
//!
//! | revision | shape | before |
//! |---|---|---|
//! | `raw_deref` | `*(4usize as *const u32)` inside `assume_total` (`k3`) | rc=0: one caller-side runtime-checked row |
//! | `transmute_box` | `transmute::<usize, Box<u32>>(4)` inside `assume_total` (`k4`) | rc=0: only an `ASSUMPTION [assumed-total]` line |
//! | `param_root` | that `Box` fed to `f(b: Box<u32>) { *b }` (`k5`) | rc=0; the binary twin exits 139 (SIGSEGV) |
//! | `safe_extern` | a `safe fn` from an `unsafe extern` block wrapped in `assume_total` | rc=0 at O0 and O2 — the twin WITHOUT the attribute is refused by its `[hardened_ffi_boundary]` row |
//! | `unsafe_fn` | an `assume_total` `unsafe fn` derefing its argument | body never verified |
//! | `safe_extern_static` | a `safe static` from an `unsafe extern` block read inside `assume_total` (review of D8-P0: the first draft checked foreign CALLS only) | rc=0 at O0 — the twin WITHOUT the attribute is refused by its `[unsafe:mutable-static]` row |
//!
//! The critic's `k5` is the sharp one: the Box-parameter validity root trusts a
//! `Box` because its CALLER is verified, and the caller that manufactured it was
//! exactly the body `assume_total` had removed from verification.
//!
//! # Why the whole body, and not "only the unsafe rows"
//!
//! Keeping `assume_total` for the panic rows while charging the validity rows
//! would need every row classified as "totality" or "validity"; a validity row
//! misfiled as a panic (rustc's alignment/null checks ARE MIR `Assert`s) would
//! be a false proof. Verifying the whole body is the split that cannot be
//! wrong; the warning's help names the repair (move the unsafe operation into
//! its own, un-attributed function). The control — a SAFE `assume_total` body
//! keeps its skip, and gets no warning — is
//! `assume_total_safe_body_keeps_its_skip.rs`.

#[cfg(raw_deref)]
#[trust::assume_total]
fn mk() -> u32 {
    //[raw_deref]~^ WARN does not cover its unsafe operations
    //[raw_deref]~| ERROR safety verification incomplete
    unsafe { *(4usize as *const u32) }
}

#[cfg(raw_deref)]
pub fn c() -> u32 {
    mk()
}

#[cfg(transmute_box)]
#[trust::assume_total]
fn mk() -> Box<u32> {
    //[transmute_box]~^ WARN does not cover its unsafe operations
    //[transmute_box]~| ERROR safety verification incomplete
    //[transmute_box]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { std::mem::transmute::<usize, Box<u32>>(4) }
}

#[cfg(transmute_box)]
pub fn c() -> usize {
    let b = mk();
    std::mem::forget(b);
    0
}

#[cfg(param_root)]
#[trust::assume_total]
fn mk() -> Box<u32> {
    //[param_root]~^ WARN does not cover its unsafe operations
    //[param_root]~| ERROR safety verification incomplete
    //[param_root]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { std::mem::transmute::<usize, Box<u32>>(4) }
}

// The Box-parameter root: row-free BY DESIGN, because `mk` is charged.
#[cfg(param_root)]
fn f(b: Box<u32>) -> u32 {
    *b
}

#[cfg(param_root)]
pub fn c() -> u32 {
    f(mk())
}

#[cfg(safe_extern)]
unsafe extern "C" {
    safe fn ext_mk() -> u32;
}

#[cfg(safe_extern)]
#[trust::assume_total]
fn w() -> u32 {
    //[safe_extern]~^ WARN does not cover its unsafe operations
    //[safe_extern]~| ERROR safety verification incomplete
    ext_mk()
}

#[cfg(safe_extern)]
pub fn c() -> u32 {
    w()
}

#[cfg(unsafe_fn)]
#[trust::assume_total]
unsafe fn rd(p: *const u32) -> u32 {
    //[unsafe_fn]~^ WARN does not cover its unsafe operations
    //[unsafe_fn]~| ERROR safety verification incomplete
    *p
}

#[cfg(unsafe_fn)]
pub fn c() -> u32 {
    unsafe { rd(4usize as *const u32) }
}

#[cfg(safe_extern_static)]
unsafe extern "C" {
    safe static EXT_R: &'static u32;
}

#[cfg(safe_extern_static)]
#[trust::assume_total]
fn w() -> &'static u32 {
    //[safe_extern_static]~^ WARN does not cover its unsafe operations
    //[safe_extern_static]~| ERROR safety verification incomplete
    EXT_R
}

#[cfg(safe_extern_static)]
pub fn c() -> u32 {
    *w()
}
