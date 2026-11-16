//@ revisions: at_assoc_drop at_assoc_drop_strict at_assoc_drop_ms at_ref_impl at_skip_method
//@ revisions: ms_const_fn ms_dep_const_fn ms_static_fn ms_promoted_fn
//@ revisions: ms_dep_static_dyn ms_const_dyn ms_promoted_dyn at_promoted_fn at_promoted_dyn
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: unverified_edge_surface_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[at_assoc_drop_strict] compile-flags: -Ztrust-policy=strict
//@[at_assoc_drop_ms] compile-flags: -Ztrust-policy=memory-safe
//@[ms_const_fn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_dep_const_fn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_static_fn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_promoted_fn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_dep_static_dyn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_const_dyn] compile-flags: -Ztrust-policy=memory-safe
//@[ms_promoted_dyn] compile-flags: -Ztrust-policy=memory-safe
//@[at_assoc_drop] check-fail
//@[at_assoc_drop_strict] check-fail
//@[at_assoc_drop_ms] check-fail
//@[at_ref_impl] check-fail
//@[at_skip_method] check-fail
//@[ms_const_fn] check-fail
//@[ms_dep_const_fn] check-fail
//@[ms_static_fn] check-fail
//@[ms_promoted_fn] check-fail
//@[ms_dep_static_dyn] check-fail
//@[ms_const_dyn] check-fail
//@[ms_promoted_dyn] check-fail
//@[at_promoted_fn] check-pass
//@[at_promoted_dyn] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
//! Trust (r20, 2026-10-07): two holes in the ONE enumeration of a body's edges
//! into code this compilation does not verify
//! (`compiler/rustc_mir_transform/src/trust_verify/unverified_edges.rs`,
//! `unverified_edge_kinds.rs` is its first fixture).
//!
//! P1, the trait-impl SURFACE of a local type. `ty_reaches_foreign_user_code`
//! answered "no" for a local ADT with no foreign field, so a sysroot callee
//! instantiated at it was held by `#[trust::assume_total]` even when the type's
//! impls name a dependency type: `Iterator::count::<L>` drops every
//! `<L as Iterator>::Item`, here the verify-off `dep::D`, whose destructor writes
//! through null. Now the walk follows every local impl of a non-local trait that
//! names the type (`trust_verify/local_impl_surface.rs`): its associated types, and
//! its methods, which must be bodies this crate holds.
//!
//! P2, pointers minted by CONST EVALUATION. Kinds 4 and 5 (function-pointer and
//! vtable creation) were judged only at a cast in the body; a promoted, a `const`
//! item and a Rust `static`'s initializer mint the same pointers in no body the scan
//! sees. Now every constant the body uses is evaluated and its allocations are
//! walked (`judge_const_value`).
//!
//! MEASURED BEFORE on stage 1 `a92f7478b6`, each revision built by hand with a
//! verify-off `main` linking the rlib:
//!
//! | revision | shape | before |
//! |---|---|---|
//! | `at_assoc_drop` / `_strict` / `_ms` | `assume_total` `t() { L(0).count() }`, `impl Iterator for L { type Item = dep::D }` | rc=0 in all three lanes, only an `assumption:[assumed-total]` row; `main` calling `t()` died with SIGSEGV (139) |
//! | `ms_const_fn` | memory-safe skip body (`&raw const s.a`) returning `const F: fn() = dep::null_fn` | rc=0, `assumption:addr-of-field`; calling the pointer SIGSEGV |
//! | `ms_dep_const_fn` | ... returning `dep::DEP_FP` | rc=0; SIGSEGV |
//! | `ms_static_fn` | ... returning a local `static G: fn() = dep::null_fn` | rc=0; SIGSEGV |
//! | `ms_promoted_fn` | ... returning `*&(dep::null_fn as fn())` (a promoted) | rc=0; SIGSEGV |
//! | `ms_dep_static_dyn` | ... returning `dep::DEP_DYN` | rc=0; `act()` SIGSEGV |
//! | `ms_const_dyn` | ... returning a local `const C: &dyn dep::Act = &dep::W(3)` | rc=0; `act()` SIGSEGV |
//! | `ms_promoted_dyn` | ... returning `*&(&dep::W(3) as &dyn dep::Act)` (a promoted) | rc=0; `act()` SIGSEGV |
//!
//! AFTER: the memory-safe skip is withheld, and the `assume_total` skip is revoked
//! with the warning naming the edge (the revoked body is then verified in full, so
//! `t`'s refusal is its own). `at_promoted_fn` / `at_promoted_dyn` are the
//! `assume_total` twins of the promoted shapes: revoked with a warning, and they
//! pass, like `at_fnptr` / `at_vtable`, because a pointer has no obligation of its
//! own. `at_ref_impl` (the surface impl is `impl Iterator for &R`) and
//! `at_skip_method` (a `#[trust::skip]` `next`) are the other two surface shapes.
//! The controls that keep their skip are in `assume_total_safe_body_keeps_its_skip.rs`
//! and `memory_safe_skip_const_local_fn_keeps_its_skip.rs`.
extern crate unverified_edge_surface_dep as dep;

pub struct S {
    pub a: u32,
}

// ---- P1: the trait-impl surface -------------------------------------------------

#[cfg(any(at_assoc_drop, at_assoc_drop_strict, at_assoc_drop_ms))]
pub struct L(pub u32);

#[cfg(any(at_assoc_drop, at_assoc_drop_strict, at_assoc_drop_ms))]
impl Iterator for L {
    type Item = dep::D;
    fn next(&mut self) -> Option<dep::D> {
        if self.0 < 2 {
            self.0 += 1;
            Some(dep::D(0))
        } else {
            None
        }
    }
}

#[cfg(any(at_assoc_drop, at_assoc_drop_strict, at_assoc_drop_ms))]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[at_assoc_drop,at_assoc_drop_strict,at_assoc_drop_ms]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_assoc_drop,at_assoc_drop_strict,at_assoc_drop_ms]~| NOTE `std::iter::Iterator::count` in bb
    L(0).count() as u32
}

#[cfg(at_ref_impl)]
pub struct R(pub u32);

#[cfg(at_ref_impl)]
impl Iterator for &R {
    type Item = dep::D;
    fn next(&mut self) -> Option<dep::D> {
        None
    }
}

#[cfg(at_ref_impl)]
#[trust::assume_total]
#[inline(never)]
pub fn t_ref(r: &R) -> u32 {
    //[at_ref_impl]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_ref_impl]~| NOTE `std::iter::Iterator::count` in bb
    r.count() as u32
}

#[cfg(at_skip_method)]
pub struct K(pub u32);

#[cfg(at_skip_method)]
impl Iterator for K {
    type Item = u32;
    #[trust::skip]
    fn next(&mut self) -> Option<u32> {
        dep::null_fn();
        None
    }
}

#[cfg(at_skip_method)]
#[trust::assume_total]
#[inline(never)]
pub fn t_skip() -> u32 {
    //[at_skip_method]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_skip_method]~| NOTE `std::iter::Iterator::count` in bb
    K(0).count() as u32
}

// ---- P2: pointers minted by const evaluation ------------------------------------

#[cfg(ms_const_fn)]
const F: fn() = dep::null_fn;

#[cfg(ms_const_fn)]
pub fn skipped_const_fn(s: &S) -> fn() {
    //[ms_const_fn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_const_fn`
    //[ms_const_fn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    F
}

#[cfg(ms_dep_const_fn)]
pub fn skipped_dep_const_fn(s: &S) -> fn() {
    //[ms_dep_const_fn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_dep_const_fn`
    //[ms_dep_const_fn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    dep::DEP_FP
}

#[cfg(ms_static_fn)]
static G: fn() = dep::null_fn;

#[cfg(ms_static_fn)]
pub fn skipped_static_fn(s: &S) -> fn() {
    //[ms_static_fn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_static_fn`
    //[ms_static_fn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    G
}

#[cfg(ms_promoted_fn)]
pub fn skipped_promoted_fn(s: &S) -> fn() {
    //[ms_promoted_fn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_promoted_fn`
    //[ms_promoted_fn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    let p: &'static fn() = &(dep::null_fn as fn());
    *p
}

#[cfg(ms_dep_static_dyn)]
pub fn skipped_dep_static_dyn(s: &S) -> &'static (dyn dep::Act + Sync) {
    //[ms_dep_static_dyn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_dep_static_dyn`
    //[ms_dep_static_dyn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    dep::DEP_DYN
}

#[cfg(ms_const_dyn)]
const C: &(dyn dep::Act + Sync) = &dep::W(3);

#[cfg(ms_const_dyn)]
pub fn skipped_const_dyn(s: &S) -> &'static (dyn dep::Act + Sync) {
    //[ms_const_dyn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_const_dyn`
    //[ms_const_dyn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    C
}

#[cfg(ms_promoted_dyn)]
pub fn skipped_promoted_dyn(s: &S) -> &'static (dyn dep::Act + Sync) {
    //[ms_promoted_dyn]~^ ERROR Trust full verification skipped `unverified_edge_surface_and_consts::skipped_promoted_dyn`
    //[ms_promoted_dyn]~| NOTE in a constant used in
    let _q = &raw const s.a;
    let p: &'static &'static (dyn dep::Act + Sync) = &(&dep::W(3) as &(dyn dep::Act + Sync));
    *p
}

#[cfg(at_promoted_fn)]
#[trust::assume_total]
pub fn hands_out_promoted_fn() -> fn() {
    //[at_promoted_fn]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_promoted_fn]~| NOTE in a constant used in
    let p: &'static fn() = &(dep::null_fn as fn());
    *p
}

#[cfg(at_promoted_dyn)]
#[trust::assume_total]
pub fn hands_out_promoted_dyn() -> &'static (dyn dep::Act + Sync) {
    //[at_promoted_dyn]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_promoted_dyn]~| NOTE in a constant used in
    let p: &'static &'static (dyn dep::Act + Sync) = &(&dep::W(3) as &(dyn dep::Act + Sync));
    *p
}
