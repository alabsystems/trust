//@ revisions: ms_safe_static ms_vtable at_dep_call at_dep_call_strict at_dep_call_ms at_fnptr at_vtable
//@ revisions: at_generic_dep_instance
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: unverified_edge_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[ms_safe_static] compile-flags: -Ztrust-policy=memory-safe
//@[ms_vtable] compile-flags: -Ztrust-policy=memory-safe
//@[at_dep_call_strict] compile-flags: -Ztrust-policy=strict
//@[at_dep_call_ms] compile-flags: -Ztrust-policy=memory-safe
//@[ms_safe_static] check-fail
//@[ms_vtable] check-fail
//@[at_dep_call] check-fail
//@[at_dep_call_strict] check-fail
//@[at_dep_call_ms] check-fail
//@[at_fnptr] check-pass
//@[at_vtable] check-pass
//@[at_generic_dep_instance] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
//! Trust (r15, 2026-10-07): the edges out of a body into code this compilation
//! does not verify are enumerated in ONE place
//! (`compiler/rustc_mir_transform/src/trust_verify/unverified_edges.rs`): a call,
//! an indirect call, a foreign static read, the creation of a function pointer or
//! of a vtable, drop glue, inline assembly. Two assumption rows ask it — the
//! memory-safe classifier skip (`memory_safe_assumption_uncharged_edges`) and the
//! `#[trust::assume_total]` revocation (`assume_total_cannot_cover_body`) — and
//! before, each scan knew a different subset.
//!
//! MEASURED BEFORE on stage-1 `ae0494648a` (the r14 review), each revision below:
//!
//! | revision | shape | before |
//! |---|---|---|
//! | `ms_safe_static` | memory-safe skip body (`&raw const s.a`) reading a local `safe static` | rc=0, `assumption:addr-of-field`; a verify-off `main` linking it (the symbol NULL) died with SIGSEGV (139) |
//! | `ms_vtable` | memory-safe skip body unsizing the dependency's `W` to `&dyn Act` | rc=0 |
//! | `at_dep_call` / `_strict` / `_ms` | `#[trust::assume_total]` body calling the verify-off `null_fn` | rc=0 in default, strict and memory-safe; each binary twin died with SIGSEGV (139) |
//! | `at_fnptr` | `assume_total` body returning `null_fn as fn()` | rc=0, skipped, no warning |
//! | `at_vtable` | `assume_total` body returning `&W(3) as &dyn Act` | rc=0, skipped, no warning |
//! | `at_generic_dep_instance` | a verified `f` calling a GENERIC `assume_total` `run<I: Iterator>` (`it.last()`) at the dependency's `It`, whose `next` writes through null | rc=0 in default, strict and memory-safe; binary SIGSEGV (139) |
//!
//! AFTER: the skip is withheld (memory-safe) and the `assume_total` skip is revoked
//! with the warning, which names the edge. A revoked `assume_total` body is verified
//! in full like any other body: the dependency CALL is then refused by its own
//! absent-callee row; the fn-pointer and vtable bodies have no obligation of their
//! own (the pointer is charged where it is called) and pass — the point is that
//! they are no longer an assumption row. A generic body's dispatch at its own type
//! parameter is an edge too (the instantiation chooses the code): `run` is revoked and
//! verified per instance, and `f`'s instance discharge is refused. The controls (`assume_total` bodies with
//! no edge keep their skip and get no warning) are in
//! `assume_total_safe_body_keeps_its_skip.rs`.
extern crate unverified_edge_dep as dep;

pub struct S {
    pub a: u32,
}

#[cfg(ms_safe_static)]
unsafe extern "C" {
    pub safe static TRUST_R: &'static u32;
}

#[cfg(ms_safe_static)]
pub fn skipped_reads_safe_static(s: &S) -> u32 {
    //[ms_safe_static]~^ ERROR Trust full verification skipped `unverified_edge_kinds::skipped_reads_safe_static`
    //[ms_safe_static]~| NOTE a read of the foreign static `TRUST_R`
    let _q = &raw const s.a;
    *TRUST_R
}

#[cfg(ms_vtable)]
pub fn skipped_mints_dep_vtable(s: &S) -> &'static dyn dep::Act {
    //[ms_vtable]~^ ERROR Trust full verification skipped `unverified_edge_kinds::skipped_mints_dep_vtable`
    //[ms_vtable]~| NOTE a vtable for
    let _q = &raw const s.a;
    &dep::W(3)
}

#[cfg(any(at_dep_call, at_dep_call_strict, at_dep_call_ms))]
#[trust::assume_total]
fn t(x: u32) -> u32 {
    //[at_dep_call,at_dep_call_strict,at_dep_call_ms]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_dep_call,at_dep_call_strict,at_dep_call_ms]~| NOTE `dep::null_fn` in bb0
    dep::null_fn();
    x
}

#[cfg(any(at_dep_call, at_dep_call_strict, at_dep_call_ms))]
pub fn calls_t() -> u32 {
    t(1)
}

#[cfg(at_fnptr)]
#[trust::assume_total]
pub fn hands_out_dep_fn_pointer() -> fn() {
    //[at_fnptr]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_fnptr]~| NOTE a function pointer to
    dep::null_fn as fn()
}

#[cfg(at_vtable)]
#[trust::assume_total]
pub fn hands_out_dep_vtable() -> &'static dyn dep::Act {
    //[at_vtable]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_vtable]~| NOTE a vtable for
    &dep::W(3)
}

#[cfg(at_generic_dep_instance)]
#[trust::assume_total]
#[inline(never)]
fn run<I: Iterator<Item = u32>>(it: I) -> Option<u32> {
    //[at_generic_dep_instance]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[at_generic_dep_instance]~| NOTE `std::iter::Iterator::last` in bb0
    it.last()
}

#[cfg(at_generic_dep_instance)]
pub fn f() -> Option<u32> {
    //[at_generic_dep_instance]~^ ERROR Trust instance discharge not established for `unverified_edge_kinds::f`
    run(dep::It(1))
}
