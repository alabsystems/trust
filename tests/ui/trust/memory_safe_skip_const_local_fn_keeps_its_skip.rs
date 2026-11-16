//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0 -Ztrust-policy=memory-safe
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Trust (r20, 2026-10-07): the CONTROL for the `ms_*` revisions of
//! `unverified_edge_surface_and_consts.rs`. A memory-safe classifier-skipped body
//! (`&raw const s.a`, an `addr-of-field` row) that hands out a function pointer
//! minted by CONST EVALUATION to a LOCAL body (a `const` item, a `static`, a
//! promoted) keeps its skip: the walk of the constant's allocations finds only a
//! function this crate holds. WARN and ERROR annotations are required here, so a
//! scan that charged every constant pointer would fail this test.
#![allow(dead_code)]

pub struct S {
    pub a: u32,
}

fn local_helper() {}

const LF: fn() = local_helper;
static LG: fn() = local_helper;

pub fn skipped_const_local_fn(s: &S) -> fn() {
    let _q = &raw const s.a;
    LF
}

pub fn skipped_static_local_fn(s: &S) -> fn() {
    let _q = &raw const s.a;
    LG
}

pub fn skipped_promoted_local_fn(s: &S) -> fn() {
    let _q = &raw const s.a;
    let p: &'static fn() = &(local_helper as fn());
    *p
}
