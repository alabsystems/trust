//@ revisions: default lower off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[default] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[lower] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[off] compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@ forbid-output: error[E
//! OPAQUE-IMPL-WHERE-LEAK-1 (fn_ptr): a trait method REIFIED to a `fn` pointer in the
//! defining body, through an impl whose where-clause names the opaque.
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every
//! lane. The producer's `Instance::resolve_for_fn_ptr` of `<u8 as Prim>::m` selects the
//! impl in the codegen mode and reveals `Tait` through `Tait: Debug` -> borrowck of
//! `define`: E0391 under `default` and `lower` on the stage 1 of `integ/fix10`
//! `425f2192be`. Declined now by the same leak-free selection walk as `resolve`. The pointer
//! is reified and not called: a call through a `fn` pointer is a strict-policy verification
//! gap with or without the opaque (measured: the same crate without the where-clause fails
//! the `default` revision on that stage 1 and on this change alike), which is not what this
//! test pins.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
use std::fmt::Debug;
pub type Tait = impl Debug;
pub trait Prim { fn m(x: u32) -> u32; }
impl Prim for u8 where Tait: Debug { fn m(x: u32) -> u32 { x } }
#[define_opaque(Tait)]
pub fn define() -> (Tait, u32) {
    let _f: fn(u32) -> u32 = <u8 as Prim>::m;
    (0u32, 1)
}
