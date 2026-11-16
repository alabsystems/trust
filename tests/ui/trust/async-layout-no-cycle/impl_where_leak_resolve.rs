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
//! OPAQUE-IMPL-WHERE-LEAK-1 (resolve): a METHOD CALL in the defining body, resolved through
//! an impl whose where-clause names the opaque (`impl Prim for u8 where Tait: Debug`).
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every
//! lane. Typeck proves `u8: Prim` with `Tait` definable (its bound answers `Tait: Debug`);
//! the producer's `Instance::try_resolve` of `<u8 as Prim>::m` selects the same impl in
//! the codegen mode, which normalizes the where-clause and reveals `Tait` -> borrowck of
//! `define`: E0391 under `default` and `lower` on the stage 1 of `integ/fix10`
//! `425f2192be`. Inside `mir_built` a trait item is now resolved only when
//! `trust_mir_extract::ctfe_reentrancy::resolution_reveal_free` walks its selection
//! leak-free; this one names `Tait`, so the call stays unresolved.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
use std::fmt::Debug;
pub type Tait = impl Debug;
pub trait Prim { fn m(&self) -> u32; }
impl Prim for u8 where Tait: Debug { fn m(&self) -> u32 { 1 } }
#[define_opaque(Tait)]
pub fn define() -> (Tait, u32) { (0u32, 0u8.m()) }
