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
//! OPAQUE-IMPL-WHERE-LEAK-1 (nonauto_where): the impl a field projection selects carries a
//! where-clause on a NON-auto trait of the opaque itself (`Tait: Debug`).
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every
//! lane. No auto trait leaks here: the CODEGEN-mode selection the layout funnel made
//! (`codegen_select_candidate` of `u8: Prim`, `every_reached_type`'s
//! `resolve_projection`) normalizes the where-clause and so reveals `Tait` ->
//! borrowck of `define`, the body being built: E0391 under `default` and `lower` on the
//! stage 1 of `integ/fix10` `425f2192be`. Inside `mir_built` that selection is now walked
//! leak-free (`trust_mir_extract::ctfe_reentrancy::select_reveal_free`), and an obligation
//! naming an opaque declines it.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
use std::fmt::Debug;
pub trait Prim { type Storage; }
pub type Tait = impl Debug;
impl Prim for u8 where Tait: Debug { type Storage = u8; }
pub struct A<T: Prim> { v: <T as Prim>::Storage }
pub struct C { p: *const A<u8>, n: u32 }
#[define_opaque(Tait)]
pub fn define(c: C) -> (Tait, u32) { (0u32, c.n) }
