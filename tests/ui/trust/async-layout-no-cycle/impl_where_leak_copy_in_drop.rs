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
//! OPAQUE-IMPL-WHERE-LEAK-1 (copy_in_drop): `needs_drop` of a struct reached behind `&`,
//! one of whose components has a USER `Copy` impl with a where-clause on an auto trait of a
//! type holding the opaque (`impl Copy for X where W: Send`).
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every
//! lane. No alias is involved: rustc's `needs_drop` reads `Y`'s fields through
//! `adt_drop_tys(X)`, a query computed in `X`'s OWN analysis environment that asks `Copy` of
//! `X`, and that leaks `W: Send` -> `type_of(Tait)` -> borrowck of `define`, whatever typing
//! environment the outer question was keyed by: E0391 under `default` and `lower` on the
//! stage 1 of `integ/fix10` `425f2192be` ("computing whether `Y` needs drop" -> "computing
//! when `X` needs drop" -> "computing whether `X` is `Copy`"). Inside `mir_built` the question
//! is now the leak-free component walk (`trust_mir_extract::ctfe_reentrancy::
//! needs_drop_leak_free`): that `Copy` goal is ambiguous there, so `X`'s fields are walked
//! instead.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
pub type Tait = impl Sized;
pub struct W { x: Tait }
#[derive(Clone)]
pub struct X(u32);
impl Copy for X where W: Send {}
pub struct Y { x: X, s: String }
#[define_opaque(Tait)]
pub fn define(y: &Y) -> (Tait, usize) { (0u32, y.s.len()) }
