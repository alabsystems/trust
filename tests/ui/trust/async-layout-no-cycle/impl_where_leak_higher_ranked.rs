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
//! OPAQUE-IMPL-WHERE-LEAK-1 (higher_ranked): the where-clause naming the opaque sits behind a
//! HIGHER-RANKED where-clause (`for<'a> &'a X: Tr2`) of the impl a reified method selects.
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every lane.
//! The producer's `Instance::resolve_for_fn_ptr` of `<u8 as Prim>::m` is admitted only by the
//! leak-free selection walk (`trust_mir_extract::ctfe_reentrancy::select_reveal_free`). That
//! walk handed every trait obligation with bound variables to fulfillment, which PROVES
//! `for<'a> &'a X: Tr2` leak-free (`Tait: Debug` holds from `Tait`'s own bound) without looking
//! at the where-clauses of the impl it selects; the codegen-mode resolution then normalizes
//! `Tait: Debug`, reveals `Tait` and borrow-checks `define`, the body being built: E0391
//! ("resolving instance `<u8 as Prim>::m`" -> "evaluating trait selection obligation
//! `for<'a> &'a X: Tr2`" -> "computing type of `Tait`") under `default` and `lower` on the
//! stage 1 of main `3ce41aa8e` and on the toolchain `321aaeda7`; `off` never asks. The walk now
//! selects a higher-ranked trait obligation with placeholders and walks its nested
//! obligations, so `Tait: Debug` is met by name and the resolution declines.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
use std::fmt::Debug;
pub type Tait = impl Debug;
pub trait Tr2 {}
pub struct X;
impl<'a> Tr2 for &'a X where Tait: Debug {}
pub trait Prim { fn m(x: u32) -> u32; }
impl Prim for u8 where for<'a> &'a X: Tr2 { fn m(x: u32) -> u32 { x } }
#[define_opaque(Tait)]
pub fn define() -> (Tait, u32) {
    let _f: fn(u32) -> u32 = <u8 as Prim>::m;
    (0u32, 1)
}
