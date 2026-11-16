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
//! OPAQUE-IMPL-WHERE-LEAK-1 (a8): a by-value argument whose field is `*const A<u8>` directly.
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every
//! lane. The type the producer asks about inside `mir_built` of `Tait`'s defining body
//! names no opaque, but normalizing its `<u8 as Prim>::Storage` selects an impl whose
//! WHERE-CLAUSE (`Wrap<u8>: Send`, `W: Send`) is an auto trait of a type holding the opaque. The
//! analysis typing mode LEAKS it (`type_of_opaque` -> borrowck of the defining body, the
//! one being built: E0391 under `default` and `lower` on the stage 1 of `integ/fix10`
//! `425f2192be`; `off` never asks). Inside `mir_built` every such question is now asked
//! leak-free (`trust_mir_extract::ctfe_reentrancy::leak_free_typing_mode`: every local
//! opaque definable, so the auto-trait goal is ambiguous and the question declines).

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
pub trait Prim { type Storage; }
pub type Tait = impl Sized;
pub struct Wrap<T> { t: T, x: Tait }
impl<T> Prim for T where Wrap<T>: Send { type Storage = u8; }
pub struct A<T: Prim> { v: <T as Prim>::Storage }
pub struct C { p: *const A<u8>, n: u32 }
#[define_opaque(Tait)]
pub fn define(c: C) -> (Tait, u32) {
    (0u32, c.n)
}
pub fn other(c: C) -> u32 { c.n }
