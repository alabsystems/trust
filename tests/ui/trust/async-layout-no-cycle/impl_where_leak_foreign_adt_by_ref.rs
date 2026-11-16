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
//! OPAQUE-IMPL-WHERE-LEAK-1 (foreign_adt_by_ref): a FOREIGN ADT (`Peekable<L>`) held BY VALUE
//! in a struct read through `&C`; its field `Option<Option<<L as Iterator>::Item>>` projects
//! through a LOCAL impl whose where-clause (`Wrap<u8>: Send`) is an auto trait of a type
//! holding the opaque.
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every lane. On the
//! stage 1 of `integ/fix10` `425f2192be` it is E0391 under `default` and `lower` ("computing
//! whether `C` needs drop" -> "normalizing `<L as Iterator>::Item`" -> "`Wrap<u8>: Send`" ->
//! "computing type of opaque `Tait`" -> "borrow-checking `define`"); `off` never asks. Two
//! questions reach the foreign field: `needs_drop(C)`, now the leak-free component walk
//! (`trust_mir_extract::ctfe_reentrancy::needs_drop_leak_free`), and the codegen-mode
//! `layout_of(C)` the field read needs, which the #48 funnel admits only once a foreign ADT
//! with a local argument has had its field projections resolved by the leak-free selection
//! walk (`every_reached_type`'s `foreign_fields_ok`); this one names `Tait`, so it declines.

#![feature(type_alias_impl_trait)]
#![allow(dead_code, unused)]
pub trait Prim { type Storage; }
pub type Tait = impl Sized;
pub struct Wrap<T> { t: T, x: Tait }
impl<T> Prim for T where Wrap<T>: Send { type Storage = u8; }
pub struct A<T: Prim> { v: <T as Prim>::Storage }
pub struct L;
impl Iterator for L where Wrap<u8>: Send {
    type Item = u8;
    fn next(&mut self) -> Option<u8> { None }
}
pub struct C { p: core::iter::Peekable<L>, n: u32 }
#[define_opaque(Tait)]
pub fn define(c: &C) -> (Tait, u32) { (0u32, c.n) }
