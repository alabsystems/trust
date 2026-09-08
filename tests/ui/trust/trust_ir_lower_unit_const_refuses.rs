//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-UC): the REFUSAL half of `trust_ir_lower_unit_const.rs`.
//!
//! Under `strict` a refusal is a compile error, so the refusals cannot share a
//! file with the admissions. One body per conjunct of the two gates the wave
//! touches, and every `//~ ERROR` here must survive every future widening.
//!
//! G2 (`try_lower_unit_arg`) is what refuses the first five, and NOTHING ELSE
//! IS — measured 2026-08-31, each reports `Call(unsupported arg) [masking:
//! <none recorded>]`, i.e. the argument declined SILENTLY and only the
//! aggregator spoke. G2 widened to `NamedConst`/`ConstBlock` on the ground that
//! a constant has no evaluation at the read site; a call, a variable read, a
//! block, a branch and a `!`-coercion all DO compute, and admitting any of them
//! would silently delete that computation. If a future edit widens G2 to
//! "anything whose ground-truth type is `()`", these five stop erroring and
//! nothing else in the tree says so.
//!
//! `non_unit_ref_const` is G1 (the ground-truth `ty::Tuple([])` gate in
//! `lower_named_const`) rather than G2: `const K: &u32 = &4;` is a const, but
//! not a unit one, and must keep taking the composite leg. `fieldless_struct_const`
//! is the other side of the same line and is DELIBERATELY not an error — a
//! zero-sized non-unit const has its own landed lane, and wave-UC keys on
//! `ty::Tuple([])`, never on ZST-ness.

#![allow(dead_code, unused_variables)]

struct Data;
struct Zst;
fn f<T>(_: T, _: ()) {}
fn h<T>(_: T, _: &u32) {}
fn z<T>(_: T, _: Zst) {}
fn produces_unit() -> () {}
fn side() {}
const K: &u32 = &4;
const ZC: Zst = Zst;

pub fn call_produces_unit() { f(Data, produces_unit()); } //~ ERROR could not fully lower
pub fn var_holding_unit() { let u = (); f(Data, u); } //~ ERROR could not fully lower
pub fn block_computing_unit() { f(Data, { side(); () }); } //~ ERROR could not fully lower
pub fn branch_computing_unit(c: bool) { f(Data, if c {} else {}); } //~ ERROR could not fully lower
pub fn never_coerced_to_unit() -> i32 { f(Data, return 3); 0 } //~ ERROR could not fully lower
pub fn non_unit_ref_const() { h(Data, K); } //~ ERROR could not fully lower

// NOT an error: a zero-sized NON-unit const keeps its own lane.
pub fn fieldless_struct_const() { z(Data, ZC); }

fn main() {}

// ---- wave-UC repair R1a: a ()-typed const with a LIVE GENERIC or INFERENCE
// argument is DELIBERATELY still refused, and these three pin that.
//
// Emitting nothing for a unit const removes the const OPERAND from the body.
// Once the body is clean the flip (`trust_ir_flip`, ON by default) replaces
// `optimized_mir`/`mir_for_ctfe` with MIR re-derived from the trust-ir, so the
// mono collector never walks the operand, the const is NEVER EVALUATED, and a
// post-monomorphization error it would have raised SILENTLY DISAPPEARS.
// Measured witness on the pre-repair build:
//
//     pub fn f<T>() { const { assert!(size_of::<T>() > 0, "ZST") }; }
//     pub fn go() { f::<()>(); }
//
// errors with E0080 today; with the unrestricted arm its twin is DerivedAgreed
// and IS flipped, and the diagnostic is gone. `flip_registry::record_green`
// checks session/provenance/markers/`unsupported.is_empty()` — nothing checks
// const parity between derived and built MIR, so no downstream guard catches it.
//
// A const carrying `has_non_region_param`/`has_non_region_infer` is exactly the
// one whose value is DEFERRED to monomorphization — that is what the `eval
// failed` tag means — so these keep their existing lanes. Cost: +9 -> +6.
trait Tr2 { const DATA: (); }
struct B2<T>(T);
impl<T: Tr2> Tr2 for B2<T> {
    const DATA: () = T::DATA;
    //~^ ERROR -Ztrust-ir-lower=strict
}
