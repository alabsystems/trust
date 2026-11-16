//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off
//! Trust (vtable slice 16): the MIR ORACLE signs pointer/struct-payload and
//! niche/Variants::Single enums FIRST-CLASS (`EnumDef` + Const-seeded construction) — the
//! extractor's faithful eligibility re-synced to the producer's `register_enum` (wave-EP thin
//! `Ty::Ptr`, #174 sized `Ty::Struct`, wave-EF `FatPtr(Str)`, B3-3 nested enums, char; NOT
//! Direct-tag-gated) and the bridge's ctor seed gone recursive (`seed_lane_ty` mirror). Before
//! this, a flat `[__tag, __v..]` construction covered tag+selected-variant lanes only, so
//! every such body held at the LIVE-havoc gate (the slice-11 "flat enum-model" family).
//!
//! Each shape below is one of the measured offender rows; the file existing at all pins
//! "these still compile clean under the flag" (the sweep measured their differential rows the
//! day this landed — see TRUST_IR_V2.md's slice-16 section for the numbers).

// Upstream 1.100: `never_type` is stable; the feature attribute now warns.
#![allow(dead_code)]
#![allow(non_upper_case_globals)]

// Variants::Single over a multi-variant def (issue-54378): descriptor declines LOCKSTEP on
// both sides; the `!` payload E1-respells to Unit on both.
pub const NEVER_OPT: Option<!> = None;

// The niche pointer-payload shape (two-uses-in-trait-impl): `Option<&T>`, fieldless-variant
// construction, never-read opaque ref param.
pub fn next_none(_r: &mut u32) -> Option<&'static u32> {
    None
}

// The niche struct-payload shape (promote-static): `Option<String>` — the String def DAG must
// agree structurally on both sides.
pub static NONE_STRING: Option<String> = None;

// The niche Box shape (enum-nullable-const): `Result<(), Box<isize>>`, Ok(()) → PhantomData
// unit lane, operand skipped.
pub static C: Result<(), Box<isize>> = Ok(());

// The Direct-tag struct-payload CONSTRUCTION (ambiguous get): the bridge ctor seed must spell
// the payload lane as the RECURSIVE struct zero (`const enum { 0, { 0, 0 } }`), never Int(0) —
// `constant_to_value` type-checks every seed lane.
pub struct Payload {
    pub a: u32,
    pub b: u64,
}
pub fn mk_ok(v: u8) -> Result<Payload, ()> {
    Ok(Payload { a: v as u32, b: 0 })
}

// The nested-enum payload shape (multispace): the inner enum registers first, the outer
// admits it via the nested arm; scalar-payload construction of the outer.
pub enum Inner {
    Position(i8),
    NodePosition(u32),
}
pub enum Outer {
    Done(i8, i8),
    Error(Inner),
    Incomplete(u32, u64),
}
pub fn mk_done() -> Outer {
    Outer::Done(0, 0)
}

// The String-payload niche enum with a fieldless construction (simple-enum-usage-8506).
pub enum Either {
    One,
    Other(String, String),
}
pub static one: Either = Either::One;

fn main() {
    let _ = (NEVER_OPT.is_none(), next_none(&mut 0), &NONE_STRING, &C);
    let _ = (mk_ok(1), mk_done(), &one);
}
