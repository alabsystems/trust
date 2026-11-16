//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Airrefutable_let_patterns
//@ edition: 2021
//! Trust (wave-LNO): the if-let VALUE-enum lane's G2 -- a `is_pure_value_shape` test -- is
//! DELETED, not widened.
//!
//! G2 was a strictly narrower PROXY for the question G3 asks three lines below it, and the two
//! neighbours disagreed on exactly one population: `!is_pure_value_shape && register_enum(..)
//! .is_some()`, which is character for character the definition of the
//! `Let(non-opaque enum scrutinee)` refusal in the opaque channel. Those bodies were refused by
//! BOTH channels -- by this lane for not being pure, and by the opaque one for not being opaque.
//!
//! The A/B is one spelling apart: `if let Some(_s) = o` refused while `match o { Some(_s) => .. }`
//! on the same `Option<&i32>` was clean.
//!
//! THE TOOTH IS NOW AN IDENTITY, which is stronger than the case analysis it replaces. `map_ty`'s
//! enum arm returns `Ty::Enum(eid)` iff `register_enum` succeeds; `is_opaque_lane_enum` is
//! literally `register_enum(..).is_none()`. So the set this lane claims and the set the opaque
//! channel claims are complements BY CONSTRUCTION: no body that lowers today can be made worse,
//! the two channels cannot both claim a scrutinee, and the lane can only ever turn a refusal into
//! a lowering.
//!
//! NO WORD IS LOOSENED. This does not widen what "pure" covers; it removes a purity test from a
//! place where purity was never the question. And it is a strict IMPROVEMENT in faithfulness for
//! this population rather than a relaxation: under the old gate these bodies could only have
//! reached the opaque channel, which mints an `Undef` test and binds every payload local at
//! `Ty::Unit` -- coverage with zero verification value. This lane binds each payload at its REAL
//! registered field type and mints a REAL discriminant test.
//!
//! Not under `=strict`: the negatives below must keep their tags.

#![allow(dead_code, unused_variables)]

// THE LANE, one fixture per admitted payload class. Each is a non-pure value shape whose enum
// `register_enum` nonetheless models first-class.
pub fn thin_ref(o: Option<&i32>) -> i32 {
    if let Some(s) = o { *s } else { 0 }
}

pub fn raw_ptr(o: Option<*const i32>) -> i32 {
    if let Some(_p) = o { 1 } else { 0 }
}

pub enum E {
    A(&'static i32),
    B,
}

pub fn data_enum(e: E) -> i32 {
    if let E::A(r) = e { *r } else { 0 }
}

// The MATCH twin, clean before this wave. It is the whole diagnosis: same enum, same variant
// test, one spelling apart.
pub fn match_twin(o: Option<&i32>) -> i32 {
    match o {
        Some(s) => *s,
        _ => 0,
    }
}

// FAIL-CLOSED, kept LIVE and mutation-relevant: a SINGLE-VARIANT enum has no discriminant to
// test, rustc compiles the test away, and this lane would emit a `Switch` the derived-MIR
// comparator reports as a disagreement on a body that reads clean. G2's deletion must not reach
// these -- they are refused by their own later gate, with their own tag.
pub enum One {
    A,
}

pub enum OneP {
    A(i32),
}

pub fn single_variant(o: One) -> i32 {
    if let One::A = o { 1 } else { 0 }
}

pub fn single_variant_payload(o: OneP) -> i32 {
    if let OneP::A(x) = o { x } else { 0 }
}

// FAIL-CLOSED: an enum `register_enum` DECLINES stays the opaque channel's. This is the boundary
// the identity keeps exact -- if this body ever starts lowering through the value lane, the two
// channels have stopped being complements.
pub enum Cyclic {
    Leaf,
    Node(Box<Cyclic>, [u128; 3]),
}

pub fn declined_enum(c: Cyclic) -> i32 {
    if let Cyclic::Leaf = c { 1 } else { 0 }
}

// A let-CHAIN is a `LogicalOp` node, not this shape, and keeps its existing verdict — it is not
// pinned here because let chains need edition 2024 and this file is deliberately 2021, matching
// the corpus the lane was sized against.

fn main() {}
