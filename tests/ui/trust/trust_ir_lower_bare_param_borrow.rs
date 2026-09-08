//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-POH): a shared borrow of a BARE `ty::Param` local -- `&i` on `i: T`.
//!
//! THE HEAD/COMPONENT AGREEMENT, not a new admission. `snapshotable_borrow_component` already
//! admits `Ty::Unit` at every depth >= 1; `snapshotable_borrow_aggregate` -- the depth-0 HEAD --
//! has no `Ty::Unit` arm at all and falls to `_ => false`. Measured, that is the whole
//! difference: `wrapped` below is CLEAN today because the wrapper's field passes the component
//! predicate, while `bare` is the sole refusal. Putting the value inside a one-field struct made
//! the borrow lower. That is a site disagreeing with its own component predicate one recursion
//! level apart, and the fix is the agreement rather than a fifth spelling of the same posture
//! with its own ledger profile.
//!
//! GROUND TRUTH, for the reason the neighbouring disjunct states: `Ty::Unit` is overloaded three
//! ways -- the genuine unit, the fail-closed degraded collapse, and `map_ty`'s deliberate opaque
//! spelling for a bare type parameter. The neighbour discriminates the FIRST with `is_unit()`;
//! this disjunct discriminates the THIRD with an affirmative `ty::Param(_)` test. The degraded
//! collapse matches neither and keeps its tag, which is the case `is_unit()` exists for.
//!
//! WHAT IT CLAIMS, stated plainly: "this slot holds T's bytes" is FALSE of the real program --
//! `T` has bytes the model erases. It is safe only because nothing is permitted to read it as
//! true. `map_ty`'s `ty::Param` arm sets `param_opaque`, which makes the body `symbolic`, and
//! `splice_ok` refuses every symbolic body outright, so no VC, no engine and no codegen ever
//! ranges over the slot. Every body below is already `symbolic` BEFORE this wave.
//!
//! A CORRECTION CARRIED IN THE FIXTURE. An earlier draft pinned "a `ty::Alias` / unresolved
//! projection local keeps the tag, as the nearest neighbour that also spells `Ty::Unit`". Both
//! halves are false: an associated-type projection over a param maps to an opaque-alias STRUCT,
//! not `Ty::Unit`, and its shared borrow is ALREADY CLEAN. `alias_stays_clean` pins that as the
//! control it actually is, so the next author does not re-derive the inverted version.

#![allow(dead_code, unused_variables)]

fn sink<T>(_x: &T) {}

// THE LANE.
pub fn bare<T>(i: T) {
    let _r = &i;
}

// THE PREEMPTION PIN, and it is the one real risk this wave carries. `sink(&i)` at an explicit
// CALL-ARGUMENT position was ALREADY CLEAN before this wave -- measured on the pre-wave driver --
// but through a different path: the call-argument fallback hands the callee a place-path VALUE
// and sets `place_path_carrier`. The `Borrow` arm now succeeds first, so this body's emitted IR
// and its flag profile CHANGE even though its verdict does not. That is intended -- the callee
// wanted a pointer and now gets one, which is the lesson recorded at the fallback's own site --
// but it must be measured, not assumed: the sweep has to report became-dirty 0 and no new
// module-validation error, and `place_path_carrier` is expected to DROP.
pub fn bare_arg<T>(i: T) {
    sink(&i);
}

// The operator desugar, which autorefs both operands.
pub fn bare_eq<T: PartialEq>(i: T, j: T) -> bool {
    i != j
}

// The CONTROL that isolates the mechanism: the same value one recursion level down, clean before
// this wave and after. If `bare` is ever refused again while this stays clean, the head and the
// component have drifted apart a second time.
pub struct W<T>(pub T);

pub fn wrapped<T>(x: W<T>) {
    let _r = &x;
}

// The CORRECTION CONTROL: an associated-type projection over a param maps to an opaque-alias
// struct, not to `Ty::Unit`, and was already clean. It is a control, not a negative.
pub trait Tr {
    type A;
}

pub fn alias_stays_clean<T: Tr>(x: T::A) {
    let _r = &x;
}

pub fn alias_eq<T: Tr>(i: T::A, j: T::A) -> bool
where
    T::A: PartialEq,
{
    i != j
}

// FAIL-CLOSED: a GENUINE unit local keeps taking its own neighbouring disjunct, byte-identical.
pub fn genuine_unit() {
    let u: () = ();
    let _r = &u;
}

fn main() {}
