//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The NET under `e9_field_projection_discharge`. Letting a clause name a
//! struct's field must not let it name anything else, so each function here is
//! one step outside the new lane and each must stay refused.
//!
//! * `via_reference` — a `&Cst` parameter. The MIR read carries a `Deref`, and
//!   more importantly the pointee is not provably unchanged between entry and
//!   exit; `ensures` has no two-state reading for it. Refused at the recognizer
//!   (no admission) and at the binding table (a reference contributes no rows).
//! * `mixed_fields` — ALL-OR-NOTHING per struct. `degree` is an ordinary `u64`,
//!   but `terms` is not a supported scalar, so the WHOLE parameter contributes
//!   nothing. A per-field filter would be two filters — one over HIR types, one
//!   over extracted-IR types — that must agree field by field; a disagreement
//!   would emit the same number of binders in a different ORDER, and a theorem
//!   about one field would discharge a clause about another.
//! * `same_cst` — `result.<field>`. This is the exact fact the veripb client
//!   records as unstatable ("SATURATE leaves the degree alone" is
//!   `(satC c).degree = c.degree`). A parameter-side path is an opaque atom the
//!   clause may quantify over; `result` denotes the return value only through
//!   the E6 import, so projecting it means projecting the MINTED TERM — the
//!   aggregate carrier this increment does not build. Refused by name.
//! * `deep_degree` — the path is DEPTH 1. `c.inner.degree` names a scalar too,
//!   but nothing here can name the intermediate aggregate value.
//! * `tuple_field` — a TUPLE index is not a named field. The binding rows are
//!   named from the ADT's declared field names, so there is no `p.0` row to
//!   bind against and the clause fails the exact-binding gate.

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

pub struct Cst {
    pub degree: u64,
    pub coeff: u64,
}

pub struct Mixed {
    pub degree: u64,
    pub terms: [u64; 2],
}

pub struct Inner {
    pub degree: u64,
}

pub struct Outer {
    pub inner: Inner,
}

pub struct Pair(pub u64, pub u64);

pub fn via_reference(c: &Cst) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == ident_isl(c.degree) //~ ERROR uncited `ensures` naming the Clean island definition `ident_isl`
{
    c.degree
}

pub fn mixed_fields(c: Mixed) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == ident_isl(c.degree) //~ ERROR uncited `ensures` naming the Clean island definition `ident_isl`
{
    c.degree
}

pub fn same_cst(c: Cst) -> Cst
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result.degree == c.degree
{
    c
}

pub fn deep_degree(c: Outer) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == ident_isl(c.inner.degree) //~ ERROR uncited `ensures` naming the Clean island definition `ident_isl`
{
    c.inner.degree
}

pub fn tuple_field(p: Pair) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == ident_isl(p.0) //~ ERROR uncited `ensures` naming the Clean island definition `ident_isl`
{
    p.0
}

fn main() {}
