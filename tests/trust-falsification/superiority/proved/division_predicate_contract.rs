#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a DIVISION in the postcondition predicate `*r == x / 2`. The
// contract-predicate lowering now emits `/` (previously Div/Rem were dropped,
// making the predicate unsupported and fail-closing a valid contract). The
// predicate's `x / 2` term matches the body's identical division, so the
// postcondition discharges (the terms cancel — UNSAT of `_0 == x/2 AND _0 != x/2`),
// and the constant divisor 2 makes the body's div-by-zero/overflow checks trivial.
// Default mode must fully discharge every obligation.
#[core::contracts::ensures(move |r: &i32| *r == x / 2)]
pub fn division_predicate_contract(x: i32) -> i32 {
    x / 2
}
