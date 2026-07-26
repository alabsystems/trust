#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a `requires` clause ALONGSIDE an `ensures` whose predicate NEGATES.
// `requires(x > 0)` rules out `x == i32::MIN`, so the body's `-x` cannot overflow,
// and the negation postcondition `*r == -x` holds. Trust statically PROVES both the
// no-overflow obligation (discharged by the precondition) and the negation
// postcondition (the predicate's `-x` matches the body's `-x`). Default mode must
// fully discharge every obligation — superior to rustc's runtime contract checks.
#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r == -x)]
pub fn requires_negation_contract(x: i32) -> i32 {
    -x
}
