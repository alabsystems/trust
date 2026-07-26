//! The legacy attribute spellings only reach the lint as inert tool
//! attributes (the builtin `core::contracts::*` forms are consumed by
//! expansion), so the test registers `contracts` and `kani` as tools.
// The machine-applicable #[kani::harness] rename cannot COMPILE in this test
// environment (no kani crate is linked); the suggestion text is still asserted.
//@no-rustfix
#![feature(register_tool)]
#![register_tool(contracts)]
#![register_tool(kani)]
#![warn(clippy::trust_legacy_spec_sugar)]
#![allow(dead_code)]

#[contracts::requires(x > 0)]
//~^ trust_legacy_spec_sugar
fn requires_sugar(x: i32) -> i32 {
    x
}

#[contracts::ensures(|ret| *ret >= 0)]
//~^ trust_legacy_spec_sugar
fn ensures_closure_sugar(x: i32) -> i32 {
    x * x
}

// `old(..)` inside the predicate gets the primes-notation note.
#[contracts::ensures(|ret| *ret == old(x) + 1)]
//~^ trust_legacy_spec_sugar
fn ensures_old_sugar(x: i32) -> i32 {
    x + 1
}

// Any path spelling ending in `contracts::requires` is caught, not just the
// two-segment form. (The builtin `core::contracts::*` spelling is consumed by
// expansion before lints run, so it cannot appear here.)
#[kani::contracts::requires(x != 0)]
//~^ trust_legacy_spec_sugar
fn qualified_requires_sugar(x: i32) -> i32 {
    x
}

#[kani::proof]
//~^ trust_legacy_spec_sugar
fn legacy_harness() {}

// Kani's own contract attributes map to the same first-class signature clauses.
#[kani::requires(x > 0)]
//~^ trust_legacy_spec_sugar
fn kani_requires_sugar(x: i32) -> i32 {
    x
}

#[kani::ensures(|ret| *ret == old(x) + 1)]
//~^ trust_legacy_spec_sugar
fn kani_ensures_old_sugar(x: i32) -> i32 {
    x + 1
}

// The native harness attribute is NOT linted.
#[kani::harness]
fn native_harness() {}

// Other tool attributes with the same terminal segment are not contracts sugar.
#[kani::requires_nothing]
fn unrelated_attr() {}

fn main() {}
