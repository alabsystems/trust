//@ needs-trust-verify
//@ proc-macro: trust.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! An attribute `requires` has no result binding, so `result` in it must be
//! refused where the text is first parsed, not lowered as the return place.
//!
//! `requires` is the one clause kind whose predicate is ASSUMED at definition
//! entry. Before the refusal, `#[trust::requires(result == 0)]` lowered to
//! `Eq(_0, 0)` through the generic identifier arm of the contract snippet
//! parser, and only the later `contract_assumption_gate` stopped it being
//! assumed: a warning ("predicate references `_0`, which is not a parameter"),
//! an "assumed (requires)" row, and a green build. The native lane refuses the
//! same spelling outright (tests/ui/trust/typed_citation_result_scope.rs).
//!
//! Now the clause does not lower, it stays an unsupported contract, and strict
//! verification fails closed on it. `control` is the same shape over a
//! parameter and keeps lowering and being assumed.
//!
//! (`_0` cannot be pinned here: the attribute payload is name-resolved as Rust
//! first, so `_0` is E0425 before the contract query sees it. The unit test
//! `attribute_requires_refuses_the_return_place_vocabulary` covers `_0`.)

extern crate trust;

#[trust::requires(result == 0)]
pub fn names_the_return_place(a: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `attribute_requires_result_refused::names_the_return_place`
    //~| ERROR Trust strict verification failed for `attribute_requires_result_refused::names_the_return_place`
    a
}

#[trust::requires(a > 0)]
pub fn control(a: u32) -> u32 {
    a
}
