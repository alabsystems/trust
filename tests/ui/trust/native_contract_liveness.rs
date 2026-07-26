//@ revisions: spec_only word_collision ordinary_arg unused_assignment
//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@[spec_only] check-pass
//@[word_collision] check-fail
//@[ordinary_arg] check-fail
//@[unused_assignment] check-fail
//! Trust contract predicates are specification uses for the unused-variable
//! lint, but only for the exact parameter name. They must not suppress vanilla
//! Rust lints for identifier collisions, contract-free arguments, or
//! unrelated dead assignments in the function body.

#![allow(dead_code)]
#![deny(unused_assignments, unused_variables)]

#[cfg(spec_only)]
fn contract_only_inputs(pre: u32, post: u32) -> u32
    requires pre > 0
    ensures result <= post
{
    0
}

#[cfg(word_collision)]
fn whole_word_collision(
    x: u32, //[word_collision]~ ERROR unused variable: `x`
    max: u32,
)
    requires max > 0
{
}

#[cfg(ordinary_arg)]
fn ordinary_no_contract(
    ordinary: u32, //[ordinary_arg]~ ERROR unused variable: `ordinary`
) {
}

#[cfg(unused_assignment)]
fn assignment_lint_is_independent(mut spec_only: u32)
    requires spec_only > 0
{
    spec_only = 1; //[unused_assignment]~ ERROR value assigned to `spec_only` is never read
}

fn main() {}
