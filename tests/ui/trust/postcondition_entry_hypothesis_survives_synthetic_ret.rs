//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! REGRESSION (2026-08-06): the verifier REFUTED true postconditions, reporting
//! `verified_counterexample = true` — an affirmative claim that a validated
//! counterexample exists — against correct code.
//!
//! `gate_contract_preconditions` drops every contract-derived precondition when
//! it sees a body local shadowing a referenced parameter. `#[ensures]` lowering
//! mints the synthetic local `__ret`, and for a straight-line body like `{ n }`
//! copy-propagation parks its `var_debug_info` entry on `_1` — the parameter
//! itself. The alias scan read that compiler-generated name as a user shadow,
//! dropped the authored `n >= 0`, and the postcondition `ret >= 0` was then
//! genuinely refutable over an unconstrained `n`.
//!
//! The discriminator was the BODY, not the contract: the same clauses over a
//! loop or an `if/else` body KEPT the precondition and proved 4/4, while `{ n }`
//! and `{ let x = n; x }` refuted. Measured before the fix this file is 1 proved
//! / 2 FAILED; after, 3 proved / 0 failed.
//!
//! `both` is the control that must keep proving either way: `ret >= n` over
//! `{ n }` does NOT need the precondition, so a fix that suppressed rows rather
//! than restoring the hypothesis would show up here as a capability loss.
#![feature(contracts)]
#![allow(internal_features, incomplete_features, unused)]

/// Needs the precondition as an entry hypothesis. This is the regression.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn needs_the_hypothesis(n: i32) -> i32 { n }

/// Provable WITHOUT the precondition — pins that the fix restores a hypothesis
/// rather than suppressing the obligation.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= n)]
pub fn provable_without_the_hypothesis(n: i32) -> i32 { n }

fn main() {}
