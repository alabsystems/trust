//! Trust: trust-spec contract clauses (`#[trust::requires]` /
//! `#[trust::ensures]`) written in spec vocabulary — `result`, `old()`,
//! `forall`, `exists`, `==>` — are OPAQUE to rustc: span-only verifier
//! metadata that is never name-resolved or type-checked, while plain,
//! typeable payloads (bool-expression requires over parameters, `|ret| ...`
//! closure ensures) keep the upstream typed contract lowering.
//!
//! Regression test for the rust-1.99 migration collision where Trust-origin
//! bool-expression ensures clauses were routed into upstream's closure-based
//! `core::contracts::build_check_ensures` (E0277: "expected an `Fn(&_)`
//! closure, found `bool`") and spec-only names hit E0425.
//@ check-pass
//@ proc-macro: trust.rs
//@ edition: 2021

// Spec-vocabulary clauses: opaque lane (would be E0425/E0277 if typed).
#[trust::requires(
    amount > 0
        && old(balance) >= amount
        && forall(|idx: usize| idx < history.len() ==> history[idx] >= 0)
)]
#[trust::ensures(
    result == old(balance) - amount
        && exists(|idx: usize| idx < ledger.len() && ledger[idx] == amount)
)]
fn withdraw(balance: i32, amount: i32) -> i32 {
    balance - amount
}

// `result`-sugar ensures beside a typeable requires: the requires keeps the
// typed lane; the ensures is opaque.
#[trust::requires(denominator != 0)]
#[trust::ensures(result * denominator == numerator)]
fn divide_exact(numerator: i32, denominator: i32) -> i32 {
    numerator / denominator
}

// Fully typeable trust-spec clauses: both stay on the upstream typed lane.
#[trust::requires(x > 0)]
#[trust::ensures(move |r: &i32| *r > 0)]
fn typed_lane(x: i32) -> i32 {
    x
}

fn main() {
    assert_eq!(withdraw(10, 3), 7);
    assert_eq!(divide_exact(10, 2), 5);
    assert_eq!(typed_lane(1), 1);
}
