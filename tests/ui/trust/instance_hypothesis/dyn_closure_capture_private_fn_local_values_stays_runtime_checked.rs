//~ NOTE "line_start":29,"col_start":21,"line_end":29,"col_end":34},"outcome":"runtime_checked","solver":"trust-full-verifier"
//~| NOTE "line_start":38,"col_start":12,"line_end":38,"col_end":24},"outcome":"runtime_checked","solver":"trust-full-verifier"
//~| NOTE "line_start":44,"col_start":12,"line_end":44,"col_end":19},"outcome":"runtime_checked","solver":"trust-full-verifier"
//@ revisions: advisory
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! CLOSURE-CAPTURE-ROOT controls (2026-10-11, docs/DECISION_QUEUE.md): a closure's
//! capture of its parent's parameter is the caller's choice exactly when the PARENT's
//! argument is, under the rule a fn argument gets (DYN-ARG-PROVENANCE-1). Each row
//! here keeps the disclosed `runtime_checked` label:
//! (1) `private_parent` is private and its every call site passes `&|..| ..`, a closed
//!     local closure: no caller outside this crate exists, so no downstream value can
//!     reach the closure (the `dyn_private_fn_local_values_stays_runtime_checked.rs`
//!     precedent);
//! (2) `rebound` captures a `let` local, not the parameter: the walk declines every
//!     `let`-local capture, because the parent may have built that trait object (as
//!     `closure_upvar` does). Here the local IS the parameter, so this is a disclosed
//!     gap in the refuting direction (the row stays non-proved; strict and certify
//!     refuse it), not a claim that the value is the parent's own;
//! (3) `mut_param` captures a `mut` parameter the parent overwrites with its own
//!     closure before building the closure: the walk declines a mutable binding.
//! Line 1 pins each closure row by its location.
fn private_parent(xs: &[u32], keep: &dyn Fn(u32) -> bool) -> usize {
    xs.iter().filter(|x| keep(**x)).count()
}

pub fn use_private(xs: &[u32]) -> usize {
    private_parent(xs, &|x| x > 3) + private_parent(xs, &|x| x % 2 == 0)
}

pub fn rebound(p: &dyn Fn(u32) -> bool) -> bool {
    let d = p;
    let c = move || d(1);
    c()
}

pub fn mut_param(mut p: &dyn Fn(u32) -> bool) -> bool {
    p = &|x| x > 1;
    let c = || p(1);
    c()
}
