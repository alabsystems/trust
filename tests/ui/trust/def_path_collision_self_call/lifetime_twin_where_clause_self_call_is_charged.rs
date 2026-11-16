//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[certify] dont-require-annotations: ERROR
//@[default] forbid-output: this function has no obligation of its own
//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08) — a lifetime-only twin impl shares the
//! def path with no crate tag at all; a where-clause self call is still charged.
//!
//! `W<(X, for<'a> fn(&'a u8) -> &'static u8)>` and `W<(X, for<'a> fn(&'a u8) -> &'a u8)>`
//! are distinct types (two impls), but render one def path. The call below is an
//! unresolved where-clause call that runs THIS body with the same `n`, forever.
//! MEASURED (level 2, JSON, `selfbound_alias.rs`): no termination row on the preview3
//! stage 1 (main `7be75e9a80`) or on round 3, rc 0 on both. Round 4's D9 census counts
//! the unresolved trait-item call and charges it.
#![allow(coherence_leak_check)]

pub struct W<X>(pub X);
pub trait Tr {
    fn f(n: u64) -> u64
    where
        Self: Tr;
}

impl<X> Tr for W<(X, for<'a> fn(&'a u8) -> &'static u8)> {
    fn f(n: u64) -> u64
    //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
    //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
    where
        Self: Tr,
    {
        if n == 0 {
            return 0;
        }
        <W<(X, for<'a> fn(&'a u8) -> &'static u8)> as Tr>::f(n)
    }
}

impl<X> Tr for W<(X, for<'a> fn(&'a u8) -> &'a u8)> {
    // The twin makes no call and owns no obligation, so it publishes `no_obligations`
    // and passes. Its rendered path is the self-calling impl's above; when the zero-row
    // negative finding was keyed by that path, the self call's finding refused THIS
    // body too (ZERO-ROW-GATE pinned it as an ERROR). Keyed by the owner `DefId`
    // (ARGS-FINGERPRINT-READ-1, docs/DECISION_QUEUE.md), it stays with its owner; the
    // `forbid-output` above fails if a finding crosses to a same-rendered body again.
    fn f(n: u64) -> u64
    where
        Self: Tr,
    {
        n
    }
}
