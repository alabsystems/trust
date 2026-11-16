//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`: the aux's crate NAME is its file stem, which is this crate's name too:
// Cargo's bin+lib layout, where a package's bin links its own lib.
//@ aux-crate: other=binlib_where_clause_self_call_is_charged.rs
//@ revisions: default certify
//@ compile-flags: --crate-type lib -Ztrust-verify=on -Cmetadata=bin
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[certify] dont-require-annotations: ERROR
//@[default] forbid-output: this function has no obligation of its own
//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08) — a WHERE-CLAUSE self call whose def
//! path another local body shares is still charged.
//!
//! The method's own `where Self: Tr` puts `W<(X, other::T)>: Tr` in the param env, so
//! the genuine self call below does not resolve: it names the trait item `Tr::f`. It
//! runs THIS body with the same `n`, forever. The twin impl for `W<(X, T)>` renders the
//! same def path (the lib and this crate share a name), so round 3's `DefId` gate
//! withdrew the call from vcgen's self-call lanes (the trait-item exception requires a
//! unique path) — and D9's census counted only `Item(own) | Unresolved(own)`, so
//! nothing charged it. MEASURED (two `dupty` crates, `selfbound_dup.rs`, level 2,
//! JSON): the preview3 stage 1 (main `7be75e9a80`) had an `unknown` "recursion measure
//! `n` may not decrease" row; round 3 had NO termination row and built rc 0.
//!
//! Round 4: D9's census counts every unresolved call to the trait item this body
//! implements (unless its self type is a proper subterm of the impl's), so the call is
//! charged an `assumption:termination-unmeasured` row (the `skipped` one below).

pub struct T;
pub struct W<X>(pub X);
pub trait Tr {
    fn f(n: u64) -> u64
    where
        Self: Tr;
}

impl<X> Tr for W<(X, other::T)> {
    fn f(n: u64) -> u64
    //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
    //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
    where
        Self: Tr,
    {
        if n == 0 {
            return 0;
        }
        <W<(X, other::T)> as Tr>::f(n)
    }
}

impl<X> Tr for W<(X, T)> {
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
