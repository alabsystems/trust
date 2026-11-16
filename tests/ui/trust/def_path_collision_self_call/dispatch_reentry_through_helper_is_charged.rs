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
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 6 (2026-10-08) — a forwarding impl that reaches the
//! implemented trait item ONE HOP AWAY, through a generic free helper, is charged.
//!
//! `impl<X: Tr> Tr for Box<X> { <X as Tr>::f(n) }` is charged since round 5 (D9's
//! `ImplementedTraitItem` class). Routing the same call through `helper::<X>` hid it from
//! every lane: `helper` implements nothing, and the `Box` body's call resolves to `helper`.
//! A downstream `impl Tr for Mine { <Box<Mine> as Tr>::f(n) }` (or a local one) makes it
//! recurse forever with the same `n`.
//!
//! MEASURED (level 2, JSON; review scratch `r9rev/probes/helper_lib.rs`): on the preview3
//! stage 1 (main `7be75e9a80`) and on round 5, rc 0 with NO termination row, while its
//! twin `direct_lib.rs` (no helper) gets round 5's D9 row. Round 6 charges the helper's
//! dispatched call: a local body that may serve `Tr::f` (the `Box` impl item) reaches
//! `helper` over the local call graph. This file FAILS on round 5 and on preview3 (no
//! warning on `helper`).
//!
//! `nocycle_helper` is the negative control: no local body that may serve `Up::g`
//! reaches it, so it carries no charge (not machine-checked here: compiletest cannot
//! require a warning's absence under `dont-require-annotations`; measured in scratch
//! `r10/probes/nocycle.rs`).

pub trait Tr {
    fn f(n: u64) -> u64;
}

fn helper<X: Tr>(n: u64) -> u64 {
    //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
    //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
    <X as Tr>::f(n)
}

impl<X: Tr> Tr for Box<X> {
    fn f(n: u64) -> u64 {
        if n == 0 {
            return 0;
        }
        helper::<X>(n)
    }
}

pub trait Up {
    fn g(n: u64) -> u64;
}

pub fn nocycle_helper<Y: Up>(n: u64) -> u64 {
    <Y as Up>::g(n)
}

impl Up for u8 {
    fn g(n: u64) -> u64 {
        n / 2
    }
}
