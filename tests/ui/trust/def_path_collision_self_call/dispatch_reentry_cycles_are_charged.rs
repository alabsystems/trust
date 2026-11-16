//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 6 (2026-10-08) — cycles that leave a body through trait
//! dispatch and come back through ANOTHER local body are charged on the dispatching body.
//!
//! * `Box<X>: Tr` calls `<X as Other>::g`; `impl Other for u8` calls
//!   `<Box<u8> as Tr>::f`: `Box<u8>::f -> u8::g -> Box<u8>::f`, same `n`, forever
//!   (review scratch `r9rev/probes/crosstrait.rs`).
//! * `Wrap<X>: Tr2` forwards from a CLOSURE in its body; `impl Tr2 for u16` calls
//!   `<Wrap<u16> as Tr2>::h`: the closure re-enters through the `u16` impl
//!   (`r9rev/probes/closure.rs`).
//!
//! MEASURED (level 2, JSON): on the preview3 stage 1 (main `7be75e9a80`) and on round 5,
//! NO termination row on any of these bodies. Both shapes also fail the default lane for
//! reasons unrelated to termination (the re-entering impl's instance discharge; the
//! closure's unproved Level-0 row), so this file is `check-fail` on both revisions and
//! pins only the termination diagnostics.

pub trait Tr {
    fn f(n: u64) -> u64;
}

pub trait Other {
    fn g(n: u64) -> u64;
}

impl<X: Other> Tr for Box<X> {
    fn f(n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
        //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
        if n == 0 {
            return 0;
        }
        <X as Other>::g(n)
    }
}

impl Other for u8 {
    fn g(n: u64) -> u64 {
        <Box<u8> as Tr>::f(n)
    }
}

pub trait Tr2 {
    fn h(n: u64) -> u64;
}

pub struct Wrap<X>(X);

impl<X: Tr2> Tr2 for Wrap<X> {
    fn h(n: u64) -> u64 {
        if n == 0 {
            return 0;
        }
        let c = |m: u64| <X as Tr2>::h(m);
        //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
        //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
        c(n)
    }
}

impl Tr2 for u16 {
    fn h(n: u64) -> u64 {
        <Wrap<u16> as Tr2>::h(n)
    }
}
