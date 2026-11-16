//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[off] forbid-output: Trust modeled fact
//! D2 tier 1 (2026-09-24): the CLOSURE-SIDE gate. The compiler's scan reads
//! only the parent, so it DOES install the premise here (`on` shows the
//! disclosure). But the closure reassigns its item (`w = &[]`) and then reads
//! `w[1]`, which always PANICS: the premise is about the parameter's ENTRY
//! value, and vcgen refuses to use it on a parameter that is ever written. The
//! bounds row must stay refuted in both revisions.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): `[slice] FAILED
//! … w__slice_len#s0_1 = 0` on the closure.
//!
//! (The `on` pin spells the disclosure without its leading `Trust modeled
//! fact` words on purpose: the `off` revision forbids that phrase, and a
//! rendered multi-line span can echo this very source line.)

pub fn item_reassigned(v: &[u32]) -> bool {
    v.windows(2).all(|mut w| {
        //~^ NOTE [slice] FAILED
        //[on]~^^ NOTE ADAPTER_YIELD: core `Iterator::all` over `<[T]>::windows(2)`
        w = &[];
        w[1] == 0
    })
}
