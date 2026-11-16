//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory -Airrefutable_let_patterns --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-LV, the NEGATIVE pin): shapes the by-value enum `if let` lane must
//! keep REFUSING, each for a measured reason.
//!
//! A SINGLE-VARIANT enum has no discriminant to test: rustc compiles the test
//! away, so the built MIR carries no `switchInt` while this lane would emit
//! `Inst::Switch`. Under `-Ztrust-ir-lower=strict` the producer re-derives MIR
//! from its own trust-ir and compares it to the built MIR, so such a body would
//! report `clean` and still be strict-RED. That is exactly the failure that cost
//! the tuple-match or-pattern lane its landing on 2026-08-31 (built
//! `switch(disc(isize,fld(a1,0)))` vs derived `return c:uint:7:w32`), and the
//! clean metric cannot see it. The gate refuses with
//! `IfLetValue(single-variant enum)`; these bodies pin that refusal.

#[repr(u8)]
pub enum One {
    A,
}
#[repr(u8)]
pub enum OneP {
    A(i32),
}
pub fn single_variant_niladic(o: One) -> i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    if let One::A = o { 1 } else { 0 }
}
pub fn single_variant_payload(o: OneP) -> i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    if let OneP::A(x) = o { x } else { 0 }
}
