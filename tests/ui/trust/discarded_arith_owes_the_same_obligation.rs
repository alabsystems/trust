//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! A DISCARDED arithmetic result owes the SAME obligation as its RETURNED twin.
//!
//! The asymmetry this pins against — "a value that flows to a return is proven,
//! and the same expression dropped goes unproven" — would be a completeness gap
//! of exactly the kind that keeps the untouched strict default out of reach, so
//! it is worth holding flat rather than re-deriving. Two mechanisms could
//! produce it: a VC generator that seeds from live values or return places (a
//! dropped temp has no consumer to seed from), or a dead-code/unused-assignment
//! pass that deletes the statement before obligations are generated. Neither is
//! present, and this fixture is what says so out loud.
//!
//! THE ARITHMETIC IS DELIBERATELY UNPROVABLE, and that is what makes the pin
//! self-checking. `u32 + u32` genuinely can overflow, so the honest verdict on
//! BOTH halves is a refutation, and under strict each one is a build error.
//! The ERROR is therefore evidence that the obligation EXISTS: if the discarded
//! half ever stopped owing one, its function would have nothing left to prove,
//! would compile CLEAN, and this fixture would go red on an unmatched
//! annotation. A provable pair could not do that job — a dropped obligation
//! leaves a function that passes VACUOUSLY, so `check-pass` would stay green in
//! exactly the case worth catching, and only a full `.stderr` count snapshot
//! could tell the two apart.
//!
//! Both halves must keep an annotation. One shared annotation would be
//! satisfied by whichever half still reports, which is the asymmetry itself.

pub fn returned(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust strict verification failed
    a + b
}

pub fn discarded(a: u32, b: u32) {
    //~^ ERROR Trust strict verification failed
    let _x = a + b;
}
