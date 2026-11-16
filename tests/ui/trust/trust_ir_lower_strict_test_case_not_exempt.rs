//@ needs-trust-verify
//@ revisions: test_case_const test_case_fn
//@ compile-flags: --test -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (CB4): `-Ztrust-ir-lower=strict`'s coverage exemption for harness
//! items (`rustc_mir_build::trust_ir_strict_coverage_applies`) is keyed on
//! PROVENANCE (`rustc_middle::middle::trust_test_harness`), not on
//! `#[rustc_test_marker]`. `#[test_case]` pushes that marker onto the AUTHOR's
//! own item, so the old "typeck root carries the marker" rule silenced the check
//! over code the author wrote — MEASURED (`spoof_tc.rs`, `spoof_tc_fn.rs`): the
//! marked `CASTS` / `casts` were NOT flagged while their byte-identical unmarked
//! twins were flagged with `Cast(borrow ptr operand)`. Now both of each pair are
//! flagged.
//!
//! The harness `main` IS synthesized (here it calls the author's runner) and is
//! now exempt from the coverage arm too: before CB4 it was not covered by the
//! exemption at all, and on a plain one-test crate under these flags it failed
//! with `REFUSED at crate assembly: UnsignableRustAbiDeclaration(…test_main_static)`
//! (MEASURED). No annotation names `main`, so an error on it fails this file.
//! The author's `runner` stays in scope like any other author body.
//!
//! MEASURED on the Track B stage 1 (2026-09-28): every error is annotated, and
//! none is on `main` or `runner`, in both revisions.
//!
//! 2026-10-01: `runner` now IS flagged, in both revisions, and that is a fix. Its
//! `for t in tests { .. }` used to pass strict only because the wave-ER for-loop
//! summary erased the loop — the lowered runner was `ret`, calling no test — and
//! reported the body clean. With the summary removed the loop must lower
//! faithfully, and the slice-iterator `next` has no lane yet, so the author's
//! runner is refused like any other author body (docs/KNOWN_HAZARDS.md, "CLOSED
//! 2026-10-01 — a `for` loop was ERASED"). `main` stays exempt.

#![feature(custom_test_frameworks)]
#![test_runner(crate::runner)]

#[cfg(test_case_const)]
pub fn runner(tests: &[&fn() -> bool]) {
    //[test_case_const]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    for t in tests {
        let _ = t();
    }
}

#[cfg(test_case_const)]
#[test_case]
pub const CASTS: fn() -> bool = || {
    //[test_case_const]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    !p.is_null()
};

#[cfg(test_case_const)]
pub const CASTS_UNMARKED: fn() -> bool = || {
    //[test_case_const]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    !p.is_null()
};

#[cfg(test_case_fn)]
pub fn runner(tests: &[&dyn Fn()]) {
    //[test_case_fn]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    for t in tests {
        t();
    }
}

#[cfg(test_case_fn)]
#[test_case]
pub fn casts() {
    //[test_case_fn]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    assert!(!p.is_null());
}

#[cfg(test_case_fn)]
pub fn casts_unmarked() {
    //[test_case_fn]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    assert!(!p.is_null());
}
