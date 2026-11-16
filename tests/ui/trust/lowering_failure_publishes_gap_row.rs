//~ NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "functions_analyzed":1,"functions_verified":0,"total_proved":1,"total_failed":0,"total_unknown":1
//@ revisions: advisory default strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[default] check-fail
//@[strict] check-fail
//@[certify] check-fail
//! A native typed-TrustIr lowering that does not complete is a coverage gap in
//! EVERY lane that publishes counts, not only under the memory-safe demotion (which
//! publishes its own `assumption:native-lowering` collapse or gap row). A safe WRITE
//! to a union field stops the lowering ("field projection on union ... requires a
//! trust-ir union representation"), so the one VC row the layer could see (the
//! guarded `v[i]` bounds check, proved) does not cover the function.
//!
//! Measured on stage-1 9212a4cd18 (origin/main, 2026-09-30), direct trustc
//! `-Ztrust-verify=on -Ztrust-verify-output=both`: advisory rc=0 with NO warning,
//! "1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1
//! obligation(s)", the JSON `proved: 1, total: 1` and the crate summary
//! `functions_verified: 1`; the default lane, strict and certify refused it ("native
//! typed-TrustIr lowering did not complete") beside the SAME JSON. Every one of these
//! lanes now publishes one `native-verification-gap` row (unknown) for the failure,
//! the crate summary no longer counts the function verified, and the human line
//! counts the published rows. Lines 1-2 pin the JSON (compiletest reads the
//! span-less `TRUST_JSON:` transport notes there).
//!
//! The shape this file first pinned (`v[i]` on a `&Vec<u32>`, whose bundle refused
//! the `<usize as SliceIndex<[u32]>>::index` member) no longer fails the lowering on
//! 9212a4cd18: the W4 Vec-index forwarder lane owns that member, and the body now
//! publishes "2 proved … 1 runtime-checked out of 3" in every lane.
pub union U {
    pub a: u32,
    pub b: f32,
}

pub fn f(u: &mut U, v: &[u32], i: usize) {
    //[default,strict,certify]~^ ERROR native typed-TrustIr lowering did not complete
    //~^^ NOTE 1 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    if i < v.len() {
        u.a = v[i];
    }
}
