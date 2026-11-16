//~ NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//@ revisions: advisory strict
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//! The compiler's per-function "Level 0 summary" and the row it PUBLISHES must
//! agree. `<T as Clone>::clone` through an open, uncontracted generic dispatch is
//! a Level-0 refutation (a downstream `impl Clone` may panic), which the summary
//! has counted `failed` since 7a127b0504. Measured on stage-1 b0b9258cc9
//! (origin/main, 2026-10-02): every lane printed "Level 0 summary: 1 failed" while
//! the transport row said `"outcome":"runtime_checked"` (JSON `failed: 0,
//! runtime_checked: 1`), so targo's advisory gate would conditional-pass the very
//! row the compiler called a refutation. Line 1 pins the published counts: the row
//! is `failed`, nothing is runtime-checked. The compile outcome is unchanged in
//! both lanes (advisory exit 0, strict exit 1). See KNOWN_HAZARDS ("the compiler's
//! \"Level 0 summary\" said `failed`") and `trust_types::l0_refutation`.
//!
//! OD-1 phase 1 (2026-10-04): the original subject, `impl<T: Clone> Clone for
//! Wrap<T>`, is now an ADMITTED instance-hypothesis site (open, uncontracted,
//! unresolved, on the impl's own parameter), so it publishes an
//! `assumption:instance-hypothesis` row and no refutation (the WARN pin). The
//! row/summary agreement this file guards is pinned on a NON-admitted open dispatch
//! instead: `<T as Tr>::m` handed a raw pointer stays class (c) of "L0 refutation
//! rows", and line 1 pins its published row exactly as it pinned the old one.
pub struct Wrap<T>(pub T);

impl<T: Clone> Clone for Wrap<T> {
    fn clone(&self) -> Self {
        //~^ WARN 1 instance hypothesis row(s)
        Wrap(self.0.clone())
    }
}

pub trait Tr {
    fn m(&self, p: *const u8) -> u32;
}

pub fn not_admitted<T: Tr>(t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~| ERROR Trust strict verification failed
    t.m(p)
}
