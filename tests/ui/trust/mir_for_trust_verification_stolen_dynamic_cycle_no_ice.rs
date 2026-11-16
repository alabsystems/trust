//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_BUNDLE_TRACE=1

//! **Regression: a callee whose elaborated MIR was already stolen by its own
//! still-running `optimized_mir` must degrade to the absent-callee marker, not
//! abort the build with `attempted to read from stolen value: Body`.**
//!
//! The ICE (lib.rs:540 on trustc `e4e923ef3`, 2026-07-21) was observed
//! compiling the third-party crate `regex-syntax 0.8.10` and on orca-alab's
//! workspace. `mir_for_trust_verification` did an unconditional
//! `mir_drops_elaborated_and_const_checked(def).borrow()`. That is only safe
//! for members of the STATIC mutual-recursion SCC, whose snapshot
//! `inner_optimized_mir` takes before it steals. But its consumers are routed
//! by `optimized_mir_query_would_cycle`, which also answers "yes" for any def
//! whose `optimized_mir` is live on the query stack — including a cycle the
//! local call graph cannot see because one edge runs through a FOREIGN
//! generic. Fixed by `775d74f050` (the query returns `Option`; `None` for a
//! stolen body that would cycle, and every consumer skips the callee); this
//! file is the regression test that commit did not land with.
//!
//! The cycle here: `c -> Into::into` (foreign blanket impl, bundled on the
//! monomorphic lane) `-> <Wrap as From<u32>>::from -> a -> b -> c`. The local
//! call graph has no `c -> from` edge, so none of these is in the static SCC
//! and no pre-steal snapshot exists. Callee-first demand order verifies `c`
//! first; its bundle reaches `from` through the instantiated `into` body, and
//! the nested verifications of `from`, `a` and `b` each ask for `c` while
//! `c`'s `optimized_mir` is in progress with its source already stolen.
//!
//! MEASURED 2026-09-23 on trustc `321aaeda7` and stage1 `ed48fd9d4`:
//! `TRUST_BUNDLE_TRACE=1` prints
//! `[BUNDLE_DROP] reason=no-mir-for-trust-verification callee=<this crate>::c`
//! three times. That reason is emitted ONLY on the `None` arm, and the query
//! returns `None` ONLY from its `is_stolen()` branch. `mir_for_trust_verification`
//! is a memoized (`no_hash`) query, so only the FIRST of the three lines is a
//! fresh read of the stolen body; the other two are cache hits of that `None`.
//! Before the fix, that first read was the unconditional `borrow()` that
//! panicked and aborted the build. Now the build passes, and `a`, `b` and
//! `from` stay "incomplete" rather than proved: the skipped callee costs
//! coverage and never grants a verdict.
//!
//! WHAT THIS FILE PINS, and how compiletest enforces each part:
//! * no ICE: `build-pass` (reverting the `is_stolen()` branch fails it);
//! * the stolen-body path is still reached: `TRUST_BUNDLE_TRACE=1` is set and
//!   the `RAW` annotation at the end of the file requires the
//!   `no-mir-for-trust-verification` trace line, so if the monomorphic lane
//!   stops bundling `Into`/`From` this test fails instead of passing vacuously;
//! * the skip never grants a verdict: `from`, `a`, `b` and `c` each carry a
//!   `WARN safety verification incomplete` annotation, and with no
//!   `dont-require-annotations` any other warning is unexpected, so a change
//!   that reported any of them as proved fails here.
//!
//! The derived-`PartialEq`-through-`Box` shape of the original regex-syntax
//! crash no longer reaches this path, because the monomorphic lane now declines
//! to bundle std `PartialEq`/`Clone`/`Debug`/... trait calls. That is why this
//! test uses `From`/`Into` to close the cycle and does not use `derive`.

pub struct Wrap(pub u32);

impl From<u32> for Wrap {
    fn from(x: u32) -> Wrap { //~ WARN safety verification incomplete
        Wrap(a(x))
    }
}

pub fn a(x: u32) -> u32 { //~ WARN safety verification incomplete
    if x == 0 { 0 } else { b(x - 1) }
}

pub fn b(x: u32) -> u32 { //~ WARN safety verification incomplete
    if x == 0 { 0 } else { c(x - 1) }
}

pub fn c(x: u32) -> u32 { //~ WARN safety verification incomplete
    if x == 0 {
        return 0;
    }
    let w: Wrap = (x - 1).into();
    w.0
}

//~? RAW reason=no-mir-for-trust-verification callee=
