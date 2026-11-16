//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08) — pins the TRAIT-ITEM EXCEPTION of
//! `direct_self_call_identity_blocks` when the def path is unique.
//!
//! The where-clause self call below does not resolve (it names `Tr::f`), and it runs
//! THIS body with the same `n`. No other local function renders this def path, so the
//! compiler admits the call to vcgen's self-call lanes, which read it as a self call and
//! report the non-decreasing measure as `unknown` (the count below; the preview3 stage
//! 1, main `7be75e9a80`, reports the same). Dropping the exception would withdraw the
//! call from vcgen and leave only D9's `skipped` charge: a different count.

pub struct W<X>(pub X);
pub trait Tr {
    fn f(n: u64) -> u64
    where
        Self: Tr;
}

impl<X> Tr for W<X> {
    fn f(n: u64) -> u64
    //~^ NOTE 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 3 skipped out of 4 obligation(s)
    where
        Self: Tr,
    {
        if n == 0 {
            return 0;
        }
        <W<X> as Tr>::f(n)
    }
}
