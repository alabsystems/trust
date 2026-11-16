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
//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08) — pins the UNIQUENESS GUARD of the
//! trait-item exception in `direct_self_call_identity_blocks`.
//!
//! An unresolved call that names the trait item a body implements counts as "may run this
//! body" for vcgen's self-call lanes only while no other local function renders the
//! body's def path. Here the two impls' self types differ only in a lifetime
//! (`for<'a> fn(&'a u8) -> &'static u8` vs `for<'a> fn(&'a u8) -> &'a u8`), which the
//! printer canonicalizes to `'_`, so both render ONE def path, and no crate tag or alias
//! tag marks the call (it still mentions the parameter `X`). The where-clause call runs
//! the TWIN, which loops forever for an even `n`. Without the guard the call reads as a
//! self call and the descent `n - 1 < n` mints a PROVED "recursion measure `n` may not
//! decrease" row on a caller whose callee never returns. MEASURED (2026-10-08): the
//! preview3 stage 1 (main `7be75e9a80`, no `DefId` gate at all) reports
//! `2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 3 skipped out of 5`
//! here, the extra proved row being that termination row (level 2, JSON). With the
//! guard the call is not a self call, vcgen mints no termination row, and D9 charges the
//! call (an unresolved call to the implemented trait item, round 4) as unmeasured: the
//! annotated count, the warning, and the certify refusal.
#![allow(coherence_leak_check)]

pub struct W<X>(pub X);
pub trait Tr {
    fn f(n: u64) -> u64;
}

impl<X> Tr for W<(X, for<'a> fn(&'a u8) -> &'static u8)>
where
    W<(X, for<'a> fn(&'a u8) -> &'a u8)>: Tr,
{
    fn f(n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
        //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
        //[default]~^^^ NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 4 skipped out of 5 obligation(s)
        if n == 0 {
            return 0;
        }
        <W<(X, for<'a> fn(&'a u8) -> &'a u8)> as Tr>::f(n - 1)
    }
}

impl<X> Tr for W<(X, for<'a> fn(&'a u8) -> &'a u8)> {
    fn f(n: u64) -> u64 {
        let mut k = n;
        while k != 7 {
            k = k.wrapping_add(2);
        }
        k
    }
}
