//@ revisions: dep_read dep_ub dep_verified sysroot_call local_call dep_const
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: memory_safe_unverified_dep.rs
//@ aux-build: requires_callee_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=memory-safe --crate-type lib
//@[dep_read] check-fail
//@[dep_ub] check-fail
//@[dep_verified] check-fail
//@[sysroot_call] check-fail
//@[local_call] check-pass
//@[dep_const] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The CLASSIFIER-SKIP twin of `reject_lowering_gap_launders_uncharged_callee.rs`
//! (docs/KNOWN_HAZARDS.md, the 2026-09-30 fn-pointer `requires` residuals entry,
//! "L2 through a classifier skip").
//!
//! Under `-Ztrust-policy=memory-safe` a body with no `unsafe` that the classifier
//! cannot model — one safe `let _q = &raw const s.a;` is `AddressOfField` — was
//! admitted as ONE authenticated `assumption:addr-of-field` row, on the premise that
//! such a body leaves only its own panic-freedom undischarged. A skipped body
//! charges none of its calls, so the premise fails for a call into code that has no
//! verdict here: the absent-callee row memory-safe refuses when it can verify the
//! body, and the call the `assumption:native-lowering` collapse may not stand for
//! (`native_lowering_collapse_uncharged_edges`). Adding the unmodelled construct
//! turned a refusal into a pass.
//!
//! BEFORE (stage 1 of `fbc6068e3`, measured 2026-09-30 with these bodies):
//! `dep_read` (a verify-off dependency's safe `deref_raw`, `unsafe { *p }`),
//! `dep_ub` (its `get`, `unreachable_unchecked`) and `dep_verified` (a VERIFIED
//! dependency's `add1_wrapping`) built exit 0 with only the `Trust: ASSUMPTION
//! [addr-of-field]` line; each without the borrow is refused. The controls built
//! exit 0.
//!
//! AFTER (predicted; no stage 1 with the change was built): the demotion is
//! withheld on a masked fail-closed source (`uncharged_callable::
//! memory_safe_skip_withheld`), so those three are refused as the skip is on every
//! other fail-closed lane, the policy note naming the reason. A sysroot call the
//! lane admits either way (`sysroot_call`), a local call (`local_call`) and a
//! dependency's CONSTANT (`dep_const`, not a call) keep compiling. NOT closed: a
//! skipped body still stands for a sysroot callee's panics (`std::process::exit`,
//! `Vec::push`), which memory-safe refuses unskipped — OPEN in docs/KNOWN_HAZARDS.md.
//!
//! MERGED onto main (integ/stage1-batch4, 2026-10-02): main's own rule for this skip
//! (`memory_safe_assumption_uncharged_edges`, 631b03f8ea;
//! `reject_classifier_skip_launders_uncharged_callee.rs`) withholds the demotion for
//! ANY call that does not resolve to a local verified item, a sysroot call included —
//! the "NOT closed" item above, closed there. Both rules are asked and the note
//! carries each reason that fires, so the three refusals keep their notes;
//! `sysroot_call` (`u32::checked_add`) is now refused by main's rule, so it is
//! check-fail. `local_call` and `dep_const` stay admitted under both. Not run.

extern crate memory_safe_unverified_dep as dep_off;
extern crate requires_callee_dep as dep;

pub struct S {
    pub a: u32,
}

#[cfg(dep_read)]
pub fn p(s: &S, q: *const u32) -> u32 {
    //[dep_read]~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_unverified_callee::p`
    //[dep_read]~| NOTE so it cannot stand for a masked fail-closed source — code no verdict in this compilation covers
    let _q = &raw const s.a;
    dep_off::deref_raw(q)
}

#[cfg(dep_ub)]
pub fn p(s: &S) -> u32 {
    //[dep_ub]~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_unverified_callee::p`
    //[dep_ub]~| NOTE so it cannot stand for a masked fail-closed source — code no verdict in this compilation covers
    let _q = &raw const s.a;
    dep_off::get()
}

#[cfg(dep_verified)]
pub fn p(s: &S, y: u32) -> u32 {
    //[dep_verified]~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_unverified_callee::p`
    //[dep_verified]~| NOTE so it cannot stand for a masked fail-closed source — code no verdict in this compilation covers
    let _q = &raw const s.a;
    dep::add1_wrapping(y)
}

#[cfg(sysroot_call)]
pub fn p(s: &S, y: u32) -> Option<u32> {
    //[sysroot_call]~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_unverified_callee::p`
    //[sysroot_call]~| NOTE checked_add` in bb
    let _q = &raw const s.a;
    y.checked_add(1)
}

#[cfg(local_call)]
fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
#[cfg(local_call)]
pub fn p(s: &S, y: u32) -> u32 {
    let _q = &raw const s.a;
    twice(y)
}

#[cfg(dep_const)]
pub fn p(s: &S, y: u32) -> u32 {
    let _q = &raw const s.a;
    y ^ dep_off::SCALE
}
