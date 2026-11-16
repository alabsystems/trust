//@ needs-trust-verify
//@ revisions: plain requires
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_REG_TRACE=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A verdict CONDITIONAL on a bundled std member's runtime check is never
//! registry authority (2026-09-29, corrections C1 and S5 of the Track R design).
//!
//! `filter().count()` keeps core's `<usize as Sum>::sum::{closure#0}` in the
//! bundle under the runtime-checked disposition. Whatever the rest of the run
//! proves, the function's panic-freedom rests on that member's own runtime check,
//! so it must not enter `panic_free_proven_funcs` (a caller would EVICT it from
//! its bundle and discharge the call, dropping the member rows out of the caller
//! too), the Part-B conditional registry, or the R40 zero-obligation fixpoint.
//!
//! * `plain`: `r` (a `RefCell::borrow_mut` beside the count) and its caller `h`.
//!   Before (stage-1 `f6773df328e`, m3 debug std and release-like std):
//!   `[PF_REG] fn=c::r established=true` — `r` was REGISTERED panic-free on a
//!   discarded bundle, and a verify-off `main` holding a `borrow()` then calling
//!   `h` panicked "RefCell already borrowed" (exit 101).
//! * `requires`: `r2` carries a declared `requires d != 0`, so its route is the
//!   Part-B conditional registry (correction C1: that branch had no
//!   conditional-std conjunct). Before: `call_r2`'s `[PF_REG] … established=true`
//!   and `call_r2` counted verified (1 of 1 proved), its call discharged against
//!   `r2`'s conditional registration.
//!
//! Pinned: the trace line the registration gate prints when it withholds, for
//! the function AND its caller (the caller's own bundle keeps the member, so its
//! verdict is conditional too). A body whose registration is withheld for this
//! reason also has its R40 candidacy revoked and is declined by the premise
//! authenticator (`verdict_rests_on_user_axiom`). Only the authenticator's pure
//! core has a unit test (`runtime_checked_std_member_verdict_is_declined_even_
//! when_axiom_free`, in `trust_verify/tests.rs`). The rest is DEFENSIVE and no
//! test observes it: the two `!conditional_std` registration conjuncts, the R40
//! poisoning and revocation, the `record_runtime_checked_std_member_verdict` call
//! and `trait_panic_free`'s early refusal. In every measured kept bundle the
//! aggregate row is runtime-checked, so `established` is already false; the Track
//! R review removed all of them together and no ui test, unit test or probe
//! changed (docs/KNOWN_HAZARDS.md, the CLOSED 2026-09-29 entry).
use std::cell::RefCell;

pub enum Tag {
    A,
    B,
}

#[cfg(plain)]
pub fn r(t: Tag, v: &[u32; 3], c: &RefCell<u32>) {
    let k = v.iter().filter(|x| **x > 1).count();
    let n = match t {
        Tag::A => 1usize,
        Tag::B => 2usize,
    };
    if k == 7 || n == 7 {
        return;
    }
    *c.borrow_mut() = 1;
}

#[cfg(plain)]
pub fn h(c: &RefCell<u32>) {
    r(Tag::A, &[1, 2, 3], c);
}

#[cfg(requires)]
pub fn r2(v: &[u32; 3], d: u32) -> u32 requires d != 0 {
    let k = v.iter().filter(|x| **x > 1).count();
    if k == 7 {
        return 0;
    }
    10 / d
}

#[cfg(requires)]
pub fn call_r2(v: &[u32; 3]) -> u32 {
    r2(v, 3)
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): the counted panic-freedom aggregate now
// carries the member's Assert, so no member is recorded under the runtime-checked disposition
// and the "registration withheld: conditional on" trace no longer prints. What this file pins
// is unchanged and still read directly: none of the four is registered (`established=false`),
// because each publishes that aggregate as an unproved `runtime_checked` row — the case the
// paragraph above already names ("the aggregate row is runtime-checked, so `established` is
// already false").
//[plain]~? RAW [PF_REG] fn=std_member_runtime_check_not_registered::r established=false
//[plain]~? RAW [PF_REG] fn=std_member_runtime_check_not_registered::h established=false
//[requires]~? RAW [PF_REG] fn=std_member_runtime_check_not_registered::r2 established=false
//[requires]~? RAW [PF_REG] fn=std_member_runtime_check_not_registered::call_r2 established=false
