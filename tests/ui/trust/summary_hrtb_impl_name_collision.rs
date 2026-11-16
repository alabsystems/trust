//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SUMMARY-NAME-COLLIDE-1 (wave 16, 2026-10-05) — A BODY-DERIVED CALLEE
//! SUMMARY KEYED BY A RENDERED NAME TWO IMPLS SHARE.
//!
//! EVERY ANNOTATED CALLER MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! # The defect
//!
//! The return upper-bound, lower-bound, const-set, discriminant, trivial-setter
//! and bool-predicate summaries each read a callee's BODY and hand every call
//! site a fact about the call, keyed by the callee's rendered `def_path`. That
//! rendering canonicalizes every lifetime to `'_`, but rustc keeps the two impls
//! below apart: their self types differ only in a region under a `for<>` binder
//! (the `coherence_leak_check` future-compatibility warning, rust#56105). Both
//! impls' methods render `<…::W<for<'_> fn(&'_ u8) -> &'_ u8> as …::Tr>::get`
//! (and `::big`, `::den`, …), and each lane kept whichever body came last. Every
//! caller below runs the FIRST impl and was handed the SECOND impl's summary.
//!
//! BEFORE (stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05):
//!
//! | revision | exit | rows |
//! |---|---|---|
//! | `default` | 0 | `const_set`/`upper_bound` `[overflow:add]`, `lower_bound` remainder-by-zero, `bool_pred` and `disc` `Call::unwrap` panic-freedom, `setter`'s assert: all `proved` |
//! | `certify` | 1 | the same rows `proved`, one row in each function but `setter` kernel-certified by the Clean kernel; only `disc` refused, for its separate `runtime_checked` panic-freedom row |
//!
//! `TRUST_RETURN_SUMMARY_DEBUG` showed `upper=[(…::big, 100), (…::den, 2),
//! (…::get, 1)]`: the second impl's bounds under the shared keys.
//! `summary_hrtb_impl_name_collision_run.rs` is the run-time witness: the first
//! impl's `get(u32::MAX) + 1` overflows.
//!
//! # The fix
//!
//! `trust_verify::body_summary_key_collisions` renders EVERY local body owner
//! (`mir_keys`) with the extractor's own renderer and refuses, in every lane and
//! in D5-B, a key two owners share; `trust_vcgen`'s `summary_candidates` applies
//! the same rule to the bodies each lane is given.
//!
//! AFTER: not built when this file was written (FIX PREPARED 2026-10-05). The
//! annotations are what the BEFORE compiler prints for this file with the second
//! impl's self type changed to the non-colliding `W<u8>` (one line, so every
//! annotation keeps its line): no summary reaches the callers, so each is
//! refused as it is with no sibling (`[overflow:add] failed` by ay). `setter`
//! is refused under certify only; the default policy keeps its assert as a
//! `runtime_checked` row, a warning. If an annotated row proves again, a shared
//! key has started to lend a summary.

pub struct W<T>(pub T);

pub trait Tr {
    fn get(x: u32) -> u32;
    fn big() -> u32;
    fn den(x: u32) -> u32;
    fn opt(x: u32) -> Option<u32>;
    fn set(p: &mut u32, v: u32);
    fn has(o: Option<u32>) -> bool;
}

// The impl every caller below runs.
impl Tr for W<for<'a> fn(&'a u8) -> &'static u8> {
    fn get(x: u32) -> u32 {
        x
    }
    fn big() -> u32 {
        core::hint::black_box(4_000_000_000)
    }
    fn den(x: u32) -> u32 {
        x
    }
    fn opt(_x: u32) -> Option<u32> {
        None
    }
    fn set(p: &mut u32, v: u32) {
        *p = v ^ 1;
    }
    fn has(_o: Option<u32>) -> bool {
        core::hint::black_box(true)
    }
}

// Its sibling: a distinct impl, every method of which renders the same key.
impl Tr for W<for<'a> fn(&'a u8) -> &'a u8> {
    fn get(_x: u32) -> u32 {
        1
    }
    fn big() -> u32 {
        100
    }
    fn den(x: u32) -> u32 {
        if x > 3 { 1 } else { 2 }
    }
    fn opt(x: u32) -> Option<u32> {
        Some(x)
    }
    fn set(p: &mut u32, v: u32) {
        *p = v;
    }
    fn has(o: Option<u32>) -> bool {
        o.is_some()
    }
}

type S = W<for<'a> fn(&'a u8) -> &'static u8>;

// Const-set summary `{1}`.
pub fn const_set(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    <S as Tr>::get(x) + 1
}

// Upper-bound summary `<= 100`.
pub fn upper_bound() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    <S as Tr>::big() + 4_000_000_000
}

// Lower-bound summary `>= 1`.
pub fn lower_bound(h: u32, x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    h % <S as Tr>::den(x)
}

// Discriminant summary: always `Some`.
pub fn disc(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    <S as Tr>::opt(x).unwrap()
}

// Trivial-setter summary `*p = v`.
pub fn setter(v: u32) -> u32 {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    let mut a = 0;
    <S as Tr>::set(&mut a, v);
    assert!(a == v);
    a
}

// Bool-predicate summary `ret == o.is_some()`.
pub fn bool_pred(o: Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if <S as Tr>::has(o) { o.unwrap() } else { 0 }
}
