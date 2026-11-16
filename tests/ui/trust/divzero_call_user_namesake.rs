//@ revisions: usernames usernames_cert usernames_ms controls localdiv
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[usernames_cert] compile-flags: -Ztrust-policy=certify
//@[usernames_ms] compile-flags: -Ztrust-policy=memory-safe
//@[usernames] check-pass
//@[usernames_cert] check-pass
//@[usernames_ms] check-pass
//@[controls] check-fail
//@[localdiv] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[localdiv] dont-require-annotations: ERROR
//! A USER function merely NAMED like one of core's zero-divisor methods owes none of
//! that method's rows (DIVZERO-NAME-1; 2026-10-06).
//!
//! `trust_vcgen`'s `panic_calls::divzero_call` MINTS core's `divisor != 0` row on
//! arg 1 of a call to `div_euclid`, `div_ceil`, `rem_euclid` (a zero divisor panics)
//! and `Iterator::step_by` (a zero step panics). It decided the callee by its last
//! path segment alone, so a call to a user `Q::div_ceil(a, b) { a ^ b }`,
//! `Q::rem_euclid(a, b) { a | b }`, a free `rem_euclid(a, b) { a | b }` or
//! `div_euclid(a, b) { a & b }`, a user `S::step_by(&self, n) -> n`, a user trait's
//! `Euclid::rem_euclid`, or a TOTAL wrapper `util::div_ceil(a, b) { if b == 0 { 0 }
//! else { a.div_ceil(b) } }` was charged `[divzero]` / `[remzero]` over the user
//! function's own arguments and REFUTED at `a = 0, b = 0` — for functions that cannot
//! panic.
//!
//! It now mints the row only for core's own methods: `div_euclid` / `div_ceil` /
//! `rem_euclid` under an authenticated sysroot root (a `core::` / `alloc::` / `std::`
//! path with no `__trust_crate@` stamp; this keeps every core owner's row, `Wrapping`,
//! `Saturating` and `NonZero` included), and `step_by` only as std's
//! `Iterator::step_by` (a user iterator that inherits std's default included). The
//! fn-item deny-list keeps the old name-only answer.
//!
//! BEFORE (the stage 1 of `46e9afaf95`, `scratchpad/stage1-w21before`, measured
//! 2026-10-09 with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json -A unused`):
//! * `usernames` exits 1 with 14 errors: `p1`..`p6` and `a6` each read "Trust Level 0
//!   safety verification incomplete" and "Trust strict verification failed", on a
//!   `[divzero]` / `[remzero] FAILED` row (`p5` also carries a runtime-checked
//!   whole-function `[assert]` row that its renamed twin proves). `g1` passes.
//! * `usernames_cert` (`certify`) exits 1 with the same 14 errors.
//! * `usernames_ms` (`memory-safe`) exits 1 with one error, for `p5`: "at least one
//!   result is not an authenticated memory-safe assumption" (that `[assert]` row).
//! * The renamed twin of this file's `user` and `util` modules (every user callee
//!   renamed off core's names, bodies byte-identical; `scratchpad/w21div2/twin/
//!   divzero_twin.rs`) builds rc=0 on the same compiler with each `usernames*`
//!   revision's flags; so does `crates/trust-vcgen/tests/fixtures/
//!   user_namesake_divzero/renamed_divzero.rs` (`p1`..`p5`) under all three policies.
//!   With `util` compiled in under `memory-safe`, the twin's `a6` is refused ("not an
//!   authenticated memory-safe assumption") while the namesake's `a6` is admitted, so
//!   `util` is left out of `usernames_ms`: after the fix the namesake's `a6` is
//!   predicted to get its twin's verdict there, a refusal.
//! * `controls` exits 1 with exactly the 11 errors annotated below; `g2` passes.
//! * `localdiv` exits 1 with 8 errors: the callee bodies' own `a / b` and `a % b` are
//!   refuted (the annotated errors), and the callers `d3`/`d4` are refused too.
//!
//! AFTER (predicted; not built — the fix is in `crates/` only and needs a rebuilt
//! stage 1): the three `usernames*` revisions exit 0 — vcgen gives each caller exactly
//! its renamed twin's obligations (`crates/trust-vcgen/tests/
//! user_namesake_divzero_realmir.rs`). `controls` is unchanged. `localdiv` still exits
//! 1 through the callee bodies' own rows; whether `d3`/`d4` themselves keep an error
//! is not pinned.

// ---- usernames: user functions that share a name with core's methods ----

#[cfg(any(usernames, usernames_cert, usernames_ms))]
pub mod user {
    pub struct Q;
    impl Q {
        #[inline(never)]
        pub fn div_ceil(a: u32, b: u32) -> u32 {
            a ^ b
        }

        #[inline(never)]
        pub fn rem_euclid(a: u32, b: u32) -> u32 {
            a | b
        }
    }

    #[inline(never)]
    pub fn rem_euclid(a: u32, b: u32) -> u32 {
        a | b
    }

    #[inline(never)]
    pub fn div_euclid(a: u64, b: u64) -> u64 {
        a & b
    }

    pub struct S;
    impl S {
        #[inline(never)]
        pub fn step_by(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Euclid {
        fn rem_euclid(&self, v: &Self) -> Self;
    }
    impl Euclid for u8 {
        #[inline(never)]
        fn rem_euclid(&self, v: &Self) -> Self {
            *self ^ *v
        }
    }

    pub fn p1(a: u32, b: u32) -> u32 {
        Q::div_ceil(a, b)
    }

    pub fn p2(a: u32, b: u32) -> u32 {
        rem_euclid(a, b)
    }

    pub fn p3(a: u64, b: u64) -> u64 {
        div_euclid(a, b)
    }

    pub fn p4(s: &S) -> usize {
        s.step_by(0)
    }

    pub fn p5(x: u8, y: u8) -> u8 {
        Euclid::rem_euclid(&x, &y)
    }

    pub fn p6(a: u32, b: u32) -> u32 {
        Q::rem_euclid(a, b)
    }

    // Passes before and after: the guard discharged the (spurious) row.
    pub fn g1(a: u32, b: u32) -> u32 {
        if b != 0 { Q::div_ceil(a, b) } else { 0 }
    }
}

// A total wrapper around core's real `div_ceil`: its own body keeps core's row, which
// the `b == 0` guard proves; its CALLER owes nothing. Not in `usernames_ms` (see the
// header: the renamed twin's caller is refused under `memory-safe` for another reason).
#[cfg(any(usernames, usernames_cert))]
pub mod util {
    #[inline(never)]
    pub fn div_ceil(a: u32, b: u32) -> u32 {
        if b == 0 { 0 } else { a.div_ceil(b) }
    }

    pub fn a6(a: u32, b: u32) -> u32 {
        div_ceil(a, b)
    }
}

// ---- controls: core's own methods keep their rows ----

#[cfg(controls)]
pub fn c1(a: u32, b: u32) -> u32 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::c1`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `divzero_call_user_namesake::c1`: 3 obligation(s)
    a.div_ceil(b)
}

#[cfg(controls)]
pub fn c2(n: usize, k: usize) -> usize {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::c2`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `divzero_call_user_namesake::c2`: 3 obligation(s)
    (0..n).step_by(k).count()
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): `c3` and `c4` count 4. Beside the two
// FAILED division-family rows, the call into the bundled `rem_euclid`/`div_euclid` body now
// carries the counted panic-freedom aggregate (`runtime_checked`) and its member Assert an
// `unknown` row. Neither is reported a "guaranteed" violation any more: with both operands
// free parameters no violation is forced (trust-router `violation_is_forced` binds only the
// hypotheses' equalities, never the violation's own `b == 0`).
#[cfg(controls)]
pub fn c3(a: i64, b: i64) -> i64 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::c3`: 4 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `divzero_call_user_namesake::c3`: 4 obligation(s)
    a.rem_euclid(b)
}

#[cfg(controls)]
pub fn c4(a: i32, b: i32) -> i32 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::c4`: 4 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `divzero_call_user_namesake::c4`: 4 obligation(s)
    a.div_euclid(b)
}

// A user iterator that inherits std's `step_by`, which panics on a zero step.
#[cfg(controls)]
pub struct It(pub u32);

#[cfg(controls)]
impl Iterator for It {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        None
    }
}

#[cfg(controls)]
pub fn s1(k: usize) -> usize {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::s1`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `divzero_call_user_namesake::s1`: 2 obligation(s)
    // Re-pinned 2026-10-15: not a "guaranteed" violation. `k` is a free parameter, so
    // `step_by(k)` panics only for `k == 0` (the FAILED row's counterexample). The stage 1 of
    // the merge still printed it (the violation's own `k == 0` was harvested as a binding);
    // trust-router's `violation_is_forced` now binds only the hypotheses' equalities.
    It(0).step_by(k).count()
}

#[cfg(controls)]
pub fn g2(a: u32, b: u32) -> u32 {
    if b != 0 { a.div_ceil(b) } else { 0 }
}

// ---- localdiv: a user namesake that DOES divide is refused through its own body ----

#[cfg(localdiv)]
#[inline(never)]
pub fn div_ceil(a: u32, b: u32) -> u32 {
    //[localdiv]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::div_ceil`
    a / b
}

#[cfg(localdiv)]
pub fn d3(a: u32, b: u32) -> u32 {
    div_ceil(a, b)
}

#[cfg(localdiv)]
pub struct W;

#[cfg(localdiv)]
impl W {
    #[inline(never)]
    pub fn rem_euclid(a: u32, b: u32) -> u32 {
        //[localdiv]~^ ERROR Trust Level 0 safety verification incomplete for `divzero_call_user_namesake::W::rem_euclid`
        a % b
    }
}

#[cfg(localdiv)]
pub fn d4(a: u32, b: u32) -> u32 {
    W::rem_euclid(a, b)
}
