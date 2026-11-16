//@ revisions: default certify guarded
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-fail
//@[certify] check-fail
//@[guarded] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SHIFT-BINDER-RESIDUE-1 (wave-23 review, 2026-10-11): the two shift-member
//! residues SELF-GUARDED-CONST-OPERAND-1 left, const-generic and place alike. In
//! each, the shift assert binder (trust-vcgen `checked_vcs.rs`,
//! `v2_shift_assert_binds_statement`) refused a canonical rustc chain, so the assert
//! lane fell to a generic `[overflow]` row and the statement-lane `[shift:*]` row,
//! sitting under the assert's own guard (UNSAT by construction), was never
//! suppressed: it read `proved` at the span of a shift that panics.
//!
//! * THE WIDTH (`rev_c`, `rev_p`). Both shifts shift the widthless `1` by the same
//!   amount, so the by-operands width recovery matched both and took the MINIMUM,
//!   8, for the first assert's `n < 64` too, and that assert never bound.
//!   `rev_c::<64>()` panics at the first shift ("attempt to shift left with
//!   overflow").
//! * THE SIGNED AMOUNT (`shl_ci`, `shl_s`). rustc checks a signed amount through a
//!   cast temporary (`_t = N as u32; _c = Lt(move _t, 32)`), and the binder compared
//!   `_t` with the shift's `N`. `shl_ci::<{ -1 }>(1)` panics.
//!
//! BEFORE (each revision's flags plus `--cfg <revision> --emit=metadata`, `nice -n
//! 19`, measured 2026-10-11), under default and certify alike, every function exits
//! 1 with a `proved` statement row beside a generic `[overflow]` FAILED row. On the
//! stage 1 of `999b006b87` (`integ/wave23`): `rev_c` and `rev_p` read `1 proved, 1
//! failed, … 1 runtime-checked`, `of which 1 kernel-certified`, `summary: 0 trusted,
//! 1 certified`; `shl_ci` and `shl_s` read `1 proved, 1 failed`, `summary: 1
//! trusted, 0 certified, 1 failed`. On the stage 1 of `5911b1325f`, `rev_c` reads `2
//! proved … of which 2 kernel-certified` (neither of its asserts bound) and the other
//! three read as above. On both, no function has a `[shift:left] FAILED` row,
//! `Trust verification: 0 proved,` or `summary: 0 trusted, 0 certified,` (counted:
//! zero occurrences of each), so every NOTE annotation below is absent before the
//! fix. `guarded` exits 0 on both.
//!
//! AFTER (the stage 1 built from this change): each shift carries exactly one row,
//! the assert lane's, built over the shift's own operands at its own width; the
//! FIRST shift of `rev_c`/`rev_p` and the shifts of `shl_ci`/`shl_s` are FAILED, the
//! second shift of `rev_c`/`rev_p` stays `runtime-checked` (its refutation is demoted,
//! as before), and no function has a proved or kernel-certified row. The `guarded`
//! twins are safe and still build.

#[cfg(not(guarded))]
pub fn rev_c<const N: u32>() -> (i64, i8) {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE Trust verification: 0 proved,
    //[default,certify]~| NOTE [shift:left] FAILED
    //[default,certify]~| NOTE summary: 0 trusted, 0 certified,
    (1i64 << N, 1i8 << N)
}

#[cfg(not(guarded))]
pub fn rev_p(s: u32) -> (i64, i8) {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE Trust verification: 0 proved,
    //[default,certify]~| NOTE [shift:left] FAILED
    //[default,certify]~| NOTE summary: 0 trusted, 0 certified,
    (1i64 << s, 1i8 << s)
}

#[cfg(not(guarded))]
pub fn shl_ci<const N: i32>(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE Trust verification: 0 proved,
    //[default,certify]~| NOTE [shift:left] FAILED
    //[default,certify]~| NOTE summary: 0 trusted, 0 certified,
    x << N
}

#[cfg(not(guarded))]
pub fn shl_s(x: u32, s: i32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE Trust verification: 0 proved,
    //[default,certify]~| NOTE [shift:left] FAILED
    //[default,certify]~| NOTE summary: 0 trusted, 0 certified,
    x << s
}

// Safe: the i64 shift under `N < 64`, the i8 one under `N < 8`.
#[cfg(guarded)]
pub fn rev_c_guarded<const N: u32>() -> (i64, i8) {
    if N < 64 { (1i64 << N, if N < 8 { 1i8 << N } else { 0 }) } else { (0, 0) }
}

#[cfg(guarded)]
pub fn shl_ci_guarded<const N: i32>(x: u32) -> u32 {
    if N >= 0 && N < 32 { x << N } else { x }
}

#[cfg(guarded)]
pub fn shl_s_guarded(x: u32, s: i32) -> u32 {
    if s >= 0 && s < 32 { x << s } else { x }
}
