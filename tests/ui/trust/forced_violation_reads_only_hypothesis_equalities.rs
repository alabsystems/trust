//@ revisions: possible forced
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[possible] forbid-output: guaranteed Level 0 safety violation
//! FORCED-OWN-EQ-1 (docs/KNOWN_HAZARDS.md, FIXED 2026-10-15): "Trust verification found N
//! guaranteed Level 0 safety violation(s)" means the violation holds on EVERY reaching
//! execution. `trust_router::violation_is_forced` folded the formula after binding every
//! `x == c` it found, the violation's own atom included, so a divisor or size that is a
//! free parameter (`windows(k)`: the row's core is `k == 0`) was bound to the value that
//! makes it panic and reported guaranteed. It now binds only the HYPOTHESES' equalities
//! (every conjunct off the violation spine), plus one value for a variable that only a
//! hypothesis range atom mentions.
//!
//! * `possible`: each function panics for some inputs and not others, so each is refused
//!   (its row is FAILED) and none may be reported guaranteed (the forbid). BEFORE (the
//!   stage 1 of the 2026-10-14 merge): `win_k`, `guarded` and `free_abs` each carried the
//!   "guaranteed" error.
//! * `forced`: each panics on every run, and each keeps the label: a ground core
//!   (`i32::MIN.abs()`, `100 / 0`), a definition before the core (`let k = 0`, `let x: u8 =
//!   255`), a path fact before the core (`if k == 0`), and a ground core beside a free value
//!   only its type range constrains (`(false as u8) % 0u8`, the cast unmodeled).

#[cfg(possible)]
pub fn win_k(s: &[u8], k: usize) -> usize {
    //[possible]~^ ERROR Trust Level 0 safety verification incomplete for `forced_violation_reads_only_hypothesis_equalities::win_k`
    s.windows(k).count()
}

#[cfg(possible)]
pub fn guarded(s: &[u8], k: usize) -> usize {
    //[possible]~^ ERROR Trust Level 0 safety verification incomplete for `forced_violation_reads_only_hypothesis_equalities::guarded`
    if k < 5 { s.windows(k).count() } else { 0 }
}

#[cfg(possible)]
pub fn free_abs(x: i32) -> i32 {
    //[possible]~^ ERROR Trust Level 0 safety verification incomplete for `forced_violation_reads_only_hypothesis_equalities::free_abs`
    x.abs()
}

#[cfg(possible)]
pub fn free_rem_euclid(a: i64, b: i64) -> i64 {
    //[possible]~^ ERROR Trust Level 0 safety verification incomplete for `forced_violation_reads_only_hypothesis_equalities::free_rem_euclid`
    a.rem_euclid(b)
}

#[cfg(forced)]
pub fn loc() -> i32 {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::loc`
    let m = i32::MIN;
    m.abs()
}

#[cfg(forced)]
pub fn wloc(s: &[u8]) -> usize {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::wloc`
    let k = 0;
    s.windows(k).count()
}

#[cfg(forced)]
pub fn guarded_eq(s: &[u8], k: usize) -> usize {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::guarded_eq`
    if k == 0 { s.windows(k).count() } else { 0 }
}

#[cfg(forced)]
#[allow(arithmetic_overflow)]
pub fn ovf_const() -> u8 {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::ovf_const`
    let x: u8 = 255;
    x + 1
}

#[cfg(forced)]
#[allow(unconditional_panic)]
pub fn div_lit() -> i32 {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::div_lit`
    100 / 0
}

#[cfg(forced)]
#[allow(unconditional_panic)]
pub fn rem_cast() -> u8 {
    //[forced]~^ ERROR guaranteed Level 0 safety violation(s) in `forced_violation_reads_only_hypothesis_equalities::rem_cast`
    (false as u8) % 0u8
}
