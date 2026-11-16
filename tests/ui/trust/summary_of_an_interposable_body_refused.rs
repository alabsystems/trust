//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
#![feature(linkage)]
//! A callee summary describes the body a call RUNS. A body whose symbol the final
//! link can replace is not that body, so it lends no summary.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (round 9 of the callee-summary review): each
//! body below is exported under a weak symbol, and a binary that defines the same
//! symbols strongly replaced them. `go`, `go_low` and `go_kst` were PROVED and
//! kernel-certified from `x.min(3)`, `g.max(1)` and `{1, 2}`, and panicked running
//! the strong definitions (`x`, `g`, `0`). The same held for a stable `#[no_mangle]`
//! function whose archive member the link never loaded (`go_plain`). The
//! inferred-return lane already excluded interposable bodies; the summaries now do
//! too (`trust_verify::summary_body_identities`).

pub trait Tr {
    fn m(&self, x: usize) -> usize;
}

pub struct S;

impl Tr for S {
    #[export_name = "trust_fixture_interposable_tr_m"]
    #[linkage = "weak"]
    #[inline(never)]
    fn m(&self, x: usize) -> usize {
        x.min(3)
    }
}

impl S {
    #[export_name = "trust_fixture_interposable_den"]
    #[linkage = "weak"]
    #[inline(never)]
    pub fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
    #[export_name = "trust_fixture_interposable_k"]
    #[linkage = "weak"]
    #[inline(never)]
    pub fn k(&self, c: bool) -> u32 {
        if c { 1 } else { 2 }
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn trust_fixture_interposable_div_by() -> u32 {
    1
}

// x = 10, once `m` is replaced by `x`.
#[inline(never)]
pub fn go(x: usize, a: &[u8; 4]) -> u8 { //~ ERROR strict verification failed for `summary_of_an_interposable_body_refused::go`
    a[S.m(x)]
}

// g = 0.
#[inline(never)]
pub fn go_low(h: u32, g: u32) -> u32 { //~ ERROR strict verification failed for `summary_of_an_interposable_body_refused::go_low`
    h % S.den(g)
}

#[inline(never)]
pub fn go_kst(h: u32, c: bool) -> u32 { //~ ERROR strict verification failed for `summary_of_an_interposable_body_refused::go_kst`
    h / S.k(c)
}

#[inline(never)]
pub fn go_plain(h: u32) -> u32 { //~ ERROR strict verification failed for `summary_of_an_interposable_body_refused::go_plain`
    h / trust_fixture_interposable_div_by()
}
