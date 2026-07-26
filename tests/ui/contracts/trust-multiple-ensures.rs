//@ revisions: unchk_pass chk_pass chk_fail_first chk_fail_second chk_fail_ret
//
//@ [unchk_pass] run-pass
//@ [chk_pass] run-pass
//@ [chk_fail_first] run-crash
//@ [chk_fail_second] run-crash
//@ [chk_fail_ret] run-crash
//
//@ [unchk_pass] compile-flags: -Zcontract-checks=no
//@ [chk_pass] compile-flags: -Zcontract-checks=yes
//@ [chk_fail_first] compile-flags: -Zcontract-checks=yes
//@ [chk_fail_second] compile-flags: -Zcontract-checks=yes
//@ [chk_fail_ret] compile-flags: -Zcontract-checks=yes
//! Trust: a function may carry MULTIPLE `#[ensures]` clauses — every clause
//! closure is lowered to its own checker binding and the checks chain in
//! attribute order at every return point (implicit tail and explicit
//! `return`). This replaced the former "at most one `#[ensures]`" hard error,
//! which was itself a guard against the phantom-DefId metadata-encoding ICE
//! (`No HirId for DefId(..::{closure#N})`) that unlowered clause closures
//! caused — and a drop-in divergence, since plain rustc (via the trust-spec
//! passthrough macro) accepts any number of ensures attributes.
#![expect(incomplete_features)]
#![feature(contracts)]

#[core::contracts::requires(a > 0 || b > 0)]
#[core::contracts::ensures(move |r: &u32| *r >= a)]
#[core::contracts::ensures(move |r: &u32| *r >= b)]
fn max(a: u32, b: u32) -> u32 {
    if a > b { a } else { b }
}

// Both clauses must also guard explicit `return` statements.
#[core::contracts::ensures(move |r: &u32| *r >= lo)]
#[core::contracts::ensures(move |r: &u32| *r <= hi)]
fn clamp(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        return lo;
    }
    if x > hi {
        return hi;
    }
    x
}

#[cfg(chk_fail_first)]
#[core::contracts::ensures(|r: &u32| *r > 100)] // first clause fails
#[core::contracts::ensures(|r: &u32| *r < 100)]
fn victim() -> u32 {
    42
}

#[cfg(chk_fail_second)]
#[core::contracts::ensures(|r: &u32| *r < 100)]
#[core::contracts::ensures(|r: &u32| *r > 100)] // second clause fails
fn victim() -> u32 {
    42
}

#[cfg(chk_fail_ret)]
#[core::contracts::ensures(|r: &u32| *r < 100)]
#[core::contracts::ensures(|r: &u32| *r != 42)] // fails via explicit return
fn victim() -> u32 {
    return 42;
}

fn main() {
    // Both postconditions hold on every lane.
    assert_eq!(max(3, 7), 7);
    assert_eq!(clamp(5, 1, 10), 5);
    assert_eq!(clamp(0, 1, 10), 1);
    assert_eq!(clamp(50, 1, 10), 10);

    // Violating either clause crashes when checks are on.
    #[cfg(any(chk_fail_first, chk_fail_second, chk_fail_ret))]
    {
        let _ = victim();
    }
}
