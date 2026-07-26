//@ needs-trust-verify
//@ revisions: pass requires_lower_mismatch requires_upper_mismatch ensures_lower_mismatch ensures_upper_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Coverflow-checks=no -Awarnings
//@[pass] run-pass
//@[requires_lower_mismatch] run-crash
//@[requires_lower_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[requires_upper_mismatch] run-crash
//@[requires_upper_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[ensures_lower_mismatch] run-crash
//@[ensures_lower_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[ensures_upper_mismatch] run-crash
//@[ensures_upper_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! Runtime parity pin for repeated first-class clauses. Each crash revision
//! violates exactly one clause while the other three remain true, proving that
//! monitor insertion neither keeps only the first clause nor silently replaces
//! an earlier clause with a later one.

fn bounded_step(x: u8) -> u8
    requires x >= 2
    requires x <= 8
    ensures result >= x
    ensures result <= x + 1
{
    #[cfg(ensures_lower_mismatch)]
    return x - 1;
    #[cfg(ensures_upper_mismatch)]
    return x + 2;
    #[cfg(not(any(ensures_lower_mismatch, ensures_upper_mismatch)))]
    return x;
}

#[test]
fn every_certified_clause_monitor_executes() {
    let x = if cfg!(requires_lower_mismatch) {
        1
    } else if cfg!(requires_upper_mismatch) {
        9
    } else {
        5
    };
    let got = bounded_step(x);
    if cfg!(pass) {
        assert_eq!(got, x);
    }
}
