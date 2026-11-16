//@ needs-trust-verify
//@ revisions: pass bool_mismatch ne_mismatch mixed_mismatch mixed_numeric_mismatch or_mismatch not_mismatch le_mismatch lt_mismatch ge_mismatch gt_mismatch sub_mismatch mul_mismatch div_mismatch rem_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Coverflow-checks=no -Awarnings
//@[pass] run-pass
//@[bool_mismatch] run-crash
//@[bool_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[ne_mismatch] run-crash
//@[ne_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[mixed_mismatch] run-crash
//@[mixed_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[mixed_numeric_mismatch] run-crash
//@[mixed_numeric_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[or_mismatch] run-crash
//@[or_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[not_mismatch] run-crash
//@[not_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[le_mismatch] run-crash
//@[le_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[lt_mismatch] run-crash
//@[lt_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[ge_mismatch] run-crash
//@[ge_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[gt_mismatch] run-crash
//@[gt_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[sub_mismatch] run-crash
//@[sub_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[mul_mismatch] run-crash
//@[mul_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[div_mismatch] run-crash
//@[div_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[rem_mismatch] run-crash
//@[rem_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! End-to-end MIR-emission coverage for the certified-monitor expression
//! fragment beyond simple unsigned equality and addition. The passing revision
//! exercises both truth-bearing sides of each connective and the equality and
//! strict cases needed to distinguish ordered comparisons. Each mismatch
//! revision falsifies only one exercised clause, proving that its monitor is
//! present rather than letting the shared passing case succeed vacuously.

// Each mismatch revision compiles only the item(s) its assertion exercises;
// `pass` still compiles and runs every item, so coverage is unchanged.
// `not(test)` keeps every body in a harness-free build of this file: the trust-ir
// producer scorecard compiles it as a plain lib with no revision cfg.

#[cfg(any(pass, not(test), bool_mismatch))]
fn bool_identity(flag: bool) -> bool
    ensures result == flag
{
    #[cfg(bool_mismatch)]
    return !flag;
    #[cfg(not(bool_mismatch))]
    return flag;
}

#[cfg(any(pass, not(test), ne_mismatch))]
fn unequal_successor(x: u8) -> u8
    ensures result != x
{
    #[cfg(ne_mismatch)]
    return x;
    #[cfg(not(ne_mismatch))]
    return x + 1;
}

#[cfg(any(pass, not(test), mixed_mismatch, mixed_numeric_mismatch))]
fn mixed_gate(flag: bool, x: u8) -> u8
    ensures flag && result == x
{
    #[cfg(mixed_numeric_mismatch)]
    return x + 1;
    #[cfg(not(mixed_numeric_mismatch))]
    x
}

#[cfg(any(pass, not(test), or_mismatch))]
fn disjunction_gate(flag: bool) -> bool
    ensures result || flag
{
    #[cfg(or_mismatch)]
    return false;
    #[cfg(not(or_mismatch))]
    return !flag;
}

#[cfg(any(pass, not(test), not_mismatch))]
fn negated_result() -> bool
    ensures !result
{
    #[cfg(not_mismatch)]
    return true;
    #[cfg(not(not_mismatch))]
    return false;
}

#[cfg(any(pass, not(test), le_mismatch))]
fn le_identity(x: u8) -> u8
    ensures result <= x
{
    #[cfg(le_mismatch)]
    return x + 1;
    #[cfg(not(le_mismatch))]
    return x;
}

#[cfg(any(pass, not(test)))]
fn le_halved(x: u8) -> u8
    ensures result <= x
{
    x / 2
}

#[cfg(any(pass, not(test), lt_mismatch))]
fn lt_predecessor(x: u8) -> u8
    ensures result < x
{
    #[cfg(lt_mismatch)]
    return x;
    #[cfg(not(lt_mismatch))]
    return x - 1;
}

#[cfg(any(pass, not(test), ge_mismatch))]
fn ge_identity(x: u8) -> u8
    ensures result >= x
{
    #[cfg(ge_mismatch)]
    return x - 1;
    #[cfg(not(ge_mismatch))]
    return x;
}

#[cfg(any(pass, not(test)))]
fn ge_max(x: u8) -> u8
    ensures result >= x
{
    u8::MAX
}

#[cfg(any(pass, not(test), gt_mismatch))]
fn gt_successor(x: u8) -> u8
    ensures result > x
{
    #[cfg(gt_mismatch)]
    return x;
    #[cfg(not(gt_mismatch))]
    return x + 1;
}

#[cfg(any(pass, not(test), sub_mismatch))]
fn wrapping_sub(x: u8) -> u8
    ensures result == x - 1
{
    #[cfg(sub_mismatch)]
    return 0;
    #[cfg(not(sub_mismatch))]
    return x - 1;
}

#[cfg(any(pass, not(test), mul_mismatch))]
fn wrapping_mul(x: u8) -> u8
    ensures result == x * 2
{
    #[cfg(mul_mismatch)]
    return 0;
    #[cfg(not(mul_mismatch))]
    return x * 2;
}

#[cfg(any(pass, not(test), div_mismatch))]
fn halved(x: u8) -> u8
    ensures result == x / 2
{
    #[cfg(div_mismatch)]
    return 4;
    #[cfg(not(div_mismatch))]
    return x / 2;
}

#[cfg(any(pass, not(test), rem_mismatch))]
fn parity(x: u8) -> u8
    ensures result == x % 2
{
    #[cfg(rem_mismatch)]
    return 0;
    #[cfg(not(rem_mismatch))]
    return x % 2;
}

#[cfg(any(pass, bool_mismatch))]
#[test]
fn certified_bool_monitor_executes() {
    assert!(bool_identity(true));
}

#[cfg(any(pass, ne_mismatch))]
#[test]
fn certified_ne_monitor_executes() {
    assert_eq!(unequal_successor(7), 8);
}

#[cfg(any(pass, mixed_mismatch, mixed_numeric_mismatch))]
#[test]
fn certified_mixed_domain_monitor_executes() {
    // One mismatch keeps the numeric atom true and falsifies only the bare
    // Bool atom; the other keeps the Bool atom true and falsifies only the
    // numeric atom. Together they prove that MIR emission retained both sides
    // of the mixed-domain `And`.
    assert_eq!(mixed_gate(!cfg!(mixed_mismatch), 7), 7);
}

#[cfg(any(pass, or_mismatch))]
#[test]
fn certified_or_monitor_executes() {
    assert!(disjunction_gate(false));
    assert!(!disjunction_gate(true));
}

#[cfg(any(pass, not_mismatch))]
#[test]
fn certified_not_monitor_executes() {
    assert!(!negated_result());
}

#[cfg(any(pass, le_mismatch, lt_mismatch, ge_mismatch, gt_mismatch))]
#[test]
fn certified_comparison_monitors_execute() {
    #[cfg(any(pass, le_mismatch))]
    assert_eq!(le_identity(7), 7);
    #[cfg(pass)]
    assert_eq!(le_halved(7), 3);
    #[cfg(any(pass, lt_mismatch))]
    assert_eq!(lt_predecessor(7), 6);
    #[cfg(any(pass, ge_mismatch))]
    assert_eq!(ge_identity(7), 7);
    #[cfg(pass)]
    assert_eq!(ge_max(7), u8::MAX);
    #[cfg(any(pass, gt_mismatch))]
    assert_eq!(gt_successor(7), 8);
}

#[cfg(any(pass, sub_mismatch))]
#[test]
fn certified_sub_monitor_uses_wrapping_machine_arithmetic() {
    assert_eq!(wrapping_sub(0), u8::MAX);
}

#[cfg(any(pass, mul_mismatch))]
#[test]
fn certified_mul_monitor_uses_wrapping_machine_arithmetic() {
    assert_eq!(wrapping_mul(200), 144);
}

#[cfg(any(pass, div_mismatch))]
#[test]
fn certified_div_monitor_executes() {
    assert_eq!(halved(7), 3);
}

#[cfg(any(pass, rem_mismatch))]
#[test]
fn certified_rem_monitor_executes() {
    assert_eq!(parity(7), 1);
}
