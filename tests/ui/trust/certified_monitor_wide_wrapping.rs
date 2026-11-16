//@ needs-trust-verify
//@ revisions: pass u16_add_mismatch u16_sub_mismatch u16_mul_mismatch u32_add_mismatch u32_sub_mismatch u32_mul_mismatch u64_add_mismatch u64_sub_mismatch u64_mul_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Coverflow-checks=no -Awarnings
//@[pass] run-pass
//@[u16_add_mismatch] run-crash
//@[u16_add_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u16_sub_mismatch] run-crash
//@[u16_sub_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u16_mul_mismatch] run-crash
//@[u16_mul_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u32_add_mismatch] run-crash
//@[u32_add_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u32_sub_mismatch] run-crash
//@[u32_sub_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u32_mul_mismatch] run-crash
//@[u32_mul_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u64_add_mismatch] run-crash
//@[u64_add_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u64_sub_mismatch] run-crash
//@[u64_sub_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u64_mul_mismatch] run-crash
//@[u64_mul_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! End-to-end proof that certified monitor lowering retains the resolved native
//! width for wrapping `u16`, `u32`, and `u64` addition, subtraction, and
//! multiplication. Each passing call crosses its carrier boundary; evaluating
//! the clause over `Nat` would reject it. Each mismatch revision falsifies one
//! clause, proving that all nine executable monitors are actually inserted.

// Each mismatch revision compiles only the item(s) its assertion exercises;
// `pass` still compiles and runs every item, so coverage is unchanged.
// `not(test)` keeps every body in a harness-free build of this file: the trust-ir
// producer scorecard compiles it as a plain lib with no revision cfg.

#[cfg(any(pass, not(test), u16_add_mismatch))]
fn u16_wrapping_add(x: u16) -> u16
    ensures result == x + 1
{
    #[cfg(u16_add_mismatch)]
    return x;
    #[cfg(not(u16_add_mismatch))]
    return x + 1;
}

#[cfg(any(pass, not(test), u16_sub_mismatch))]
fn u16_wrapping_sub(x: u16) -> u16
    ensures result == x - 1
{
    #[cfg(u16_sub_mismatch)]
    return x;
    #[cfg(not(u16_sub_mismatch))]
    return x - 1;
}

#[cfg(any(pass, not(test), u16_mul_mismatch))]
fn u16_wrapping_mul(x: u16) -> u16
    ensures result == x * 2
{
    #[cfg(u16_mul_mismatch)]
    return x;
    #[cfg(not(u16_mul_mismatch))]
    return x * 2;
}

#[cfg(any(pass, not(test), u32_add_mismatch))]
fn u32_wrapping_add(x: u32) -> u32
    ensures result == x + 1
{
    #[cfg(u32_add_mismatch)]
    return x;
    #[cfg(not(u32_add_mismatch))]
    return x + 1;
}

#[cfg(any(pass, not(test), u32_sub_mismatch))]
fn u32_wrapping_sub(x: u32) -> u32
    ensures result == x - 1
{
    #[cfg(u32_sub_mismatch)]
    return x;
    #[cfg(not(u32_sub_mismatch))]
    return x - 1;
}

#[cfg(any(pass, not(test), u32_mul_mismatch))]
fn u32_wrapping_mul(x: u32) -> u32
    ensures result == x * 2
{
    #[cfg(u32_mul_mismatch)]
    return x;
    #[cfg(not(u32_mul_mismatch))]
    return x * 2;
}

#[cfg(any(pass, not(test), u64_add_mismatch))]
fn u64_wrapping_add(x: u64) -> u64
    ensures result == x + 1
{
    #[cfg(u64_add_mismatch)]
    return x;
    #[cfg(not(u64_add_mismatch))]
    return x + 1;
}

#[cfg(any(pass, not(test), u64_sub_mismatch))]
fn u64_wrapping_sub(x: u64) -> u64
    ensures result == x - 1
{
    #[cfg(u64_sub_mismatch)]
    return x;
    #[cfg(not(u64_sub_mismatch))]
    return x - 1;
}

#[cfg(any(pass, not(test), u64_mul_mismatch))]
fn u64_wrapping_mul(x: u64) -> u64
    ensures result == x * 2
{
    #[cfg(u64_mul_mismatch)]
    return x;
    #[cfg(not(u64_mul_mismatch))]
    return x * 2;
}

#[cfg(any(pass, u16_add_mismatch, u16_sub_mismatch, u16_mul_mismatch))]
#[test]
fn certified_u16_monitors_use_u16_wrapping() {
    #[cfg(any(pass, u16_add_mismatch))]
    assert_eq!(u16_wrapping_add(u16::MAX), 0);
    #[cfg(any(pass, u16_sub_mismatch))]
    assert_eq!(u16_wrapping_sub(0), u16::MAX);
    #[cfg(any(pass, u16_mul_mismatch))]
    assert_eq!(u16_wrapping_mul((u16::MAX / 2) + 1), 0);
}

#[cfg(any(pass, u32_add_mismatch, u32_sub_mismatch, u32_mul_mismatch))]
#[test]
fn certified_u32_monitors_use_u32_wrapping() {
    #[cfg(any(pass, u32_add_mismatch))]
    assert_eq!(u32_wrapping_add(u32::MAX), 0);
    #[cfg(any(pass, u32_sub_mismatch))]
    assert_eq!(u32_wrapping_sub(0), u32::MAX);
    #[cfg(any(pass, u32_mul_mismatch))]
    assert_eq!(u32_wrapping_mul((u32::MAX / 2) + 1), 0);
}

#[cfg(any(pass, u64_add_mismatch, u64_sub_mismatch, u64_mul_mismatch))]
#[test]
fn certified_u64_monitors_use_u64_wrapping() {
    #[cfg(any(pass, u64_add_mismatch))]
    assert_eq!(u64_wrapping_add(u64::MAX), 0);
    #[cfg(any(pass, u64_sub_mismatch))]
    assert_eq!(u64_wrapping_sub(0), u64::MAX);
    #[cfg(any(pass, u64_mul_mismatch))]
    assert_eq!(u64_wrapping_mul((u64::MAX / 2) + 1), 0);
}
