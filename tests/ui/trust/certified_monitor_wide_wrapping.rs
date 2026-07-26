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

fn u16_wrapping_add(x: u16) -> u16
    ensures result == x + 1
{
    #[cfg(u16_add_mismatch)]
    return x;
    #[cfg(not(u16_add_mismatch))]
    return x + 1;
}

fn u16_wrapping_sub(x: u16) -> u16
    ensures result == x - 1
{
    #[cfg(u16_sub_mismatch)]
    return x;
    #[cfg(not(u16_sub_mismatch))]
    return x - 1;
}

fn u16_wrapping_mul(x: u16) -> u16
    ensures result == x * 2
{
    #[cfg(u16_mul_mismatch)]
    return x;
    #[cfg(not(u16_mul_mismatch))]
    return x * 2;
}

fn u32_wrapping_add(x: u32) -> u32
    ensures result == x + 1
{
    #[cfg(u32_add_mismatch)]
    return x;
    #[cfg(not(u32_add_mismatch))]
    return x + 1;
}

fn u32_wrapping_sub(x: u32) -> u32
    ensures result == x - 1
{
    #[cfg(u32_sub_mismatch)]
    return x;
    #[cfg(not(u32_sub_mismatch))]
    return x - 1;
}

fn u32_wrapping_mul(x: u32) -> u32
    ensures result == x * 2
{
    #[cfg(u32_mul_mismatch)]
    return x;
    #[cfg(not(u32_mul_mismatch))]
    return x * 2;
}

fn u64_wrapping_add(x: u64) -> u64
    ensures result == x + 1
{
    #[cfg(u64_add_mismatch)]
    return x;
    #[cfg(not(u64_add_mismatch))]
    return x + 1;
}

fn u64_wrapping_sub(x: u64) -> u64
    ensures result == x - 1
{
    #[cfg(u64_sub_mismatch)]
    return x;
    #[cfg(not(u64_sub_mismatch))]
    return x - 1;
}

fn u64_wrapping_mul(x: u64) -> u64
    ensures result == x * 2
{
    #[cfg(u64_mul_mismatch)]
    return x;
    #[cfg(not(u64_mul_mismatch))]
    return x * 2;
}

#[test]
fn certified_u16_monitors_use_u16_wrapping() {
    assert_eq!(u16_wrapping_add(u16::MAX), 0);
    assert_eq!(u16_wrapping_sub(0), u16::MAX);
    assert_eq!(u16_wrapping_mul((u16::MAX / 2) + 1), 0);
}

#[test]
fn certified_u32_monitors_use_u32_wrapping() {
    assert_eq!(u32_wrapping_add(u32::MAX), 0);
    assert_eq!(u32_wrapping_sub(0), u32::MAX);
    assert_eq!(u32_wrapping_mul((u32::MAX / 2) + 1), 0);
}

#[test]
fn certified_u64_monitors_use_u64_wrapping() {
    assert_eq!(u64_wrapping_add(u64::MAX), 0);
    assert_eq!(u64_wrapping_sub(0), u64::MAX);
    assert_eq!(u64_wrapping_mul((u64::MAX / 2) + 1), 0);
}
