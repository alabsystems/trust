//@ needs-trust-verify
//@ revisions: pass i8_mismatch i16_mismatch i32_mismatch i64_mismatch usize_mismatch isize_mismatch u128_mismatch i128_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[i8_mismatch] run-crash
//@[i8_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i16_mismatch] run-crash
//@[i16_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i32_mismatch] run-crash
//@[i32_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i64_mismatch] run-crash
//@[i64_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[usize_mismatch] run-crash
//@[usize_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[isize_mismatch] run-crash
//@[isize_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u128_mismatch] run-crash
//@[u128_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i128_mismatch] run-crash
//@[i128_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr

//! End-to-end MIR execution for the signed, pointer-sized, and 128-bit
//! certified carriers. Each negative revision falsifies exactly one clause so
//! a missing carrier cannot pass vacuously.

fn signed_i8(x: i8) -> i8
    ensures result == x
{
    #[cfg(i8_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(i8_mismatch))]
    x
}

fn signed_i16(x: i16) -> i16
    ensures result == x
{
    #[cfg(i16_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(i16_mismatch))]
    x
}

fn signed_i32(x: i32) -> i32
    ensures result == x
{
    #[cfg(i32_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(i32_mismatch))]
    x
}

fn signed_i64(x: i64) -> i64
    ensures result == x
{
    #[cfg(i64_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(i64_mismatch))]
    x
}

fn pointer_unsigned(x: usize) -> usize
    ensures result == x
{
    #[cfg(usize_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(usize_mismatch))]
    x
}

fn pointer_signed(x: isize) -> isize
    ensures result == x
{
    #[cfg(isize_mismatch)]
    return x.wrapping_sub(1);
    #[cfg(not(isize_mismatch))]
    x
}

fn wide_unsigned(x: u128) -> u128
    ensures result == x
{
    #[cfg(u128_mismatch)]
    return x.wrapping_add(1);
    #[cfg(not(u128_mismatch))]
    x
}

fn wide_signed(x: i128) -> i128
    ensures result == x
{
    #[cfg(i128_mismatch)]
    return x.wrapping_sub(1);
    #[cfg(not(i128_mismatch))]
    x
}

#[test]
fn every_extended_carrier_executes() {
    assert_eq!(signed_i8(-7), -7);
    assert_eq!(signed_i16(-700), -700);
    assert_eq!(signed_i32(-70_000), -70_000);
    assert_eq!(signed_i64(-7_000_000_000), -7_000_000_000);
    assert_eq!(pointer_unsigned(11), 11);
    assert_eq!(pointer_signed(-3), -3);
    assert_eq!(wide_unsigned(u128::MAX - 1), u128::MAX - 1);
    assert_eq!(wide_signed(i128::MIN + 1), i128::MIN + 1);
}
