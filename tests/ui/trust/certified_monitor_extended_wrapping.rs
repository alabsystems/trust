//@ needs-trust-verify
//@ revisions: pass i8_mismatch i16_mismatch i32_mismatch i64_mismatch i128_mismatch u128_mismatch usize_mismatch isize_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Coverflow-checks=no -Awarnings
//@[pass] run-pass
//@[i8_mismatch] run-crash
//@[i8_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i16_mismatch] run-crash
//@[i16_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i32_mismatch] run-crash
//@[i32_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i64_mismatch] run-crash
//@[i64_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[i128_mismatch] run-crash
//@[i128_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u128_mismatch] run-crash
//@[u128_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[usize_mismatch] run-crash
//@[usize_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[isize_mismatch] run-crash
//@[isize_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr

//! End-to-end boundary coverage for arithmetic emitted into certified monitor
//! MIR over every signed width, `u128`, and the target-exact pointer carriers.
//! Every passing call crosses `MAX + 1 -> MIN` (or `0` for `u128`), which a
//! mathematical-Int/Nat monitor would reject. Each negative revision falsifies
//! exactly one arithmetic clause, so carrier support cannot pass vacuously.

fn wrapping_i8(x: i8) -> i8
    ensures result == x + 1
{
    #[cfg(i8_mismatch)]
    return x;
    #[cfg(not(i8_mismatch))]
    return x + 1;
}

fn wrapping_i16(x: i16) -> i16
    ensures result == x + 1
{
    #[cfg(i16_mismatch)]
    return x;
    #[cfg(not(i16_mismatch))]
    return x + 1;
}

fn wrapping_i32(x: i32) -> i32
    ensures result == x + 1
{
    #[cfg(i32_mismatch)]
    return x;
    #[cfg(not(i32_mismatch))]
    return x + 1;
}

fn wrapping_i64(x: i64) -> i64
    ensures result == x + 1
{
    #[cfg(i64_mismatch)]
    return x;
    #[cfg(not(i64_mismatch))]
    return x + 1;
}

fn wrapping_i128(x: i128) -> i128
    ensures result == x + 1
{
    #[cfg(i128_mismatch)]
    return x;
    #[cfg(not(i128_mismatch))]
    return x + 1;
}

fn wrapping_u128(x: u128) -> u128
    ensures result == x + 1
{
    #[cfg(u128_mismatch)]
    return x;
    #[cfg(not(u128_mismatch))]
    return x + 1;
}

fn wrapping_usize(x: usize) -> usize
    ensures result == x + 1
{
    #[cfg(usize_mismatch)]
    return x;
    #[cfg(not(usize_mismatch))]
    return x + 1;
}

fn wrapping_isize(x: isize) -> isize
    ensures result == x + 1
{
    #[cfg(isize_mismatch)]
    return x;
    #[cfg(not(isize_mismatch))]
    return x + 1;
}

#[test]
fn extended_certified_monitors_use_exact_wrapping_carriers() {
    assert_eq!(wrapping_i8(i8::MAX), i8::MIN);
    assert_eq!(wrapping_i16(i16::MAX), i16::MIN);
    assert_eq!(wrapping_i32(i32::MAX), i32::MIN);
    assert_eq!(wrapping_i64(i64::MAX), i64::MIN);
    assert_eq!(wrapping_i128(i128::MAX), i128::MIN);
    assert_eq!(wrapping_u128(u128::MAX), 0);
    assert_eq!(wrapping_usize(usize::MAX), 0);
    assert_eq!(wrapping_isize(isize::MAX), isize::MIN);
}
