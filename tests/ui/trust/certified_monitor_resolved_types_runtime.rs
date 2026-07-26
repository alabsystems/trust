//@ needs-trust-verify
//@ revisions: alias_pass alias_mismatch qualified_pass qualified_mismatch u16_pass u16_mismatch u32_pass u32_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[alias_pass] run-pass
//@[alias_mismatch] run-crash
//@[alias_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[qualified_pass] run-pass
//@[qualified_mismatch] run-crash
//@[qualified_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u16_pass] run-pass
//@[u16_mismatch] run-crash
//@[u16_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[u32_pass] run-pass
//@[u32_mismatch] run-crash
//@[u32_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! Runtime proof that resolved type aliases and qualified primitive paths both
//! receive executable certified monitors. Plain `u16` and `u32` cases complete
//! the runtime coverage for every supported unsigned carrier (`u8` wrapping is
//! covered by `certified_monitor_u8_wrapping.rs`). Each spelling has a passing
//! revision and a mismatching return-value control; the crash controls prevent
//! the passing runs from succeeding vacuously if monitor injection disappears.

type Word = u64;

fn alias_identity(x: Word) -> Word
    ensures result == x
{
    #[cfg(alias_mismatch)]
    return x + 1;
    #[cfg(not(alias_mismatch))]
    return x;
}

fn qualified_identity(
    x: core::primitive::u64,
) -> core::primitive::u64
    ensures result == x
{
    #[cfg(qualified_mismatch)]
    return x + 1;
    #[cfg(not(qualified_mismatch))]
    return x;
}

fn u16_identity(x: u16) -> u16
    ensures result == x
{
    #[cfg(u16_mismatch)]
    return x + 1;
    #[cfg(not(u16_mismatch))]
    return x;
}

fn u32_identity(x: u32) -> u32
    ensures result == x
{
    #[cfg(u32_mismatch)]
    return x + 1;
    #[cfg(not(u32_mismatch))]
    return x;
}

#[cfg(any(alias_pass, alias_mismatch))]
#[test]
fn alias_carrier_is_monitored() {
    assert_eq!(alias_identity(7), 7);
}

#[cfg(any(qualified_pass, qualified_mismatch))]
#[test]
fn qualified_carrier_is_monitored() {
    assert_eq!(qualified_identity(11), 11);
}

#[cfg(any(u16_pass, u16_mismatch))]
#[test]
fn u16_carrier_is_monitored() {
    assert_eq!(u16_identity(13), 13);
}

#[cfg(any(u32_pass, u32_mismatch))]
#[test]
fn u32_carrier_is_monitored() {
    assert_eq!(u32_identity(17), 17);
}
