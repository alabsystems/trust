//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ rustc-env:TRUST_MONITOR_REPORT=1
//@ build-pass
//@ dont-check-compiler-stderr
//! Certified-monitor carrier selection is type-directed. A transparent alias
//! and a fully qualified primitive path must both retain the resolved `u64`
//! carrier instead of being rejected because their HIR spelling is not `u64`.
//! Plain `u8`, `u16`, and `u32` cases complete the report coverage for every
//! supported unsigned carrier.

type Word = u64;

pub fn u8_identity(x: u8) -> u8
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}

pub fn alias_identity(x: Word) -> Word
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}

pub fn qualified_identity(
    x: core::primitive::u64,
) -> core::primitive::u64
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}

pub fn u16_identity(x: u16) -> u16
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}

pub fn u32_identity(x: u32) -> u32
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}
