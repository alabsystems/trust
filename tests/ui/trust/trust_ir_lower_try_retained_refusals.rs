//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]

// Authentic core FromResidual still performs From<u8> for u32; it is not
// justified by an authentic method identity alone. The old exact-type guard
// must continue to report Try(From-converting residual).
pub fn converting_error(value: Result<u32, u8>) -> Result<u32, u32> {
    //~^ ERROR Try(From-converting residual)
    let payload = value?;
    Ok(payload)
}

// Shared str is Copy, but still outside this scalar-only increment.
pub fn borrowed_success(value: Option<&str>) -> Option<u32> {
    //~^ ERROR Try(non-scalar success payload)
    let _payload = value?;
    Some(7)
}

// A borrowed error is also still outside the existing error-seeding model.
pub fn borrowed_error(value: Result<u32, &str>) -> Result<u32, &str> {
    //~^ ERROR Try(fat err field)
    let payload = value?;
    Ok(payload)
}
