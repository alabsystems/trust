//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
// Producer-positive core cases retain their measured current structural refusals.
// This file does not assert whole-body derived admission or check-pass.
#![no_std]

pub fn option_scalar(value: Option<u32>) -> Option<u32> {
    //~^ ERROR MIR re-derived from the THIR-derived trust-ir DISAGREES with the built MIR for this body
    let payload = value?;
    Some(payload)
}

pub fn result_scalar(value: Result<u32, u32>) -> Result<u32, u32> {
    let payload = value?;
    Ok(payload)
}

// Distinct success monomorphizations retain the identical u32 residual.
pub fn result_unit_success(value: Result<(), u32>) -> Result<u32, u32> {
    value?;
    Ok(7)
}

pub fn option_unit_success(value: Option<()>) -> Option<u32> {
    //~^ ERROR MIR re-derived from the THIR-derived trust-ir DISAGREES with the built MIR for this body
    value?;
    Some(7)
}

// An initializer evaluation has an observable local effect. The recognizer is
// read-only; only the existing lower_expr(operand) evaluates this block.
pub fn initializer_once(value: Option<u32>) -> Option<u32> {
    //~^ ERROR MIR re-derived from the THIR-derived trust-ir DISAGREES with the built MIR for this body
    let mut visits = 0u32;
    let payload = {
        visits += 1;
        value
    }?;
    Some(payload ^ visits)
}
