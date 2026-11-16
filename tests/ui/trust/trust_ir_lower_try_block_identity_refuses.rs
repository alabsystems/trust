//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]
#![feature(try_blocks)]

pub fn option_block(value: Option<u32>) -> Option<u32> {
    //~^ ERROR Try(non-identity return desugar)
    let caught: Option<u32> = try { value? };
    match caught {
        Some(payload) => Some(payload),
        None => Some(99),
    }
}

pub fn option_block_explicit(value: Option<u32>) -> Option<u32> {
    match value {
        Some(payload) => Some(payload),
        None => Some(99),
    }
}

pub fn result_block(value: Result<u32, u32>) -> Result<u32, u32> {
    //~^ ERROR Try(non-identity return desugar)
    let caught: Result<u32, u32> = try { value? };
    match caught {
        Ok(payload) => Ok(payload),
        Err(_) => Ok(99),
    }
}

pub fn result_block_explicit(value: Result<u32, u32>) -> Result<u32, u32> {
    match value {
        Ok(payload) => Ok(payload),
        Err(_) => Ok(99),
    }
}
