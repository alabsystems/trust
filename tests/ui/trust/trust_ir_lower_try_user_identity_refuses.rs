//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]
#![feature(try_trait_v2, try_trait_v2_residual)]

use core::ops::{ControlFlow, FromResidual, Try};

pub enum PretendOption {
    Some(u32),
    None,
}

impl core::ops::Residual<u32> for PretendOption {
    type TryType = Self;
}

impl FromResidual for PretendOption {
    fn from_residual(residual: Self) -> Self {
        match residual {
            Self::Some(value) => Self::Some(value ^ 1),
            Self::None => Self::Some(9),
        }
    }
}

impl Try for PretendOption {
    type Output = u32;
    type Residual = Self;

    fn from_output(output: u32) -> Self {
        Self::Some(output)
    }

    fn branch(self) -> ControlFlow<Self, u32> {
        match self {
            Self::Some(value) => ControlFlow::Break(Self::Some(value)),
            Self::None => ControlFlow::Continue(41),
        }
    }
}

pub fn option_names(value: PretendOption) -> PretendOption {
    //~^ ERROR Try(non-core enum identity)
    let payload = value?;
    PretendOption::Some(payload ^ 2)
}

pub fn option_names_explicit(value: PretendOption) -> PretendOption {
    match value {
        PretendOption::Some(payload) => PretendOption::Some(payload ^ 1),
        PretendOption::None => PretendOption::Some(43),
    }
}

pub enum PretendResult {
    Ok(u32),
    Err(u32),
}

impl core::ops::Residual<u32> for PretendResult {
    type TryType = Self;
}

impl FromResidual for PretendResult {
    fn from_residual(residual: Self) -> Self {
        match residual {
            Self::Ok(value) => Self::Ok(value ^ 8),
            Self::Err(value) => Self::Ok(value ^ 4),
        }
    }
}

impl Try for PretendResult {
    type Output = u32;
    type Residual = Self;

    fn from_output(output: u32) -> Self {
        Self::Ok(output)
    }

    fn branch(self) -> ControlFlow<Self, u32> {
        match self {
            Self::Ok(value) => ControlFlow::Break(Self::Err(value)),
            Self::Err(value) => ControlFlow::Continue(value),
        }
    }
}

pub fn result_names(value: PretendResult) -> PretendResult {
    //~^ ERROR Try(non-core enum identity)
    let payload = value?;
    PretendResult::Ok(payload ^ 2)
}

pub fn result_names_explicit(value: PretendResult) -> PretendResult {
    match value {
        PretendResult::Ok(payload) => PretendResult::Ok(payload ^ 4),
        PretendResult::Err(payload) => PretendResult::Ok(payload ^ 2),
    }
}
