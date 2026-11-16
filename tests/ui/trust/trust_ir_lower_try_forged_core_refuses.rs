//@ edition: 2021
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib --crate-name=core
// Derived from the minimal language declarations in the in-tree
// tests/ui/traits/const-traits/auxiliary/minicore.rs. Compile this WHOLE source
// with --crate-name core, ordinary subject invocation (no sysroot-build flag).
#![no_core]
#![feature(no_core, lang_items)]
#![allow(internal_features)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u32 {}

#[lang = "Try"]
pub trait Try: FromResidual<Self::Residual> {
    type Output;
    type Residual;
    #[lang = "from_output"]
    fn from_output(output: Self::Output) -> Self;
    #[lang = "branch"]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

pub trait FromResidual<R = <Self as Try>::Residual> {
    #[lang = "from_residual"]
    fn from_residual(residual: R) -> Self;
}

pub enum ControlFlow<B, C> {
    #[lang = "Continue"]
    Continue(C),
    #[lang = "Break"]
    Break(B),
}

#[lang = "Option"]
pub enum Option<T> {
    #[lang = "Some"]
    Some(T),
    #[lang = "None"]
    None,
}

impl FromResidual for Option<u32> {
    fn from_residual(_residual: Self) -> Self {
        Self::None
    }
}

impl Try for Option<u32> {
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

pub fn forged_core_question(value: Option<u32>) -> Option<u32> {
    //~^ ERROR Try(branch operand not found)
    let payload = value?;
    Option::Some(payload)
}

pub fn forged_core_explicit(value: Option<u32>) -> Option<u32> {
    match value {
        Option::Some(_) => Option::None,
        Option::None => Option::Some(41),
    }
}
