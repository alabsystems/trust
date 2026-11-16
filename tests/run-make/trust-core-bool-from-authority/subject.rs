#![feature(no_core)]
#![no_core]
extern crate core;

#[no_mangle]
pub fn counterfeit_from(flag: bool) -> u32 {
    <u32 as core::From<bool>>::from(flag)
}
