#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_signed_byte(value: i8) -> i8 { value }
