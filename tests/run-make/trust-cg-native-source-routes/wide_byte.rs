#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_wide_byte(value: u16) -> u16 { value }
