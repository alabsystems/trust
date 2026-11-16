#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_c_byte(value: u8) -> u8 {
    value ^ 0x5a
}
