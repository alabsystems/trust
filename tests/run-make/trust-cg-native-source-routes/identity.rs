#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_identity(value: u64) -> u64 {
    value
}
