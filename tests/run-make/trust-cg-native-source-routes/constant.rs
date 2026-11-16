#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_constant() -> u64 {
    37
}
