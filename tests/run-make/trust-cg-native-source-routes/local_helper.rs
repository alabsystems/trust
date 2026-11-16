#![no_std]
#![crate_type = "lib"]

#[inline(never)]
fn local_adjust(value: u64) -> u64 {
    value ^ 0x5a
}

#[unsafe(no_mangle)]
pub extern "C" fn ordinary_helper_call(value: u64) -> u64 {
    local_adjust(value)
}
