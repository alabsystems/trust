#![no_std]

#[repr(C)]
pub struct Pair {
    pub first: u8,
    pub second: u8,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_store_rhs_order(
    mut destination: *mut u8,
    replacement: *mut u8,
    value: u64,
) -> u64 {
    unsafe {
        *destination = {
            destination = replacement;
            value as u8
        };
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_field_rhs_order(
    mut destination: *mut Pair,
    replacement: *mut Pair,
    value: u64,
) -> u64 {
    unsafe {
        (*destination).second = {
            destination = replacement;
            value as u8
        };
    }
    0
}
