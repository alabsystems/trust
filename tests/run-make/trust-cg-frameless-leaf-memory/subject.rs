#![no_std]

#[unsafe(no_mangle)]
pub unsafe extern "C" fn leaf_store(p: *mut u8, value: u64) -> u64 {
    unsafe {
        *p = value as u8;
    }
    0
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn leaf_load(p: *const u8) -> u64 {
    unsafe { *p as u64 }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn leaf_copy(to: *mut u8, from: *const u8) -> u64 {
    unsafe {
        *to = *from;
    }
    0
}
#[repr(C)]
pub struct Pair {
    pub first: u8,
    pub second: u8,
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn leaf_gep(p: *mut Pair, value: u64) -> u64 {
    unsafe {
        (*p).second = value as u8;
    }
    0
}
