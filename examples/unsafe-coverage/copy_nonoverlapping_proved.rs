use std::ptr::{addr_of, addr_of_mut};
pub fn copy_guarded(count: usize) {
    let src = [7u8; 64];
    let mut dst = [0u8; 64];
    if count <= 64 { unsafe { std::ptr::copy_nonoverlapping(addr_of!(src) as *const u8, addr_of_mut!(dst) as *mut u8, count) } }
}
pub fn copy_unguarded(count: usize) {
    let src = [7u8; 64];
    let mut dst = [0u8; 64];
    unsafe { std::ptr::copy_nonoverlapping(addr_of!(src) as *const u8, addr_of_mut!(dst) as *mut u8, count) }
}
