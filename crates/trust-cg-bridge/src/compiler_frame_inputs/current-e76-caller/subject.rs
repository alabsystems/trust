#![no_std]

// New subject reconstructed from the historical b8 capture's typed IR shape.
// The historical Rust source bytes were not retained; this is not an unchanged b8 subject.
#[inline(never)]
unsafe fn source_memory_callee(to: *mut u8, from: *const u8, value: u64) -> u64 {
    let previous = unsafe { *from };
    unsafe { *to = value as u8 };
    previous as u64
}

#[no_mangle]
pub unsafe extern "C" fn source_memory_caller(
    to: *mut u8,
    from: *const u8,
    value: u64,
) -> u64 {
    unsafe { source_memory_callee(to, from, value) }
}
