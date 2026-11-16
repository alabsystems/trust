#![no_std]

// Transport the complete incoming address, including null. No dereference or
// reference conversion supplies validity, alignment or aliasing assumptions.
#[unsafe(no_mangle)]
pub extern "C" fn ordinary_raw_pointer(value: *mut u8) -> *mut u8 {
    value
}
