#![crate_type = "lib"]

// These coercion kinds keep their existing refusal arms. Visiting an Unsize
// operand does not grant another pointer coercion a lowering implementation.
// Since 94502e4acc a THIN raw mut→const coercion lowers to one `PtrToPtr` (no access
// rights are granted; `mutable_to_const_thin`). The fat shape keeps the refusal arm.
pub fn mutable_to_const(value: *mut [u32]) -> *const [u32] {
    value
}

pub fn mutable_to_const_thin(value: *mut u32) -> *const u32 {
    value
}

pub fn safe_to_unsafe(value: fn(u32) -> u32) -> unsafe fn(u32) -> u32 {
    value
}
