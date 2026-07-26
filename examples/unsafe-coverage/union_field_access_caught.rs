// Reading a union field is unconditionally unsafe (the read may observe an
// invalid bit-pattern for the field's type). Trust does not model union validity,
// so it must be CAUGHT fail-closed — never silently passed.
//   trustc -Z trust-verify-output=human --crate-type lib union_field_access_caught.rs
#![allow(dead_code)]

union FloatBits {
    f: f32,
    bits: u32,
}

/// Reading `u.bits` is a union field access — must be CAUGHT (`[unsafe:union-field]`).
pub fn float_to_bits(f: f32) -> u32 {
    let u = FloatBits { f };
    unsafe { u.bits }
}

/// Control: no union access — must NOT be flagged.
pub fn safe(x: u32) -> u32 {
    x.wrapping_add(1)
}
