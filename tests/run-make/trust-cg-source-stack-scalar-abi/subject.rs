#![no_std]
#![allow(unused_variables)]

#[unsafe(no_mangle)]
pub extern "C" fn trust_stack_int(i0: i64, i1: i64, i2: i64, i3: i64, i4: i64, i5: i64, i6: i64, i7: i64, a: i8, b: u8, c: i16, d: u16, e: i32, f: u32, g: i64) -> i64 {
    match i0 {
        0 => a as i64,
        1 => b as i64,
        2 => c as i64,
        3 => d as i64,
        4 => e as i64,
        5 => f as i64,
        _ => g,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn trust_stack_f32(f0: f32, f1: f64, f2: f32, f3: f64, f4: f32, f5: f64, f6: f32, f7: f64, x: f32) -> f32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn trust_stack_f64(f0: f32, f1: f64, f2: f32, f3: f64, f4: f32, f5: f64, f6: f32, f7: f64, x: f32, y: f64) -> f64 { y }

unsafe extern "C" {
    fn original_stack_mixed(i0: i64, f0: f32, i1: i64, f1: f64, i2: i64, f2: f32, i3: i64, f3: f64, i4: i64, f4: f32, i5: i64, f5: f64, i6: i64, f6: f32, i7: i64, f7: f64, a: u8, b: f32, c: i16, d: f64, e: u32, f: f32, g: i64) -> f64;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_stack_mixed(i0: i64, f0: f32, i1: i64, f1: f64, i2: i64, f2: f32, i3: i64, f3: f64, i4: i64, f4: f32, i5: i64, f5: f64, i6: i64, f6: f32, i7: i64, f7: f64, a: u8, b: f32, c: i16, d: f64, e: u32, f: f32, g: i64) -> f64 {
    unsafe { original_stack_mixed(i0, f0, i1, f1, i2, f2, i3, f3, i4, f4, i5, f5, i6, f6, i7, f7, a, b, c, d, e, f, g) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_stack_outgoing() -> f64 {
    unsafe { original_stack_mixed(11, 1.25, -22, -2.5, 33, 3.75, -44, -4.25, 55, 5.5, -66, -6.75, 77, 7.25, -88, -8.5, 241, -9.75, -12345, 17.5, 4000000001, 21.25, 81985529216486895) }
}

#[inline(never)]
#[unsafe(no_mangle)]
fn rust_stack_helper(i0: i64, i1: i64, i2: i64, i3: i64, i4: i64, i5: i64, i6: i64, i7: i64, x: i64) -> i64 { x }

#[unsafe(no_mangle)]
pub extern "C" fn trust_stack_local() -> i64 {
    rust_stack_helper(11, -22, 33, -44, 55, -66, 77, -88, 81985529216486895)
}
