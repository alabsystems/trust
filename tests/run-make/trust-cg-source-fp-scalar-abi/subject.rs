#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn trust_fp32_identity(x: f32) -> f32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn trust_fp64_identity(x: f64) -> f64 { x }

#[inline(never)]
#[unsafe(no_mangle)]
fn rust_fp32_add(x: f32) -> f32 { x + 1.25 }

#[inline(never)]
#[unsafe(no_mangle)]
fn rust_fp64_add(x: f64) -> f64 { x + 2.5 }

#[unsafe(no_mangle)]
pub extern "C" fn trust_fp32_add(x: f32) -> f32 { rust_fp32_add(x) }

#[unsafe(no_mangle)]
pub extern "C" fn trust_fp64_add(x: f64) -> f64 { rust_fp64_add(x) }

unsafe extern "C" {
    fn original_fp_mixed(a: i32, b: f32, c: i64, d: f64) -> f64;
    fn original_fp_banks(i0: i64, f0: f32, i1: i64, f1: f64,
        i2: i64, f2: f32, i3: i64, f3: f64, i4: i64, f4: f32, i5: i64, f5: f64,
        i6: i64, f6: f32, i7: i64, f7: f64) -> f64;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_fp_mixed(a: i32, b: f32, c: i64, d: f64) -> f64 {
    unsafe { original_fp_mixed(a, b, c, d) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_fp_banks(i0: i64, f0: f32, i1: i64, f1: f64,
    i2: i64, f2: f32, i3: i64, f3: f64, i4: i64, f4: f32, i5: i64, f5: f64,
    i6: i64, f6: f32, i7: i64, f7: f64) -> f64 {
    unsafe { original_fp_banks(i0, f0, i1, f1, i2, f2, i3, f3, i4, f4, i5, f5, i6, f6, i7, f7) }
}
