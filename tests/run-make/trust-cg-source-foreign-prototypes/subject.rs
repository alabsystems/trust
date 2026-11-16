#![no_std]

unsafe extern "C" {
    fn original_foreign_fixed(signed: i8, unsigned: u16) -> i32;
    fn original_foreign_variadic(tag: i32, ...) -> i32;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_foreign_fixed() -> i32 {
    unsafe { original_foreign_fixed(-101, 0xfedc) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_foreign_variadic(tag: i32) -> i32 {
    unsafe { original_foreign_variadic(tag, -123_i32, 17.5_f64, 0xfedc_ba98_7654_3210_u64) }
}
