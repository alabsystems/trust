// Family: integer predicate/sign leaves.
// Probes: iN::{is_positive,is_negative,signum,abs} for i32/i64/i8,
// u32::is_power_of_two, i32::{rem_euclid,div_euclid} with positive const divisor,
// plus min(abs(a), b) compositions.

#[inline(never)]
pub fn w_i32_is_positive(x: i32) -> bool {
    x.is_positive()
}

#[inline(never)]
pub fn w_i32_is_negative(x: i32) -> bool {
    x.is_negative()
}

#[inline(never)]
pub fn w_i32_signum(x: i32) -> i32 {
    x.signum()
}

#[inline(never)]
pub fn w_i32_abs(x: i32) -> i32 {
    x.abs()
}

#[inline(never)]
pub fn w_i64_is_positive(x: i64) -> bool {
    x.is_positive()
}

#[inline(never)]
pub fn w_i64_is_negative(x: i64) -> bool {
    x.is_negative()
}

#[inline(never)]
pub fn w_i64_signum(x: i64) -> i64 {
    x.signum()
}

#[inline(never)]
pub fn w_i64_abs(x: i64) -> i64 {
    x.abs()
}

#[inline(never)]
pub fn w_i8_is_positive(x: i8) -> bool {
    x.is_positive()
}

#[inline(never)]
pub fn w_i8_is_negative(x: i8) -> bool {
    x.is_negative()
}

#[inline(never)]
pub fn w_i8_signum(x: i8) -> i8 {
    x.signum()
}

#[inline(never)]
pub fn w_i8_abs(x: i8) -> i8 {
    x.abs()
}

#[inline(never)]
pub fn w_u32_is_power_of_two(x: u32) -> bool {
    x.is_power_of_two()
}

#[inline(never)]
pub fn w_i32_rem_euclid_7(x: i32) -> i32 {
    x.rem_euclid(7)
}

#[inline(never)]
pub fn w_i32_div_euclid_7(x: i32) -> i32 {
    x.div_euclid(7)
}

#[inline(never)]
pub fn w_min_abs_i32(a: i32, b: i32) -> i32 {
    a.abs().min(b)
}

#[inline(never)]
pub fn w_min_abs_i64(a: i64, b: i64) -> i64 {
    a.abs().min(b)
}

fn main() {
    let n = std::env::args().count() as i64;
    let x32 = (n as i32) - 2;
    let x64 = n - 2;
    let x8 = (n as i8) - 2;
    let u = n as u32;

    let mut acc = String::new();
    acc.push_str(&format!("{}", w_i32_is_positive(x32)));
    acc.push_str(&format!("{}", w_i32_is_negative(x32)));
    acc.push_str(&format!("{}", w_i32_signum(x32)));
    acc.push_str(&format!("{}", w_i32_abs(x32)));
    acc.push_str(&format!("{}", w_i64_is_positive(x64)));
    acc.push_str(&format!("{}", w_i64_is_negative(x64)));
    acc.push_str(&format!("{}", w_i64_signum(x64)));
    acc.push_str(&format!("{}", w_i64_abs(x64)));
    acc.push_str(&format!("{}", w_i8_is_positive(x8)));
    acc.push_str(&format!("{}", w_i8_is_negative(x8)));
    acc.push_str(&format!("{}", w_i8_signum(x8)));
    acc.push_str(&format!("{}", w_i8_abs(x8)));
    acc.push_str(&format!("{}", w_u32_is_power_of_two(u)));
    acc.push_str(&format!("{}", w_i32_rem_euclid_7(x32)));
    acc.push_str(&format!("{}", w_i32_div_euclid_7(x32)));
    acc.push_str(&format!("{}", w_min_abs_i32(x32, 5)));
    acc.push_str(&format!("{}", w_min_abs_i64(x64, 5)));
    println!("{acc}");
}
