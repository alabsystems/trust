// arith-guarded family probe: wrapping/saturating/checked arithmetic on i32/u8.

#[inline(never)]
pub fn w_i32_wrapping_add(a: i32, b: i32) -> i32 { a.wrapping_add(b) }
#[inline(never)]
pub fn w_i32_wrapping_sub(a: i32, b: i32) -> i32 { a.wrapping_sub(b) }
#[inline(never)]
pub fn w_i32_wrapping_mul(a: i32, b: i32) -> i32 { a.wrapping_mul(b) }
#[inline(never)]
pub fn w_i32_saturating_add(a: i32, b: i32) -> i32 { a.saturating_add(b) }
#[inline(never)]
pub fn w_i32_saturating_sub(a: i32, b: i32) -> i32 { a.saturating_sub(b) }
#[inline(never)]
pub fn w_i32_checked_add_is_some(a: i32, b: i32) -> bool { a.checked_add(b).is_some() }
#[inline(never)]
pub fn w_i32_overflowing_add_0(a: i32, b: i32) -> i32 { a.overflowing_add(b).0 }

#[inline(never)]
pub fn w_u8_wrapping_add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }
#[inline(never)]
pub fn w_u8_wrapping_sub(a: u8, b: u8) -> u8 { a.wrapping_sub(b) }
#[inline(never)]
pub fn w_u8_wrapping_mul(a: u8, b: u8) -> u8 { a.wrapping_mul(b) }
#[inline(never)]
pub fn w_u8_saturating_add(a: u8, b: u8) -> u8 { a.saturating_add(b) }
#[inline(never)]
pub fn w_u8_saturating_sub(a: u8, b: u8) -> u8 { a.saturating_sub(b) }
#[inline(never)]
pub fn w_u8_checked_add_is_some(a: u8, b: u8) -> bool { a.checked_add(b).is_some() }
#[inline(never)]
pub fn w_u8_overflowing_add_0(a: u8, b: u8) -> u8 { a.overflowing_add(b).0 }

fn main() {
    let n = std::env::args().count() as i32;
    let m = (n + 3) as i32;
    let nu = n as u8;
    let mu = m as u8;

    let mut acc_i: i64 = 0;
    acc_i += w_i32_wrapping_add(n, m) as i64;
    acc_i += w_i32_wrapping_sub(n, m) as i64;
    acc_i += w_i32_wrapping_mul(n, m) as i64;
    acc_i += w_i32_saturating_add(n, m) as i64;
    acc_i += w_i32_saturating_sub(n, m) as i64;
    acc_i += w_i32_checked_add_is_some(n, m) as i64;
    acc_i += w_i32_overflowing_add_0(n, m) as i64;

    let mut acc_u: u64 = 0;
    acc_u += w_u8_wrapping_add(nu, mu) as u64;
    acc_u += w_u8_wrapping_sub(nu, mu) as u64;
    acc_u += w_u8_wrapping_mul(nu, mu) as u64;
    acc_u += w_u8_saturating_add(nu, mu) as u64;
    acc_u += w_u8_saturating_sub(nu, mu) as u64;
    acc_u += w_u8_checked_add_is_some(nu, mu) as u64;
    acc_u += w_u8_overflowing_add_0(nu, mu) as u64;

    println!("acc_i={} acc_u={}", acc_i, acc_u);
}
