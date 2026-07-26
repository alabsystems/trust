#![feature(int_roundings)] // signed div_ceil/div_floor/next_multiple_of are still unstable

// integer-methods2 harvest corpus: i32/u32/i8 method breadth through the 21 certifier lanes.
// Inputs derived from std::env::args().count() (>= 1, so isqrt/ilog2/div args stay in-domain).

#[inline(never)]
fn w_pow2(x: i32) -> i32 {
    x.pow(2)
}

#[inline(never)]
fn w_isqrt(x: i32) -> i32 {
    x.isqrt()
}

#[inline(never)]
fn w_abs_diff(a: i32, b: i32) -> u32 {
    a.abs_diff(b)
}

#[inline(never)]
fn w_midpoint(a: i32, b: i32) -> i32 {
    a.midpoint(b)
}

#[inline(never)]
fn w_div_ceil(a: i32, b: i32) -> i32 {
    a.div_ceil(b)
}

#[inline(never)]
fn w_div_floor(a: i32, b: i32) -> i32 {
    a.div_floor(b)
}

#[inline(never)]
fn w_next_multiple_of(x: i32) -> i32 {
    x.next_multiple_of(8)
}

#[inline(never)]
fn w_is_power_of_two(x: u32) -> bool {
    x.is_power_of_two()
}

#[inline(never)]
fn w_next_power_of_two(x: u32) -> u32 {
    x.next_power_of_two()
}

#[inline(never)]
fn w_ilog2(x: u32) -> u32 {
    x.ilog2()
}

#[inline(never)]
fn w_checked_neg(x: i8) -> Option<i8> {
    x.checked_neg()
}

#[inline(never)]
fn w_wrapping_neg(x: i8) -> i8 {
    x.wrapping_neg()
}

fn main() {
    let n = std::env::args().count() as i32; // >= 1
    let m = (n + 3) as i32;
    let u = n as u32; // >= 1
    let s = n as i8;

    let mut acc: i64 = 0;
    acc += w_pow2(n) as i64;
    acc += w_isqrt(n) as i64;
    acc += w_abs_diff(n, m) as i64;
    acc += w_midpoint(n, m) as i64;
    acc += w_div_ceil(m, n) as i64;
    acc += w_div_floor(m, n) as i64;
    acc += w_next_multiple_of(n) as i64;
    acc += w_is_power_of_two(u) as i64;
    acc += w_next_power_of_two(u) as i64;
    acc += w_ilog2(u) as i64;
    acc += w_checked_neg(s).unwrap_or(0) as i64;
    acc += w_wrapping_neg(s) as i64;

    // Mono-dump forcing probes: instantiate the generic intra-core callees the
    // family leaves forward to, so their instance dumps land in the directory.
    let nz = core::num::NonZero::<u32>::new(u);
    if let Some(z) = nz {
        acc += z.get() as i64;
    }
    acc += Some(n).is_none() as i64;

    std::process::exit((acc & 0x3f) as i32);
}
