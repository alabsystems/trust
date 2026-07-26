// Two-call-chain harvest family: sem_two_call_chain lane breadth.
// Shapes: a.min(b).max(c); a.max(b).min(c); saturating_add-then-saturating_sub;
// wrapping_add-then-wrapping_sub; clamp-via-min-max hand-spelled min(max(x,lo),hi)
// through the std::cmp free functions.

use std::cmp::{max, min};

// --- a.min(b).max(c) at {i32, u8, i64, usize} ---
#[inline(never)]
fn min_max_i32(a: i32, b: i32, c: i32) -> i32 {
    a.min(b).max(c)
}
#[inline(never)]
fn min_max_u8(a: u8, b: u8, c: u8) -> u8 {
    a.min(b).max(c)
}
#[inline(never)]
fn min_max_i64(a: i64, b: i64, c: i64) -> i64 {
    a.min(b).max(c)
}
#[inline(never)]
fn min_max_usize(a: usize, b: usize, c: usize) -> usize {
    a.min(b).max(c)
}

// --- a.max(b).min(c) at {i32, u8, i64, usize} ---
#[inline(never)]
fn max_min_i32(a: i32, b: i32, c: i32) -> i32 {
    a.max(b).min(c)
}
#[inline(never)]
fn max_min_u8(a: u8, b: u8, c: u8) -> u8 {
    a.max(b).min(c)
}
#[inline(never)]
fn max_min_i64(a: i64, b: i64, c: i64) -> i64 {
    a.max(b).min(c)
}
#[inline(never)]
fn max_min_usize(a: usize, b: usize, c: usize) -> usize {
    a.max(b).min(c)
}

// --- saturating chains: sat_add(a,b) then sat_sub(_,c) — intrinsic callees ---
#[inline(never)]
fn sat_add_sub_i32(a: i32, b: i32, c: i32) -> i32 {
    a.saturating_add(b).saturating_sub(c)
}
#[inline(never)]
fn sat_add_sub_u8(a: u8, b: u8, c: u8) -> u8 {
    a.saturating_add(b).saturating_sub(c)
}
#[inline(never)]
fn sat_add_sub_i64(a: i64, b: i64, c: i64) -> i64 {
    a.saturating_add(b).saturating_sub(c)
}
#[inline(never)]
fn sat_add_sub_usize(a: usize, b: usize, c: usize) -> usize {
    a.saturating_add(b).saturating_sub(c)
}

// --- wrapping chains: wrapping_add then wrapping_sub — intrinsic callees ---
#[inline(never)]
fn wrap_add_sub_i32(a: i32, b: i32, c: i32) -> i32 {
    a.wrapping_add(b).wrapping_sub(c)
}
#[inline(never)]
fn wrap_add_sub_u8(a: u8, b: u8, c: u8) -> u8 {
    a.wrapping_add(b).wrapping_sub(c)
}

// --- clamp-via-min-max hand-spelled min(max(x,lo),hi) via std::cmp free fns ---
#[inline(never)]
fn clamp_mm_i32(x: i32, lo: i32, hi: i32) -> i32 {
    min(max(x, lo), hi)
}
#[inline(never)]
fn clamp_mm_u8(x: u8, lo: u8, hi: u8) -> u8 {
    min(max(x, lo), hi)
}
#[inline(never)]
fn clamp_mm_i64(x: i64, lo: i64, hi: i64) -> i64 {
    min(max(x, lo), hi)
}
#[inline(never)]
fn clamp_mm_usize(x: usize, lo: usize, hi: usize) -> usize {
    min(max(x, lo), hi)
}

fn main() {
    let n = std::env::args().count();
    let a32 = n as i32;
    let b32 = (n + 3) as i32;
    let c32 = (n + 1) as i32;
    let a8 = (n % 200) as u8;
    let b8 = ((n + 3) % 200) as u8;
    let c8 = ((n + 1) % 200) as u8;
    let a64 = n as i64;
    let b64 = (n + 3) as i64;
    let c64 = (n + 1) as i64;
    let au = n;
    let bu = n + 3;
    let cu = n + 1;

    let mut acc_i32: i32 = 0;
    let mut acc_u8: u8 = 0;
    let mut acc_i64: i64 = 0;
    let mut acc_usize: usize = 0;

    acc_i32 = acc_i32.wrapping_add(min_max_i32(a32, b32, c32));
    acc_u8 = acc_u8.wrapping_add(min_max_u8(a8, b8, c8));
    acc_i64 = acc_i64.wrapping_add(min_max_i64(a64, b64, c64));
    acc_usize = acc_usize.wrapping_add(min_max_usize(au, bu, cu));

    acc_i32 = acc_i32.wrapping_add(max_min_i32(a32, b32, c32));
    acc_u8 = acc_u8.wrapping_add(max_min_u8(a8, b8, c8));
    acc_i64 = acc_i64.wrapping_add(max_min_i64(a64, b64, c64));
    acc_usize = acc_usize.wrapping_add(max_min_usize(au, bu, cu));

    acc_i32 = acc_i32.wrapping_add(sat_add_sub_i32(a32, b32, c32));
    acc_u8 = acc_u8.wrapping_add(sat_add_sub_u8(a8, b8, c8));
    acc_i64 = acc_i64.wrapping_add(sat_add_sub_i64(a64, b64, c64));
    acc_usize = acc_usize.wrapping_add(sat_add_sub_usize(au, bu, cu));

    acc_i32 = acc_i32.wrapping_add(wrap_add_sub_i32(a32, b32, c32));
    acc_u8 = acc_u8.wrapping_add(wrap_add_sub_u8(a8, b8, c8));

    acc_i32 = acc_i32.wrapping_add(clamp_mm_i32(a32, c32, b32));
    acc_u8 = acc_u8.wrapping_add(clamp_mm_u8(a8, c8, b8));
    acc_i64 = acc_i64.wrapping_add(clamp_mm_i64(a64, c64, b64));
    acc_usize = acc_usize.wrapping_add(clamp_mm_usize(au, cu, bu));

    println!("{} {} {} {}", acc_i32, acc_u8, acc_i64, acc_usize);
}
