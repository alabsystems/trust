// NonZero family harvest v2 — breadth minus the transmute gap.
// NonZeroU8/U16/I32: new (safe), get, bit-method delegation
// (count_ones/leading_zeros/trailing_zeros), Ord comparisons.
use std::num::{NonZeroI32, NonZeroU16, NonZeroU32, NonZeroU8};

#[inline(never)]
fn nz_u8_new(x: u8) -> Option<NonZeroU8> {
    NonZeroU8::new(x)
}

#[inline(never)]
fn nz_u8_get(n: NonZeroU8) -> u8 {
    n.get()
}

#[inline(never)]
fn nz_u16_new(x: u16) -> Option<NonZeroU16> {
    NonZeroU16::new(x)
}

#[inline(never)]
fn nz_u16_get(n: NonZeroU16) -> u16 {
    n.get()
}

#[inline(never)]
fn nz_i32_new(x: i32) -> Option<NonZeroI32> {
    NonZeroI32::new(x)
}

#[inline(never)]
fn nz_i32_get(n: NonZeroI32) -> i32 {
    n.get()
}

#[inline(never)]
fn nz_u8_count_ones(n: NonZeroU8) -> NonZeroU32 {
    n.count_ones()
}

#[inline(never)]
fn nz_u8_leading_zeros(n: NonZeroU8) -> u32 {
    n.leading_zeros()
}

#[inline(never)]
fn nz_u8_trailing_zeros(n: NonZeroU8) -> u32 {
    n.trailing_zeros()
}

#[inline(never)]
fn nz_u16_count_ones(n: NonZeroU16) -> NonZeroU32 {
    n.count_ones()
}

#[inline(never)]
fn nz_i32_count_ones(n: NonZeroI32) -> NonZeroU32 {
    n.count_ones()
}

#[inline(never)]
fn nz_i32_leading_zeros(n: NonZeroI32) -> u32 {
    n.leading_zeros()
}

#[inline(never)]
fn nz_i32_trailing_zeros(n: NonZeroI32) -> u32 {
    n.trailing_zeros()
}

#[inline(never)]
fn nz_u8_lt(a: NonZeroU8, b: NonZeroU8) -> bool {
    a < b
}

#[inline(never)]
fn nz_i32_lt(a: NonZeroI32, b: NonZeroI32) -> bool {
    a < b
}

#[inline(never)]
fn nz_u8_cmp(a: NonZeroU8, b: NonZeroU8) -> std::cmp::Ordering {
    a.cmp(&b)
}

fn main() {
    let c = std::env::args().count();
    let a8 = c as u8;
    let b8 = a8.wrapping_add(1);
    let a16 = c as u16;
    let ai = c as i32;

    let x8 = nz_u8_new(a8).unwrap_or(NonZeroU8::MIN);
    let y8 = nz_u8_new(b8).unwrap_or(NonZeroU8::MIN);
    let x16 = nz_u16_new(a16).unwrap_or(NonZeroU16::MIN);
    let xi = nz_i32_new(ai).unwrap_or(NonZeroI32::MIN);
    let yi = nz_i32_new(ai.wrapping_add(1)).unwrap_or(NonZeroI32::MIN);

    let mut acc: u32 = 0;
    acc = acc.wrapping_add(nz_u8_get(x8) as u32);
    acc = acc.wrapping_add(nz_u16_get(x16) as u32);
    acc = acc.wrapping_add(nz_i32_get(xi) as u32);
    acc = acc.wrapping_add(nz_u8_count_ones(x8).get());
    acc = acc.wrapping_add(nz_u8_leading_zeros(x8));
    acc = acc.wrapping_add(nz_u8_trailing_zeros(x8));
    acc = acc.wrapping_add(nz_u16_count_ones(x16).get());
    acc = acc.wrapping_add(nz_i32_count_ones(xi).get());
    acc = acc.wrapping_add(nz_i32_leading_zeros(xi));
    acc = acc.wrapping_add(nz_i32_trailing_zeros(xi));
    acc = acc.wrapping_add(nz_u8_lt(x8, y8) as u32);
    acc = acc.wrapping_add(nz_i32_lt(xi, yi) as u32);
    acc = acc.wrapping_add(nz_u8_cmp(x8, y8) as i32 as u32);

    std::process::exit((acc & 0x3f) as i32);
}
