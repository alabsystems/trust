// NonZero + conversions harvest probe (bin crate).
use std::num::{NonZeroI64, NonZeroU32};

#[inline(never)]
pub fn nz_u32_new(x: u32) -> Option<NonZeroU32> {
    NonZeroU32::new(x)
}

#[inline(never)]
pub fn nz_u32_get(x: NonZeroU32) -> u32 {
    x.get()
}

#[inline(never)]
pub fn nz_i64_get(x: NonZeroI64) -> i64 {
    x.get()
}

#[inline(never)]
pub fn opt_nz_is_some(x: Option<NonZeroU32>) -> bool {
    x.is_some()
}

// From::from widening conversions
#[inline(never)]
pub fn from_u8_u32(x: u8) -> u32 {
    u32::from(x)
}

#[inline(never)]
pub fn from_i8_i64(x: i8) -> i64 {
    i64::from(x)
}

#[inline(never)]
pub fn from_u16_usize(x: u16) -> usize {
    usize::from(x)
}

#[inline(never)]
pub fn from_u8_i32(x: u8) -> i32 {
    i32::from(x)
}

#[inline(never)]
pub fn from_u16_u64(x: u16) -> u64 {
    u64::from(x)
}

#[inline(never)]
pub fn from_i16_i32(x: i16) -> i32 {
    i32::from(x)
}

// as-widening wrappers (pure casts, no From impl)
#[inline(never)]
pub fn as_u8_u32(x: u8) -> u32 {
    x as u32
}

#[inline(never)]
pub fn as_i8_i64(x: i8) -> i64 {
    x as i64
}

#[inline(never)]
pub fn as_u16_usize(x: u16) -> usize {
    x as usize
}

#[inline(never)]
pub fn as_u32_u64(x: u32) -> u64 {
    x as u64
}

#[inline(never)]
pub fn as_i32_i64(x: i32) -> i64 {
    x as i64
}

fn main() {
    // Value derived from argc so nothing const-folds away.
    let n = std::env::args().count() as u32;
    let nz = match nz_u32_new(n + 1) {
        Some(v) => v,
        None => return,
    };
    let nzi = match NonZeroI64::new(n as i64 + 1) {
        Some(v) => v,
        None => return,
    };
    let mut acc: u64 = 0;
    acc += nz_u32_get(nz) as u64;
    acc += nz_i64_get(nzi) as u64;
    acc += opt_nz_is_some(Some(nz)) as u64;
    acc += opt_nz_is_some(None) as u64;
    acc += from_u8_u32(n as u8) as u64;
    acc += from_i8_i64(n as i8) as u64 & 0xff;
    acc += from_u16_usize(n as u16) as u64;
    acc += from_u8_i32(n as u8) as u64;
    acc += from_u16_u64(n as u16);
    acc += from_i16_i32(n as i16) as u64 & 0xffff;
    acc += as_u8_u32(n as u8) as u64;
    acc += as_i8_i64(n as i8) as u64 & 0xff;
    acc += as_u16_usize(n as u16) as u64;
    acc += as_u32_u64(n);
    acc += as_i32_i64(n as i32) as u64 & 0xffff_ffff;
    println!("{}", acc);
}
