// cmp method-call family probes: a.min(b), a.max(b), a.clamp(lo,hi)
// at {i32, u8, i64, usize}, nested min().max() at i32, struct-field forms.

pub struct S {
    pub x: i32,
}

pub struct SU {
    pub x: usize,
}

// --- min ---
#[inline(never)]
pub fn min_i32(a: i32, b: i32) -> i32 {
    a.min(b)
}

#[inline(never)]
pub fn min_u8(a: u8, b: u8) -> u8 {
    a.min(b)
}

#[inline(never)]
pub fn min_i64(a: i64, b: i64) -> i64 {
    a.min(b)
}

#[inline(never)]
pub fn min_usize(a: usize, b: usize) -> usize {
    a.min(b)
}

// --- max ---
#[inline(never)]
pub fn max_i32(a: i32, b: i32) -> i32 {
    a.max(b)
}

#[inline(never)]
pub fn max_u8(a: u8, b: u8) -> u8 {
    a.max(b)
}

#[inline(never)]
pub fn max_i64(a: i64, b: i64) -> i64 {
    a.max(b)
}

#[inline(never)]
pub fn max_usize(a: usize, b: usize) -> usize {
    a.max(b)
}

// --- clamp ---
#[inline(never)]
pub fn clamp_i32(a: i32, lo: i32, hi: i32) -> i32 {
    a.clamp(lo, hi)
}

#[inline(never)]
pub fn clamp_u8(a: u8, lo: u8, hi: u8) -> u8 {
    a.clamp(lo, hi)
}

#[inline(never)]
pub fn clamp_i64(a: i64, lo: i64, hi: i64) -> i64 {
    a.clamp(lo, hi)
}

#[inline(never)]
pub fn clamp_usize(a: usize, lo: usize, hi: usize) -> usize {
    a.clamp(lo, hi)
}

// --- nested composition ---
#[inline(never)]
pub fn min_max_i32(a: i32, b: i32, c: i32) -> i32 {
    a.min(b).max(c)
}

// --- struct-field forms ---
#[inline(never)]
pub fn field_min_i32(s: &S, cap: i32) -> i32 {
    s.x.min(cap)
}

#[inline(never)]
pub fn field_min_usize(s: &SU, cap: usize) -> usize {
    s.x.min(cap)
}

fn main() {
    let n = std::env::args().count();
    let a = n as i32;
    let b = (n as i32) + 3;
    let c = (n as i32) - 1;
    let au = n as u8;
    let bu = (n as u8).wrapping_add(5);
    let al = n as i64;
    let bl = (n as i64) + 7;
    let az = n;
    let bz = n + 11;

    let s = S { x: a + 2 };
    let su = SU { x: az + 4 };

    let mut acc: i64 = 0;
    acc += min_i32(a, b) as i64;
    acc += min_u8(au, bu) as i64;
    acc += min_i64(al, bl);
    acc += min_usize(az, bz) as i64;
    acc += max_i32(a, b) as i64;
    acc += max_u8(au, bu) as i64;
    acc += max_i64(al, bl);
    acc += max_usize(az, bz) as i64;
    acc += clamp_i32(a, c, b) as i64;
    acc += clamp_u8(au, au, bu.max(au)) as i64;
    acc += clamp_i64(al, al - 2, bl);
    acc += clamp_usize(az, az, bz) as i64;
    acc += min_max_i32(a, b, c) as i64;
    acc += field_min_i32(&s, b) as i64;
    acc += field_min_usize(&su, bz) as i64;

    println!("acc={acc}");
}
