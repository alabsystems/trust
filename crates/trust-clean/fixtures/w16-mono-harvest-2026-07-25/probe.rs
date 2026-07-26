// W16 monomorphic-instance harvest probe (2026-07-25).
// Exercises GENERIC stdlib functions at CONCRETE types so codegen's mono inventory
// contains their instances. Observational only.
#![allow(dead_code)]

pub fn cmp_family(a: i32, b: i32, c: u8, d: u8) -> i32 {
    let x = Ord::min(a, b);
    let y = Ord::max(a, b);
    let z = Ord::min(c, d) as i32;
    let w = Ord::max(c, d) as i32;
    a.clamp(b, b.wrapping_add(1)) ^ x ^ y ^ z ^ w
}

pub fn option_family(o: Option<i32>, p: Option<u64>) -> i64 {
    let a = o.unwrap_or(0);
    let b = o.is_some() as i32;
    let c = p.unwrap_or(7);
    let d = o.map(|v| v + 1).unwrap_or(2);
    (a as i64) + (b as i64) + (c as i64) + (d as i64)
}

pub fn result_family(r: Result<i32, u8>, s: Result<u32, i16>) -> i64 {
    let a = r.unwrap_or(0);
    let b = r.is_ok() as i32;
    let c = s.unwrap_or(9);
    (a as i64) + (b as i64) + (c as i64)
}

pub fn generic_id<T>(t: T) -> T { t }
pub fn use_generic_id(a: i32, b: u64, c: i8) -> i64 {
    (generic_id(a) as i64) + (generic_id(b) as i64) + (generic_id(c) as i64)
}

pub fn generic_add<T: core::ops::Add<Output = T> + Copy>(a: T, b: T) -> T { a + b }
pub fn use_generic_add(a: i32, b: i32, c: u16, d: u16) -> i64 {
    (generic_add(a, b) as i64) + (generic_add(c, d) as i64)
}

pub fn slice_family(s: &[i32], t: &[u8]) -> usize { s.len() + t.len() }

pub fn convert_family(a: i32, b: u8) -> i64 {
    let x: i64 = i64::from(a);
    let y: i64 = i64::from(b);
    x + y
}

fn main() {
    let v = cmp_family(3, 4, 5, 6)
        + option_family(Some(1), Some(2)) as i32
        + result_family(Ok(1), Ok(2)) as i32
        + use_generic_id(1, 2, 3) as i32
        + use_generic_add(1, 2, 3, 4) as i32
        + slice_family(&[1, 2], &[3]) as i32
        + convert_family(1, 2) as i32;
    core::hint::black_box(v);
}
