// Re-review probes E, lens chc: runtime values the extractor lowers to the
// identity-less OpaqueScalar (pointer expose casts, float/byte/MaybeUninit
// transmutes) share the width-interned symbol with each other and with every
// unevaluated constant. No generics needed.
#![allow(clippy::all)]
use std::mem::{transmute, MaybeUninit};

// E1: two different addresses compared (safe code). Always panics for two
// distinct locals.
pub fn two_addrs(a: &u8, b: &u8) -> usize {
    let x = a as *const u8 as usize;
    let y = b as *const u8 as usize;
    if x != y {
        panic!("different addresses");
    }
    x
}

// E2: an address and a constant-like opaque of the same width (generic size_of).
pub fn addr_vs_size<T>(a: &u8) -> usize {
    let x = a as *const u8 as usize;
    let s = const { std::mem::size_of::<T>() };
    if s == 0 && x != 0 {
        panic!("zst T and a non-null address");
    }
    x
}

// E3: float bit patterns of two different floats.
pub fn float_bits(x: f32, y: f32) -> u32 {
    let a: u32 = unsafe { transmute::<f32, u32>(x) };
    let b: u32 = unsafe { transmute::<f32, u32>(y) };
    if a != b {
        panic!("bits differ");
    }
    a
}

// E4: byte-array packs of two arrays.
pub fn byte_packs(p: [u8; 4], q: [u8; 4]) -> u32 {
    let a: u32 = unsafe { transmute::<[u8; 4], u32>(p) };
    let b: u32 = unsafe { transmute::<[u8; 4], u32>(q) };
    if a == 0 && b != 0 {
        panic!("one zero, one not");
    }
    a
}

// E5: MaybeUninit<u64> -> u64 vs a pointer address (both u64).
pub fn mu_vs_addr(m: MaybeUninit<u64>, r: &u8) -> u64 {
    let v: u64 = unsafe { transmute::<MaybeUninit<u64>, u64>(m) };
    let x = r as *const u8 as usize as u64;
    if v != x {
        panic!("value differs from address");
    }
    v
}

// E6: false REFUTATION on correct code: end != start for a 4-byte array.
pub fn span_nonempty(a: &[u8; 4]) -> usize {
    let s = a.as_ptr() as usize;
    let e = a.as_ptr().wrapping_add(4) as usize;
    if e == s {
        panic!("empty span");
    }
    4
}

// E7: control: a single expose cast, no aliasing partner. Must stay refutable.
pub fn one_addr(a: &u8) -> usize {
    let x = a as *const u8 as usize;
    if x % 2 == 1 {
        panic!("odd address");
    }
    x
}
