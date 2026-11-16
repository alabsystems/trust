// Confirmer probes (lens chcconfirm), finding 1: runtime values the extractor
// lowers to OpaqueScalar. Written independently of the hunter's file; each
// function's panic is reachable on the input named in its comment.
#![allow(clippy::all)]
use std::mem::{transmute, MaybeUninit};

// R1: safe, non-generic. Two distinct live locals: always panics.
pub fn cc_two_addrs(a: &u8, b: &u8) -> usize {
    let x = a as *const u8 as usize;
    let y = b as *const u8 as usize;
    if x != y {
        panic!("R1 addresses differ");
    }
    x
}

// R1b: same, assert! form (the shape a user would write).
pub fn cc_assert_same_addr(a: &u32, b: &u32) {
    let x = a as *const u32 as usize;
    let y = b as *const u32 as usize;
    assert!(x == y, "R1b");
}

// R2: f32 bits of 1.0 and 2.0 differ: panics.
pub fn cc_f32_bits(x: f32, y: f32) -> u32 {
    let a: u32 = unsafe { transmute::<f32, u32>(x) };
    let b: u32 = unsafe { transmute::<f32, u32>(y) };
    if a != b {
        panic!("R2 bits differ");
    }
    a
}

// R3: f64 bits vs a pointer address (both u64, different kinds of runtime value).
// cc_f64_vs_addr(1.5, &v): panics.
pub fn cc_f64_vs_addr(x: f64, r: &u8) -> u64 {
    let a: u64 = unsafe { transmute::<f64, u64>(x) };
    let b = r as *const u8 as usize as u64;
    if a != b {
        panic!("R3 bits != address");
    }
    a
}

// R4: [u8;4] packs: [1,2,3,4] vs [0;4]: panics.
pub fn cc_bytes(p: [u8; 4], q: [u8; 4]) -> u32 {
    let a: u32 = unsafe { transmute::<[u8; 4], u32>(p) };
    let b: u32 = unsafe { transmute::<[u8; 4], u32>(q) };
    if a != b {
        panic!("R4 packs differ");
    }
    a
}

// R5: MaybeUninit<u64> value vs an f64's bits. MaybeUninit::new(3), 0.25: panics.
pub fn cc_mu_vs_f64(m: MaybeUninit<u64>, f: f64) -> u64 {
    let v: u64 = unsafe { transmute::<MaybeUninit<u64>, u64>(m) };
    let w: u64 = unsafe { transmute::<f64, u64>(f) };
    if v != w {
        panic!("R5 differ");
    }
    v
}

// R6: an address vs a literal-free generic constant (size_of::<T>()).
// cc_addr_vs_size::<u64>(&v): address != 8: panics.
pub fn cc_addr_vs_size<T>(r: &u8) -> usize {
    let x = r as *const u8 as usize;
    let s = const { std::mem::size_of::<T>() };
    if x != s {
        panic!("R6 address != size");
    }
    x
}

// R7: control, one runtime value compared with itself + 1 (no aliasing partner):
// must NOT be proved (it can never hold; we expect PROVED to be impossible
// here only if the arithmetic is honest: x + 1 == x is never true, so the
// panic below is unreachable and PROVED is CORRECT).
pub fn cc_ctl_self(r: &u8) -> usize {
    let x = r as *const u8 as usize;
    let y = x.wrapping_add(1);
    if y == x {
        panic!("R7 unreachable");
    }
    x
}

// R8: control, one address tested against an arbitrary user value: must not be
// proved (cc_ctl_param(&v, 0) panics: a live address is never 0).
pub fn cc_ctl_param(r: &u8, k: usize) -> usize {
    let x = r as *const u8 as usize;
    if x != k {
        panic!("R8 address != k");
    }
    x
}

// R9 (false refutation): correct code: the end of a 4-byte array is never its start.
pub fn cc_span(a: &[u8; 4]) -> usize {
    let s = a.as_ptr() as usize;
    let e = a.as_ptr().wrapping_add(4) as usize;
    if e == s {
        panic!("R9 empty span");
    }
    e - s
}
