// Confirmer probes (lens chcconfirm): the shared symbol on ArithmeticOverflow rows.
#![allow(clippy::all)]
use std::mem::{size_of, transmute};

// O1: end - start reversed: s - (s + 4) underflows (debug: panics).
pub fn cc_span_rev(a: &[u8; 4]) -> usize {
    let s = a.as_ptr() as usize;
    let e = a.as_ptr().wrapping_add(4) as usize;
    s - e
}

// O2: f32 bit patterns: bits(1.0) - bits(2.0) underflows.
pub fn cc_bits_sub(x: f32, y: f32) -> u32 {
    let a: u32 = unsafe { transmute::<f32, u32>(x) };
    let b: u32 = unsafe { transmute::<f32, u32>(y) };
    a - b
}

// O3: size_of::<u8>() - size_of::<u64>() underflows.
pub fn cc_k_sub<T, U>() -> usize {
    let a = const { size_of::<T>() };
    let b = const { size_of::<U>() };
    a - b
}
