// Confirmer probes (lens chcconfirm), finding 2: unevaluated generic constants.
// Written independently of the hunter's file.
#![allow(clippy::all)]
use std::marker::PhantomData;
use std::mem::{align_of, size_of};

// K1: size_of::<T>() vs size_of::<U>(). cc_k_sizes::<u8, u64>: 1 != 8: panics.
pub fn cc_k_sizes<T, U>() -> usize {
    let a = const { size_of::<T>() };
    let b = const { size_of::<U>() };
    if a != b {
        panic!("K1 sizes differ");
    }
    a
}

// K2: align_of::<T>() vs size_of::<U>(). cc_k_align_size::<u16, [u8; 3]>: 2 != 3.
pub fn cc_k_align_size<T, U>() -> usize {
    let a = const { align_of::<T>() };
    let s = const { size_of::<U>() };
    if a != s {
        panic!("K2 align != size");
    }
    s
}

// K3: two const-generic expressions. ::<3, 5>: 6 != 10: panics.
pub fn cc_k_cexpr<const N: usize, const M: usize>() -> usize {
    let x = const { N * 2 };
    let y = const { M * 2 };
    if x != y {
        panic!("K3 differ");
    }
    x
}

// K4: associated consts of two type params (usize).
pub trait Kv {
    const V: usize;
}
pub fn cc_k_assoc<A: Kv, B: Kv>() -> usize {
    if A::V != B::V {
        panic!("K4 assoc differ");
    }
    A::V
}

// K5: u32 associated consts.
pub trait K32 {
    const W: u32;
}
pub fn cc_k_u32<A: K32, B: K32>() -> u32 {
    if A::W != B::W {
        panic!("K5 u32 differ");
    }
    A::W
}

// K6: u8 associated consts (a third width).
pub trait K8 {
    const B: u8;
}
pub fn cc_k_u8<A: K8, B: K8>() -> u8 {
    if A::B != B::B {
        panic!("K6 u8 differ");
    }
    A::B
}

// K7: signed i64 associated consts (hunter: declined by MalformedTrustIr).
pub trait Ki {
    const S: i64;
}
pub fn cc_k_i64<A: Ki, B: Ki>() -> i64 {
    if A::S != B::S {
        panic!("K7 i64 differ");
    }
    A::S
}

// K8: nested generic sizes. ::<u8>: size_of::<Vec<u8>>()=24, size_of::<Option<u8>>()=2.
pub fn cc_k_nested<T>() -> usize {
    let a = const { size_of::<Vec<T>>() };
    let b = const { size_of::<Option<T>>() };
    if a != b {
        panic!("K8 nested differ");
    }
    a
}

// K9: a pointer check's size_of (via the rustc null check on *p) next to the user's
// size_of::<T>(). P<T> is a ZST for every T, so the read check passes for a null p;
// the user's size_of::<T>() is 1 for T = u8: cc_k_into_user::<u8>(null) panics.
#[derive(Clone, Copy)]
pub struct P<T> {
    pub t: PhantomData<T>,
}
pub unsafe fn cc_k_into_user<T>(p: *mut P<T>) -> usize {
    let _z = unsafe { (*p).t };
    if const { size_of::<T>() } == 1 && (p as usize) == 0 {
        panic!("K9 null with 1-byte T");
    }
    2
}

// K10: control, a const generic N (a ConstParam, not an unevaluated const) vs
// size_of: should be refuted (hunter: FAILED).
pub fn cc_k_param_ctl<const N: usize, T>() -> usize {
    let s = const { size_of::<T>() };
    if N != s {
        panic!("K10 N != size");
    }
    s
}

// K11 (false refutation): size_of::<T>() + 1 never overflows (sizes are <= isize::MAX).
pub fn cc_k_succ<T>() -> usize {
    let s = const { size_of::<T>() };
    s + 1
}
