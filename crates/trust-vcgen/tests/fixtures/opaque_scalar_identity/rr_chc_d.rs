// Re-review probes D, lens chc: (1) the pre-fix leak of a pointer check's size_of
// into the user's size_of (does the fix close it?), (2) more user-level aliasing
// families (widths, signedness, nested generics, mixed with a pointer check).
#![allow(clippy::all)]
use std::marker::PhantomData;
use std::mem::{align_of, size_of};

#[derive(Clone, Copy)]
pub struct Z<T> {
    pub t: PhantomData<T>,
}

// D1: the read's null check (size_of::<Z<T>>() == 0 always) passes for null p;
// the user's size_of::<T>() != 0 for T = u8. Shared symbol would make the
// passed check say p != 0 and prove the panic unreachable.
pub unsafe fn check_into_user<T>(p: *mut Z<T>) -> usize {
    let _z = unsafe { (*p).t };
    if const { size_of::<T>() } != 0 && (p as usize) == 0 {
        panic!("null with sized T");
    }
    1
}

// D2: the alignment check's align_of::<A<T>>() vs the user's align_of::<T>().
#[derive(Clone, Copy)]
pub struct A<T> {
    pub b: u8,
    pub t: PhantomData<T>,
}
pub unsafe fn align_check_into_user<T>(p: *mut A<T>) -> u8 {
    let v = unsafe { (*p).b };
    // A<T> has align 1; for T = u64, align_of::<T>() == 8 and an odd p reaches the panic.
    if const { align_of::<T>() } == 8 && (p as usize) % 2 == 1 {
        panic!("odd p with 8-aligned T");
    }
    v
}

// D3: two u32-width opaque constants.
pub trait W {
    const N: u32;
}
pub fn u32_assoc<A: W, B: W>() -> u32 {
    if A::N == 0 && B::N == 1 {
        panic!("u32 differ");
    }
    A::N
}

// D4: two i64 (signed) opaque constants.
pub trait S64 {
    const V: i64;
}
pub fn i64_assoc<A: S64, B: S64>() -> i64 {
    if A::V < 0 && B::V > 0 {
        panic!("signs differ");
    }
    A::V
}

// D5: nested generics: size_of::<Vec<T>>() vs size_of::<Option<T>>().
pub fn nested_sizes<T>() -> usize {
    let a = const { size_of::<Vec<T>>() };
    let b = const { size_of::<Option<T>>() };
    if a == 24 && b == 1 {
        panic!("vec 24, option 1");
    }
    a
}

// D6: a user size_of in a loop guard vs another after the loop.
pub fn loop_alias<T, U>(n: usize) -> usize {
    let mut i = 0;
    while i < n && const { size_of::<T>() } == 0 {
        i += 1;
    }
    if i == n && n > 0 && const { size_of::<U>() } == 4 {
        panic!("loop ran with zst T and 4-byte U");
    }
    i
}

// D7: const generic array length vs an unevaluated const of another param.
pub fn cg_len<const N: usize, T>(a: [u8; N]) -> usize {
    let s = const { size_of::<T>() };
    if a.len() == 3 && s == 0 {
        panic!("len 3 zst");
    }
    s
}
