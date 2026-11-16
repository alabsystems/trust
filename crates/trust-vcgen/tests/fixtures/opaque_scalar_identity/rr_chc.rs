// Re-review probes, lens chc / opaque constants (f4a512ad40 + 8ab04409df).
#![allow(clippy::all)]
use std::marker::PhantomData;
use std::mem::{align_of, size_of};

#[derive(Clone, Copy)]
pub struct S<T> {
    pub flag: bool,
    pub v: T,
}

// P01 gvn_cast_zst: the read goes through q = p as *mut U (U may be a ZST); at -O1
// GVN may fold `copy q as *const ()` to `copy p as *const ()`, so the check's
// pointer local is p (pointee S<T>, provably non-ZST) while its size_of is U's.
// T = u8, U = (), p = null: the read passes (ZST), the `&mut *p` borrow panics.
pub unsafe fn gvn_cast_zst<T, U: Copy>(p: *mut S<T>) -> U {
    unsafe {
        let q = p as *mut U;
        let u: U = *q;
        let r = &mut *p;
        r.flag = true;
        u
    }
}

// P02 user_sizes_alias: two user size_of of different types.
// T = (), U = u8 panics.
pub fn user_sizes_alias<T, U>() -> usize {
    let a = const { size_of::<T>() };
    let b = const { size_of::<U>() };
    if a == 0 && b != 0 {
        panic!("sizes differ");
    }
    a + 1
}

// P03 align_vs_size: align_of::<T>() vs size_of::<U>(). T = u8, U = u32 panics.
pub fn align_vs_size<T, U>() -> usize {
    let a = const { align_of::<T>() };
    let s = const { size_of::<U>() };
    if a != s {
        panic!("align != size");
    }
    s
}

// P04 const_expr_nm: two const-generic expressions (unevaluated consts).
// N = 1, M = 2 panics.
pub fn const_expr_nm<const N: usize, const M: usize>() -> usize {
    let x = const { N + 1 };
    let y = const { M + 1 };
    if x != y {
        panic!("N+1 != M+1");
    }
    x
}

// P05 assoc_consts: associated consts of two type parameters.
pub trait K {
    const V: usize;
}
pub fn assoc_consts<A: K, B: K>() -> usize {
    let a = A::V;
    let b = B::V;
    if a != b {
        panic!("A::V != B::V");
    }
    a
}

// P06 const_fn_result: a const fn applied to size_of vs size_of itself.
// T = u16: 4 != 2 panics.
pub const fn sq(x: usize) -> usize {
    x * x
}
pub fn const_fn_result<T>() -> usize {
    let a = const { sq(size_of::<T>()) };
    let b = const { size_of::<T>() };
    if a != b {
        panic!("sq(size) != size");
    }
    a
}

// P07 user_size_vs_check: a pointer check on p (S<T>), then the user's
// size_of::<T>() == 0 panic AND the user's align_of::<T>() pinned via a second
// user constant. T = () panics.
pub unsafe fn user_size_vs_check<T>(p: *mut S<T>) -> bool {
    unsafe {
        let f = (*p).flag;
        let al = const { align_of::<S<T>>() };
        if const { size_of::<T>() } == 0 && al == 1 {
            panic!("zst payload");
        }
        f
    }
}

// P08 two_ptr_two_types: checks on two different pointers of different generic
// pointee types; then a borrow of the second. q null, Z = () reaches the borrow
// panic. The first pointer's check must not leak into the second's.
pub unsafe fn two_ptr_two_types<T, Z: Copy>(p: *mut S<T>, q: *mut Z) -> Z {
    unsafe {
        let _f = (*p).flag;
        let z = *q;
        let r = &mut *q;
        let _ = r;
        z
    }
}

// P09 loop_reseat: the null check on *p passes, then p is reseated from the
// node's next field (may be null) at the back-edge; the borrow at loop head of
// the NEXT iteration must not reuse the old p's non-null fact.
pub struct Node<T> {
    pub next: *mut Node<T>,
    pub v: T,
}
pub unsafe fn loop_reseat<T>(mut p: *mut Node<T>, n: usize) -> usize {
    unsafe {
        let mut i = 0;
        let _first = (*p).next;
        while i < n {
            let r = &mut *p;
            p = r.next;
            i += 1;
        }
        i
    }
}

// P10 call_reseat: a passed null check, then p handed to a callee by &mut that
// may null it, then a borrow.
#[inline(never)]
pub fn maybe_null<T>(p: &mut *mut S<T>, c: bool) {
    if c {
        *p = std::ptr::null_mut();
    }
}
pub unsafe fn call_reseat<T>(mut p: *mut S<T>, c: bool) -> bool {
    unsafe {
        let f = (*p).flag;
        maybe_null(&mut p, c);
        let r = &mut *p;
        r.flag = f;
        f
    }
}

// P11 inline_two_insts: an inlined generic reader instantiated at two types in
// one body (at -O1 both checks are inlined, each with its own pointee).
#[inline(always)]
pub unsafe fn rd<X: Copy>(p: *const X) -> X {
    unsafe { *p }
}
pub unsafe fn inline_two_insts<T: Copy, U: Copy>(p: *mut S<T>, q: *mut U) -> U {
    unsafe {
        let _s = rd(p as *const S<T>).flag;
        let u = rd(q as *const U);
        let r = &mut *q;
        let _ = r;
        u
    }
}

// P12 zst_field_borrow: alignment check FollowProjections: a borrow of a field
// (align_of::<T>()) and a whole read (align_of::<S<T>>()) share the pointer
// local; then the user's align_of::<T>() decides a panic.
pub unsafe fn field_vs_whole<T: Copy>(p: *mut S<T>) -> T {
    unsafe {
        let a = &(*p).v;
        let v = *a;
        let _w = (*p).flag;
        if const { align_of::<T>() } == 1 {
            panic!("align 1");
        }
        v
    }
}

// P13 phantom_fnitem: a pointee that is a ZST for every T but whose fields are
// a PhantomData and a fn item.
pub fn helper() {}
pub unsafe fn null_like<X>(_: &X) -> *mut X {
    std::ptr::null_mut()
}
pub unsafe fn phantom_fnitem<T>(p: *mut (PhantomData<T>, fn())) -> bool {
    unsafe {
        let v = *p;
        let r = &mut *p;
        let _ = r;
        let _ = v;
        true
    }
}
