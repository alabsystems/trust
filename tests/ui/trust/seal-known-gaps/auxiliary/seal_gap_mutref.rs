//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_s4e_f1_s4e_tied_bare_param_reaches_nothing.rs`,
//! `r6_s4e_f2_abstract_item_at_tied_bare_param.rs` and
//! `r6_s4e_f3_own_code_at_param_sealed_to_holder.rs` (review 6 of the review-14
//! build). SOUND: `MutRef` is an unsafe trait whose contract says `bytes()`
//! gives the target's own bytes, uniquely borrowed, and its only impl is this
//! crate's, for `&mut T`; `swap_mut` byte-swaps the two targets (what
//! `mem::swap` of them does); `swap_bytes` swaps two `&mut T`; `Exactly<X>` is
//! implemented by `X` alone.
pub trait Make { type Out; }
/// # Safety
/// `bytes` gives the address and the size of the value `self` points to,
/// which `self` borrows uniquely (no other live value points to it), valid
/// for reads and writes of that many bytes while `self` lives.
pub unsafe trait MutRef: ::core::ops::DerefMut {
    fn bytes(&mut self) -> (*mut u8, usize);
}
unsafe impl<'a, T> MutRef for &'a mut T {
    fn bytes(&mut self) -> (*mut u8, usize) {
        let p: *mut T = &mut **self;
        (p as *mut u8, ::core::mem::size_of::<T>())
    }
}
/// Swaps what two such pointers point to, by its bytes (what `mem::swap` of
/// the targets does: two distinct live unique borrows of one type).
pub fn swap_mut<P: MutRef>(mut a: P, mut b: P) {
    let (pa, n) = a.bytes();
    let (pb, m) = b.bytes();
    if n == m && n > 0 && pa != pb {
        unsafe { ::core::ptr::swap_nonoverlapping(pa.cast::<::core::mem::MaybeUninit<u8>>(), pb.cast::<::core::mem::MaybeUninit<u8>>(), n) }
    }
}
/// The same, reading only (sound): compares the first bytes.
pub fn peek_mut<P: MutRef>(mut a: P, mut b: P) -> bool {
    let (pa, n) = a.bytes();
    let (pb, _) = b.bytes();
    n > 0 && unsafe { ::core::ptr::read(pa as *const ::core::mem::MaybeUninit<u8>); true } && pa != pb
}
/// The same swap over a pair of them (the fn handles only `(P, P)`).
pub fn swap_pair<P: MutRef>(mut ab: (P, P)) {
    let (pa, n) = ab.0.bytes();
    let (pb, m) = ab.1.bytes();
    if n == m && n > 0 && pa != pb {
        unsafe { ::core::ptr::swap_nonoverlapping(pa.cast::<::core::mem::MaybeUninit<u8>>(), pb.cast::<::core::mem::MaybeUninit<u8>>(), n) }
    }
}
/// Safe: swaps the targets of two `DerefMut` pointers (std's mem::swap).
pub trait SwapPtr { fn swap_ptr(self, other: Self); }
impl<P: ::core::ops::DerefMut> SwapPtr for P where P::Target: Sized {
    fn swap_ptr(mut self, mut other: Self) { ::core::mem::swap(&mut *self, &mut *other) }
}
/// Safe: a free fn doing the same, which names the target type.
pub fn swap_targets<P: ::core::ops::DerefMut>(mut a: P, mut b: P) where P::Target: Sized {
    let pa: *mut P::Target = &mut *a; let pb: *mut P::Target = &mut *b;
    if pa != pb { unsafe { ::core::ptr::swap(pa, pb) } }
}
/// A blanket method over every `MutRef` that swaps the targets in `unsafe`.
pub trait RawSwapTr { fn raw_swap(self, other: Self); }
impl<P: MutRef> RawSwapTr for P {
    fn raw_swap(mut self, mut other: Self) {
        let (pa, n) = self.bytes();
        let (pb, m) = other.bytes();
        if n == m && n > 0 && pa != pb { unsafe { ::core::ptr::swap_nonoverlapping(pa.cast::<::core::mem::MaybeUninit<u8>>(), pb.cast::<::core::mem::MaybeUninit<u8>>(), n) } }
    }
}
/// The swap in a closure the fn runs.
pub fn swap_in_closure<P: MutRef>(a: P, b: P) {
    let f = move |mut a: P, mut b: P| {
        let (pa, n) = a.bytes();
        let (pb, m) = b.bytes();
        if n == m && n > 0 && pa != pb { unsafe { ::core::ptr::swap_nonoverlapping(pa.cast::<::core::mem::MaybeUninit<u8>>(), pb.cast::<::core::mem::MaybeUninit<u8>>(), n) } }
    };
    f(a, b)
}
/// Implemented by `X` alone (sealed: `s::S` cannot be named outside).
mod s { pub trait S<X> {} impl<X> S<X> for X {} }
pub trait Exactly<X>: s::S<X> {}
impl<X> Exactly<X> for X {}
/// Swaps two values by their bytes, in `unsafe` (what mem::swap does).
pub fn swap_bytes<T>(a: &mut T, b: &mut T) {
    let pa: *mut T = a; let pb: *mut T = b;
    unsafe { ::core::ptr::swap_nonoverlapping(pa, pb, 1) }
}
