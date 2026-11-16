//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_s4e_f5_handed_out_async_block_no_entry.rs` (review 6 of
//! the review-14 build): a fn that RETURNS an `async` block (the long-hand of
//! an `async fn`) which READS one byte of the value it is handed in `unsafe`
//! (sound: it writes nothing), and the same as an `async fn`.
pub trait Make { type Out; }
pub union Pun<T> { pub t: *mut T, pub b: *mut ::core::mem::MaybeUninit<u8> }
pub fn peek_block<'a, M: Make>(a: &'a mut M::Out) -> impl ::core::future::Future<Output = u8> + 'a where M::Out: 'a {
    async move { let pa: *mut M::Out = a; unsafe {
        let q = Pun::<M::Out> { t: pa }.b;
        let _b: ::core::mem::MaybeUninit<u8> = if ::core::mem::size_of::<M::Out>() > 0 { ::core::ptr::read_volatile(q) } else { ::core::mem::MaybeUninit::uninit() };
        ::core::mem::size_of::<M::Out>() as u8
    } }
}
pub async fn peek_async<M: Make>(a: &mut M::Out) -> u8 { let pa: *mut M::Out = a; unsafe {
        let q = Pun::<M::Out> { t: pa }.b;
        let _b: ::core::mem::MaybeUninit<u8> = if ::core::mem::size_of::<M::Out>() > 0 { ::core::ptr::read_volatile(q) } else { ::core::mem::MaybeUninit::uninit() };
        ::core::mem::size_of::<M::Out>() as u8
    } }
