//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_s4e_f4_note_entry_for_non_adt_impl_method_names_two.rs`
//! (review 6 of the review-14 build): a trait with a provided method that
//! READS one byte of a value in `unsafe` (sound: it writes nothing), used as
//! the default for `Wrap<T>` and overridden in an impl for `&mut T`.
pub union Pun<T> { pub t: *mut T, pub b: *mut ::core::mem::MaybeUninit<u8> }
pub trait Poke {
    fn poke(&mut self) -> u8 where Self: Sized { let p: *mut Self = self; unsafe {
        let q = Pun::<Self> { t: p }.b;
        let _b: ::core::mem::MaybeUninit<u8> = if ::core::mem::size_of::<Self>() > 0 { ::core::ptr::read_volatile(q) } else { ::core::mem::MaybeUninit::uninit() };
        ::core::mem::size_of::<Self>() as u8
    } }
}
pub struct Wrap<T>(pub T);
impl<T> Poke for Wrap<T> {}
impl<'a, T> Poke for &'a mut T {
    fn poke(&mut self) -> u8 { let p: *mut T = &mut **self; unsafe {
        let q = Pun::<T> { t: p }.b;
        let _b: ::core::mem::MaybeUninit<u8> = if ::core::mem::size_of::<T>() > 0 { ::core::ptr::read_volatile(q) } else { ::core::mem::MaybeUninit::uninit() };
        ::core::mem::size_of::<T>() as u8
    } }
}
