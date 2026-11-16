//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_lowering.rs`: a fn whose SOURCE uses
//! `unsafe` (it reads the first byte of what it is handed through a raw
//! pointer: it only reads, and is sound, but the check does not read what
//! `unsafe` code of such a crate does).

pub fn peek<T>(x: &mut T) -> u8 {
    if std::mem::size_of::<T>() == 0 {
        return 0;
    }
    unsafe { *(x as *mut T as *const u8) }
}
