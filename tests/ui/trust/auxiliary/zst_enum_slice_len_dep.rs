//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A library VERIFIED under the advisory policy (so an unproved row is a warning,
//! not a build failure) with the two spellings of `zst_enum_slice_len.rs`
//! (ZST-ENUM-SLICE-LEN-1). While a zero-sized enum's slice length took the
//! `len <= isize::MAX` ceiling, `* 2` was proved and kernel-certified, and its
//! overflow check was elided from the MIR every consumer runs or instantiates.

#[derive(Clone, Copy)]
pub enum One {
    A,
}

pub fn twice_len(a: &[One]) -> usize {
    a.len() * 2
}

pub fn twice_n<const N: usize>() -> usize {
    let a = [One::A; N];
    a.len() * 2
}
