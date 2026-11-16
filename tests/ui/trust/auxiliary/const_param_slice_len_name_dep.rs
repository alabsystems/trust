//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A library VERIFIED under the advisory policy (so an unproved row is a warning,
//! not a build failure) with the two const-generic spellings of
//! `const_param_slice_len_name.rs` (SLICE-LEN-NAME-1, the const-parameter half).
//! When a parameter's symbol is read as a length, `- 1` is proved and
//! kernel-certified, and its overflow check is elided from the MIR every consumer
//! instantiates.
#![allow(non_upper_case_globals)]

pub fn dec<const n__slice_len: i8>() -> i8 {
    n__slice_len - 1
}

pub fn dec_joined<const _slice_len: i8>() -> i8 {
    _slice_len - 1
}
