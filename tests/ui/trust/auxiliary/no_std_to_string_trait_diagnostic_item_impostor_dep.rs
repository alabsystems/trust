//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that CLAIMS alloc's `ToString` diagnostic
//! item for a TRAIT of its own and implements it for `str` with a bare panic.
//!
//! In a graph that never loads `alloc`, nothing contests the claim: rustc
//! rejects a duplicate diagnostic item only when both owners are loaded, so
//! `tcx.get_diagnostic_name(<this trait>)` answers `ToString`, and the trait is
//! not local to the caller. That was all `typed_self_total_std_call` asked of
//! the trait before it also required artifact residency. The caller fixture is
//! `typed_self_total_to_string_trait_diagnostic_item_impostor_refuted.rs`.
#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]

#[rustc_diagnostic_item = "ToString"]
pub trait ToString {
    #[rustc_diagnostic_item = "to_string_method"]
    fn to_string(&self) -> u8;
}

impl ToString for str {
    #[inline(never)]
    fn to_string(&self) -> u8 {
        panic!("impostor <str as ToString>::to_string")
    }
}
