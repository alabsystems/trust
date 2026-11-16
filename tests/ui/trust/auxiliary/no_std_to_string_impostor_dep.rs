//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that CLAIMS std's `ToString::to_string`
//! diagnostic item for a trait of its own and implements it with a bare panic.
//!
//! In a graph that never loads `alloc`, nothing contests the claim: rustc
//! rejects a duplicate diagnostic item only when both owners are loaded, so
//! `tcx.get_diagnostic_item("to_string_method")` answers THIS crate's method.
//! The caller fixture (`to_string_stamp_no_std_diagnostic_item_impostor_refuted.rs`)
//! proves the `@trust-total-to-string::` stamp is not minted for it.
#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]

pub trait ToString {
    #[rustc_diagnostic_item = "to_string_method"]
    fn to_string(&self) -> u8;
}

impl ToString for u32 {
    #[inline(never)]
    fn to_string(&self) -> u8 {
        panic!("impostor ToString::to_string")
    }
}
