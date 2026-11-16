//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that OWNS alloc's `String` LANG ITEM
//! (`#[lang = "String"]`) for a struct of its own and gives it a `Deref` impl
//! (core's REAL `Deref` trait) that panics on every call.
//!
//! In a graph that never loads `alloc`, nothing contests the declaration, so
//! `tcx.lang_items().string()` answers THIS crate's struct, and it is not local
//! to the caller. That was all the `<String as Deref>::deref` arm of
//! `typed_self_total_std_call` asked of `Self` before it also required artifact
//! residency. The caller fixture is
//! `typed_self_total_deref_string_lang_item_impostor_refuted.rs`.
#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]

#[lang = "String"]
pub struct FakeString;

impl core::ops::Deref for FakeString {
    type Target = u8;
    #[inline(never)]
    fn deref(&self) -> &u8 {
        panic!("impostor <FakeString as Deref>::deref")
    }
}
