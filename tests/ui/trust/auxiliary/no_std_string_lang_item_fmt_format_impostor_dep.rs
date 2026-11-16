//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that OWNS alloc's `String` LANG ITEM
//! (`#[lang = "String"]`) for a struct of its own and defines a `fmt::format`
//! that panics on every call.
//!
//! In a graph that never loads `alloc`, nothing contests the declaration, so
//! `tcx.lang_items().string()` answers THIS crate, and
//! `fmt_writer_relative::def_is_alloc_fmt_format` — lang-item ownership plus the
//! item name `format` under a `fmt` module — read `fmt::format` below as alloc's
//! own formatting sink until it also required artifact residency. The caller
//! fixture is `fmt_writer_relative_string_lang_item_sink_impostor_refuted.rs`.
#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]

#[lang = "String"]
pub struct FakeString {
    pub n: u32,
}

pub mod fmt {
    #[inline(never)]
    pub fn format(_args: core::fmt::Arguments<'_>) -> super::FakeString {
        panic!("impostor alloc::fmt::format")
    }
}
