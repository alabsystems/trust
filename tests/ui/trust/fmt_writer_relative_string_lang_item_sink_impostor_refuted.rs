//@ needs-trust-verify
//@ aux-build: no_std_string_lang_item_fmt_format_impostor_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION FOR THE RESIDENCY CONJUNCT OF
//! `fmt_writer_relative::def_is_alloc_fmt_format`.
//!
//! The auxiliary crate is `#![no_std]`, declares `#[lang = "String"]` for a
//! struct of its own, and defines a panicking `fmt::format`. This crate never
//! loads `alloc`, so nothing contests the declaration and the dependency OWNS the
//! `String` lang item. While `def_is_alloc_fmt_format` decided identity by that
//! ownership alone, it read the dependency's `fmt::format` as alloc's own
//! `format!` sink, and `body_formats_only_into_recognized_sinks` accepted it as
//! the writer for `P`'s writer-relative `Display`.
//!
//! The IMPOSTOR CALL stayed fail-closed either way (the masked-dispatch crate
//! rule, and the bridge keeps its row), so this is a belt, not a false proof;
//! the refusal lost its writer-relative sink note. MEASURED 2026-09-28 on
//! stage-1 `trustc` at `52113eb46` (origin/main, before the fix): same two
//! errors, no note.
//!
//! Fix the compiler, not this file.
#![no_std]

extern crate no_std_string_lang_item_fmt_format_impostor_dep;

pub struct P;

impl core::fmt::Display for P {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("p")
    }
}

pub fn victim() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `fmt_writer_relative_string_lang_item_sink_impostor_refuted::victim`
    //~| ERROR Trust strict verification failed for `fmt_writer_relative_string_lang_item_sink_impostor_refuted::victim`
    //~| NOTE this body hands its `fmt::Arguments` to a consumer that is not a std formatting sink
    no_std_string_lang_item_fmt_format_impostor_dep::fmt::format(format_args!("{}", P)).n
}
