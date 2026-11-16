//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! A `&str` variable captured WHOLE (`|| s`) — the thin `s[]` capture.
//!
//! CORRECTED 2026-09-07. This file was written as the pin of wave-FUC's
//! "singleton `&str` capture" lane (the `s[Deref]` shape), and it never pinned
//! it: `|| s` returns the variable itself, so rustc captures `s[]` — an upvar of
//! type `&&str`, THIN — and the ordinary thin lane lowers it. Measured with
//! `#[rustc_capture_analysis]` on the sealed toolchain: `|| s` -> "Min Capture
//! s[] -> Immutable"; `|| s.len()` -> "Min Capture s[Deref] -> Immutable". The
//! lane this file claimed to pin was the one that produced
//! `OperandTypeMismatch { op: "extract_field", expected: "fatptr<str>", actual:
//! "ptr" }` on every real repo (`ny-claims`, `ny-cert`, `ay-param`,
//! `clap_builder`), and it was REMOVED that day — see
//! `trust_ir_lower_fat_str_upvar_extract_field.rs`, which pins both faces and
//! the refusal. What THIS file still pins, and keeps pinning: a whole-variable
//! `&str` capture lowers through the thin lane and runs. A test that cannot
//! fail is not a test; a test that pins something other than its header says
//! is worse, because the header is what the next reader trusts.

pub fn capture_str(s: &str) -> usize {
    let c = || s;
    c().len()
}

pub fn capture_str_indirect() -> usize {
    let s: &str = "hello";
    let c = || s;
    c().len()
}

fn main() {
    assert_eq!(capture_str("abcd"), 4);
    assert_eq!(capture_str_indirect(), 5);
}
