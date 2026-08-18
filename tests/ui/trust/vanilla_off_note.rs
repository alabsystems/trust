//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ unset-rustc-env:TRUST_VANILLA_ANNOUNCED
//@ check-pass
//! Loud-when-off (design item 6): the explicit `-Ztrust-verify=off` spelling
//! must announce, once per crate, that this compile checked nothing — and the
//! batteries-on lane must NOT emit that note.
//!
//! `unset-rustc-env` removes compiletest's own announced-policy marker
//! (`TRUST_VANILLA_ANNOUNCED`, set beside the harness's managed
//! `-Ztrust-verify=off` isolation flag), so this test observes the compiler
//! default that a raw terminal or coordinator invocation sees. The `off`
//! revision pins the note through its `.stderr`; the `on` revision pins the
//! note's ABSENCE by expecting exactly empty compiler output — the pin
//! discipline `contract_verify_off_no_ice.rs` documents for a missing
//! `.stderr` file. Do NOT add `dont-check-compiler-stderr` to either revision.

pub fn could_be_verified(x: u32) -> u32 {
    x
}

//[off]~? NOTE compiled WITHOUT Trust verification
