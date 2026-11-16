//@ revisions: off on env
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@[env] compile-flags: -Ztrust-verify=on
//@[env] rustc-env:TRUST_NO_VERIFY=1
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
//!
//! The `env` revision pins the third route: `TRUST_NO_VERIFY=1` with NO
//! announcing parent — what a user gets from `export TRUST_NO_VERIFY=1` in
//! their shell. Until 2026-09-14 this compile checked nothing and printed
//! nothing, the one silent off-switch the four-claims audit found
//! (docs/audits/2026-09-14-four-claims-audit.md §2.6). The only production
//! setters of that variable are the two bootstrap shims, and they run under
//! `TRUST_VANILLA_ANNOUNCED=1`, so they stay quiet by the marker — which is
//! exactly the marker this test unsets, so the note must appear here.
//!
//! It pairs the variable with an explicit `-Ztrust-verify=on`, and that is the
//! STRONGER pin, not a concession to compiletest's opt-in validator. The driver
//! applies the variable as a post-parse override
//! (`rustc_driver_impl::apply_trust_verify_override`, run AFTER
//! `build_session_options`), so it BEATS the flag wherever the flag sits in
//! argv — argv last-wins does not apply. Measured 2026-09-16 on stage1
//! 611f4f9086: `-Ztrust-verify=on` plus `TRUST_NO_VERIFY=1` compiles nothing
//! and prints the note; the same compile without the variable verifies and
//! prints nothing. So this revision measures the override ITSELF — a
//! verification-ON compile turned off by the environment — where a
//! flagless spelling could not: compiletest's `IsolatedOff` lane appends its
//! own `-Ztrust-verify=off` to every command it builds
//! (`compiletest/src/common.rs`, `configure_trust_verification_isolation`), so
//! a revision with no flag of its own would have produced the note through the
//! FLAG route and pinned nothing about the variable.

pub fn could_be_verified(x: u32) -> u32 {
    x
}

//[off]~? NOTE compiled WITHOUT Trust verification
//[env]~? NOTE compiled WITHOUT Trust verification
