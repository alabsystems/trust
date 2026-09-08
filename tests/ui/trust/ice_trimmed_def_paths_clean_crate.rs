//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! Regression: a crate that compiles CLEANLY must not ICE the verifier.
//!
//! `native_trust_ir_monomorphic_foreign_callees` decided the R177
//! diverging-panic-terminal gate on `tcx.def_path_str(callee_def_id)`, and
//! `def_path_str` runs the `trimmed_def_paths` query. rustc treats that query as
//! diagnostics-only and asserts the caller goes on to emit one
//! (`rustc_errors/src/lib.rs:478`, `must_produce_diag`). The gate runs over every
//! std callee of every body, so a crate with nothing wrong in it set the flag and
//! then had no diagnostic to satisfy it:
//!
//!     thread 'rustc' panicked at compiler/rustc_errors/src/lib.rs:478:17:
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!
//! One `wrapping_add` was enough. Measured on the sealed trust-6500fd4d against
//! the fix (stage1 adc1cb536): exit 101 before, exit 0 after. It passed before
//! only under `-Ztrust-verify=off` — the one flag verification exists to make
//! unnecessary. Any clean crate calling a std method reproduced it, which is
//! most of them.
//!
//! ── THIS FILE MUST EMIT NO DIAGNOSTICS AT ALL ────────────────────────────────
//!
//! Not one warning, and not one `note:` either. `must_produce_diag` is satisfied
//! by ANY emission, so a single diagnostic anywhere in the crate hides the ICE
//! and the test silently stops testing. Two drafts died this way, both measured
//! against the UNPATCHED compiler, which is the only check that means anything:
//!
//!   * a `fn main() {}` under `--crate-type=lib` -> `warning: function `main` is
//!     never used` -> exit 0, no panic.
//!   * a `pub fn sum(xs: &[u8]) -> u32` looping with `wrapping_add` -> its
//!     obligation PROVES, the verifier prints `note: Trust verification: 1
//!     proved, ...` -> exit 0, no panic. It was added "so the gate is exercised
//!     rather than merely reached", and it is exactly what neutered the test.
//!
//! So the shape here is deliberate and fragile: a lib crate, no `main`, every
//! item `pub` (no dead-code warnings), and only bodies whose obligations do NOT
//! discharge into a printed report. Before trusting a green from this file after
//! any edit, re-measure it against a compiler WITHOUT the fix and confirm it
//! still exits 101. A regression test that cannot fail is not a regression test.
//!
//! ── THE HALF THAT WAS NOT A CRASH ────────────────────────────────────────────
//!
//! Trimming SHORTENS a path to its unambiguous tail, while every pattern in
//! `is_diverging_panic_or_abort_terminal` is anchored on a separator
//! (`ends_with("::unwrap_failed")`, `ends_with("::raw_vec::handle_error")`, …).
//! So on a build that DID emit a diagnostic there was no crash and the gate
//! quietly failed OPEN instead: a trimmed `unwrap_failed` matches nothing, the
//! R177 decline stops firing, and the diverging terminal is bundled after all —
//! decided by whether an unrelated warning happened to print. A fail-closed gate
//! whose verdict depends on diagnostic context is not fail-closed.
//!
//! Fix: `with_no_trimmed_paths!` at both gate sites (the R177 terminal gate and
//! the thiserror TCB probe). A rendered path a GATE reads is not diagnostic text
//! and must not vary with diagnostic context.

pub fn add(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

pub fn checked(a: u8, b: u8) -> Option<u8> {
    a.checked_add(b)
}

pub fn saturating(a: u8, b: u8) -> u8 {
    a.saturating_add(b)
}
