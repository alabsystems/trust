//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN

//! **Regression: a path comparison must not arm `must_produce_diag`.**
//!
//! `trust-mir-extract`'s niche-wrap recogniser tested an ADT's def-path with a
//! bare `tcx.def_path_str`. That runs `try_print_trimmed_def_path`, which
//! invokes the `trimmed_def_paths` query, which arms rustc's `must_produce_diag`
//! assertion — "path trimming was computed, so a diagnostic had better follow".
//! The call site builds no diagnostic; it is a pure control-flow test.
//!
//! Under the fail-closed default an error happens to follow and the assertion is
//! satisfied by accident. Under `-Ztrust-policy=advisory` a clean compile emits
//! no error, and `DiagCtxtInner::drop` fires
//!
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!
//! — an ICE naming nothing in the file that caused it. MEASURED 2026-09-07 on
//! trustc 07f9466c4: this exact program ICEs (exit 101) under advisory while
//! exiting 1, a normal refusal, under strict. That made the ADVISORY LANE — the
//! rung every consuming repo's verification ratchet stands on — unusable for any
//! program that prints.
//!
//! `println!` is the trigger only because std's stdio path is what reaches the
//! `UsizeNoHighBit` niche recogniser; nothing about printing is special. The fix
//! routes the comparison through `safe_def_path_str`, the single rendering seam
//! the extractor already uses everywhere else, which wraps `with_no_trimmed_paths`.
//!
//! `build-pass` is the whole assertion: an ICE is not a build failure the harness
//! would otherwise notice as a wrong verdict, so this test pins TERMINATION, not
//! any particular report. Do not add stderr expectations — the point is that the
//! compiler reaches the end of the run at all.

fn main() {
    println!("hello");
}
