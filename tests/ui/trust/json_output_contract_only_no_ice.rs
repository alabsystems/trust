//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ edition: 2021
//@ dont-check-compiler-stderr
#![crate_type = "lib"]
//! **Regression: a fully proved, contract-only crate must not ICE on the JSON wire.**
//!
//! `trust-thir-lower`'s contract disclosure (`contract_disclosure.rs`, the IR-3
//! `DesignOnly` SpecModule) named each contract-bearing body with a bare
//! `tcx.def_path_str`. That runs the `trimmed_def_paths` query, which arms
//! rustc's `must_produce_diag` assertion — "path trimming was computed, so a
//! diagnostic had better follow" — and the disclosure row is artifact text, not
//! a diagnostic. MEASURED on stage2 `9b4c6b3ab` (the parent of the fix) with
//! THIS file and exactly the header flags above:
//!
//!     $ trustc -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human \
//!              --edition 2021 json_output_contract_only_no_ice.rs
//!     TRUST_JSON:{"type":"function_result", ... "outcome":"proved" ...}   (x2)
//!     TRUST_JSON:{"type":"crate_summary", ... "total_proved":3,"total_failed":0,"total_unknown":0 ...}
//!     thread 'rustc' panicked at compiler/rustc_errors/src/lib.rs:478:17:
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!     exit 101
//!
//! and `RUST_BACKTRACE=1` names the arming caller `install_contract_disclosure`
//! at `crates/trust-thir-lower/src/contract_disclosure.rs:77:28`. The same source
//! (`min2`) ICEd the same way on stage2 `db07002ff` in the measurement round, and
//! the one-line `pub fn keep(x: u32) -> u32 ensures result == x { x }` on both
//! that stage2 and the installed pack.
//!
//! The proved rows and the rlib were written FIRST and the panic came at session
//! teardown, so a consumer that reads rows and ignores the exit status graded an
//! ICE as green (`tests/two-language-programs/wire_grade.py --exit-code` closes
//! that on the grader's side).
//!
//! ── WHY THESE EXACT FLAGS ────────────────────────────────────────────────────
//!
//! `must_produce_diag` is satisfied by ANY emission, so the defect only shows on
//! a compile that emits no diagnostic at all. Three things each hide it:
//!
//!   * TEXT output mode prints `note: Trust verification: N proved, ...`.
//!   * A `clean { }` island prints `note: Clean island kernel-checked: ...`.
//!   * `--error-format=json` — which compiletest passes by DEFAULT and Cargo
//!     always passes — makes `emit_transport_payload` wrap every `TRUST_JSON`
//!     row in a `note:` diagnostic. Only the HUMAN error format writes the rows
//!     with a raw `eprintln!`, which is the raw-trustc wire the measurement used.
//!     Hence the explicit `--error-format=human` above: without it this file
//!     cannot fail and tests nothing. MEASURED on the same stage2 `9b4c6b3ab`:
//!     the identical compile with `--error-format=json` exits 0.
//!
//! So the shape is deliberate and fragile, exactly like its sibling
//! `ice_trimmed_def_paths_clean_crate.rs`: a lib crate, no `main`, one `pub` item
//! (no dead-code warning), a contract that PROVES, no island. Before trusting a
//! green from this file after any edit, re-measure it against a compiler WITHOUT
//! the fix and confirm it still exits 101. A regression test that cannot fail is
//! not a regression test.
//!
//! `build-pass` is the assertion that matters: TERMINATION with exit 0. The
//! `RAW` annotation at the bottom pins that the JSON wire really ran AND that the
//! one function verified — if the flag were ever dropped or renamed this would
//! silently become a text-mode test, which the verification `note:` masks. It is
//! a RAW annotation, not an `error-pattern` directive: under a human error format
//! compiletest reads every stderr line as a RAW diagnostic and makes a matching
//! `error-pattern` FATAL (runtest.rs, `check_expected_errors`). Note that the
//! annotation sigil may not appear anywhere in this prose either — compiletest
//! scans every line of the file, comments included, and a mention in a doc
//! comment is parsed as a second expectation that nothing can satisfy (measured
//! on the first draft of this file). stderr is otherwise unchecked: the function
//! rows carry absolute paths, claim digests and engine detail.
//!
//! The close negative twin is `json_output_contract_only_unproved_stays_rejected.rs`.

pub fn min2(a: u64, b: u64) -> u64
    ensures result <= a
{
    if a < b { a } else { b }
}

//~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"json_output_contract_only_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":3,"total_failed":0,"total_unknown":0
