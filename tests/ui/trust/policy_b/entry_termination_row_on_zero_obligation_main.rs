//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ revisions: box_dyn_error box_dyn_error_strict dep_type io_error_advisory string_control
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0
//@[box_dyn_error_strict] compile-flags: -Ztrust-policy=strict
//@[io_error_advisory] compile-flags: -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[box_dyn_error] forbid-output: "kind":"no_obligations"
//@[box_dyn_error_strict] forbid-output: "kind":"no_obligations"
//@[dep_type] forbid-output: "kind":"no_obligations"
//@[io_error_advisory] forbid-output: "kind":"no_obligations"
//! The policy-B entry-`Termination` row reaches the JSON transport when `main` has
//! no obligation of its own (2026-10-03).
//!
//! `main`'s return value is dispatched by `lang_start` through `<T as
//! Termination>::report` (its `Debug` on `Err`, its `Drop` always). When `T` reaches
//! foreign or dynamic code, the compiler owes one honest `runtime_checked` row for that
//! dispatch — CONDITIONAL on the default lane, refused under `certify`
//! (`entry_termination_dispatch_reported.rs`). The transport's zero-obligation branch
//! never read that row: it published its own base instead.
//!
//! MEASURED on stage-1 `6011b74bad` with this file's flags, rc 0 on every revision:
//! each charged `main` here published `[no_obligations: proved]` and the crate summary
//! `functions_verified: 1, total_proved: 1, total_runtime_checked: 0`. With
//! `-Ztrust-verify-output=json` alone (what targo reads) nothing disclosed the row, so
//! targo's strict lane would grade PASS where it owes CONDITIONAL-PASS. A `main` that
//! has obligations of its own (`std::env::args().count()`) did publish the row.
//!
//! Lines below pin the fixed wire: the charged revisions publish the entry row as
//! `runtime_checked` and as `main`'s only row (one pin, because compiletest lets one
//! output line satisfy only one `RAW` annotation; it starts inside the row's location,
//! which is `main`'s own span, so each `main` has its own line), the row states its
//! stop (`not-dispatched`, RUNTIME-CHECKED-NO-STOP-CAUSE-1), the function is not counted
//! verified, and the synthetic
//! `no_obligations` row is never minted beside it (the forbid-output above). The
//! `string_control` revision (`Result<(), String>` mints no entry row) still publishes
//! `no_obligations` and counts verified: the uncharged branch is untouched. The exit
//! codes do not move: the fix is transport-only.
#[cfg(dep_type)]
extern crate policy_b_unverified_dep as dep;

#[cfg(any(box_dyn_error, box_dyn_error_strict))]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}

#[cfg(dep_type)]
fn main() -> Result<(), dep::Bomb> {
    Ok(())
}

#[cfg(io_error_advisory)]
fn main() -> Result<(), std::io::Error> {
    Ok(())
}

#[cfg(string_control)]
fn main() -> Result<(), String> {
    Ok(())
}

//[box_dyn_error,box_dyn_error_strict]~? RAW ","line_start":48,"col_start":0,"line_end":50,"col_end":1},"outcome":"runtime_checked","solver":"trust-classifier","time_ms":0,"reason":"entry `Termination::report` dispatch: reported gap (policy B) — a panic in the returned value's `Debug`/`Drop` is a defined abort during error reporting; return `()`, `ExitCode`, or an error type whose `Debug`/`Drop` this crate verifies to close it [stop:not-dispatched]"}],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":1}
//[dep_type]~? RAW ","line_start":53,"col_start":0,"line_end":55,"col_end":1},"outcome":"runtime_checked","solver":"trust-classifier","time_ms":0,"reason":"entry `Termination::report` dispatch: reported gap (policy B) — a panic in the returned value's `Debug`/`Drop` is a defined abort during error reporting; return `()`, `ExitCode`, or an error type whose `Debug`/`Drop` this crate verifies to close it [stop:not-dispatched]"}],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":1}
//[io_error_advisory]~? RAW ","line_start":58,"col_start":0,"line_end":60,"col_end":1},"outcome":"runtime_checked","solver":"trust-classifier","time_ms":0,"reason":"entry `Termination::report` dispatch: reported gap (policy B) — a panic in the returned value's `Debug`/`Drop` is a defined abort during error reporting; return `()`, `ExitCode`, or an error type whose `Debug`/`Drop` this crate verifies to close it [stop:not-dispatched]"}],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":1}
//[box_dyn_error,box_dyn_error_strict,dep_type,io_error_advisory]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"entry_termination_row_on_zero_obligation_main","functions_analyzed":1,"functions_verified":0,"total_proved":0,"total_failed":0,"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":1,"total_obligations":1}
//[string_control]~? RAW {"kind":"no_obligations","description":"function has no panic obligations (trivially panic-free)","outcome":"proved"
//[string_control]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"entry_termination_row_on_zero_obligation_main","functions_analyzed":1,"functions_verified":1,"total_proved":1,"total_failed":0,"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":0,"total_obligations":1}
