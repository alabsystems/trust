//@ needs-trust-verify
//@ revisions: default strict advisory memory_safe certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[strict] check-pass
//@[advisory] check-pass
//@[memory_safe] check-fail
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: "kind":"no_obligations"
//! A zero-obligation body charged the `GlobalAlloc` premise keeps the honest
//! `native-verification-gap` row it owes (2026-10-03).
//!
//! An rlib does not choose the final link's allocator, so since 2026-10-02 every rlib
//! body that may reach a global-allocator shim is charged the discharged
//! `contract:global-alloc-dealloc-panic-free` premise (`skipped`). The transport's
//! zero-obligation branch was guarded by "no global-alloc disposition", so a charged
//! body was diverted to the policy rows and the gap row the branch owed was dropped.
//!
//! MEASURED on stage-1 `6011b74bad` with this file's flags: `q5` — whose zero-obligation
//! run is NOT vacuously clean (`TRUST_PF_REG_TRACE`: `all_calls_proven=false`; its
//! uncharged whole-program twin publishes the gap row) — published ONLY the premise row
//! (`"unknown":1,"skipped":1,"total":1`) under every policy here, each rc 0, and the
//! crate summary read `total_unknown` 3 of `total_obligations` 3. targo's strict and
//! memory-safe lanes grade that lone `assumed` premise CONDITIONAL-PASS; the unknown
//! gap row owes INCONCLUSIVE.
//!
//! Lines below pin the fixed wire: `q5` publishes the gap row FOLLOWED by the premise
//! row; `bx` (`Box::new`, a clean run, charged) publishes the premise row first, with no
//! gap row; `rs` (no allocator reach, so uncharged, and unclean) publishes its gap row
//! alone; and no body here mints the synthetic `no_obligations` row (the forbid-output
//! above). The crate summary's 4 rows and 2 skipped then leave `q5` exactly 2 rows and
//! `bx` 1. Each pin is on a different output line: compiletest lets one line satisfy
//! only one `RAW` annotation, so `q5`'s own count is read from the summary. The fix is
//! transport-only: it moves no exit code, and the rows above are the same under every
//! policy here.
//!
//! ZERO-ROW-GATE (2026-10-10, docs/DECISION_QUEUE.md): the `default` and `strict`
//! revisions are now refused. `q5` and `rs` publish the `unknown` gap row, and the
//! strict gate's empty-inventory accept now reads the same predicate that chose that
//! row (`zero_obligation_native_vacuously_clean`), so trustc's exit status agrees
//! with the row instead of exiting 0 beside it. The published rows are unchanged;
//! `bx` (clean, charged only the discharged premise) still passes.
//!
//! The `memory_safe` and `certify` revisions are refused, by a different gate. `q5` and
//! `rs` hand a std function item (`Instant::now`, `RandomState::new`) to generic code
//! inside `AssertUnwindSafe`, and since SYS-CALLABLE-1
//! (`sysroot_fn_item_handed_to_generic_code.rs`) those two policies resolve such an
//! item only when its own MIR is shown unable to panic. MEASURED on the stage 1 that
//! carries both fixes: `q5` and `rs` are refused under both policies, `bx` is not,
//! and the published rows are byte-identical to the default revision's. Before that
//! gate both revisions built exit 0.
use std::collections::hash_map::RandomState;
use std::panic::AssertUnwindSafe;
use std::time::Instant;

pub fn q5(o: Option<Instant>) -> Instant {
    o.unwrap_or_else(AssertUnwindSafe(Instant::now))
}

pub fn bx() -> Box<u8> {
    Box::new(7)
}

pub fn rs(o: Option<RandomState>) -> RandomState {
    o.unwrap_or_else(AssertUnwindSafe(RandomState::new))
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): `q5` and `rs` are
// no longer zero-obligation bodies. Their call into the bundled `unwrap_or_else` body now
// carries the counted panic-freedom aggregate the soundness line mints for such a call
// (docs/KNOWN_HAZARDS.md, "A may-panic MARKER is only as good as its CARRIER"), one
// `runtime_checked` row, so the zero-obligation branch and its gap row are not reached and
// ZERO-ROW-GATE no longer refuses them: `default` and `strict` report the runtime-checked row
// and build (`check-pass`), `certify` refuses it, and `memory_safe` and `certify` keep their
// SYS-CALLABLE-1 refusals below. `q5` still publishes its premise row after its own row;
// `bx` still publishes the premise row alone; no body mints `no_obligations` (the forbid).
// Re-pinned 2026-10-18 (1.101 toolchain): `rs` is now ALSO charged the
// global-alloc premise — its `RandomState::new` call graph reaches an
// allocator shim again (thread-local key initialization on this std), so
// the crate carries 5 obligations (3 skipped premises) and each charged
// body's summary tallies its premise row. The semantic pins are unchanged:
// the premise row is published, no body mints `no_obligations`, and the
// per-policy exit codes below are as before.
// Re-pinned 2026-10-26 (GLR-1, docs/DECISION_QUEUE.md): under `memory_safe` and
// `certify` the indirect-call gate refuses `q5` and `rs` (SYS-CALLABLE-1 does not resolve
// the std item they hand to generic code), and that refusal now publishes an `unknown`
// `native-verification-gap` row on the body, so each of the two bodies reads 2 unknown
// of 3 and the crate 5 unknown of 7. `default`, `strict` and `advisory` resolve the item,
// the gate refuses nothing, and their rows are unchanged. `bx` is the same everywhere.
//~? RAW "results":[{"kind":"contract:global-alloc-dealloc-panic-free"
//[default,strict,advisory]~? RAW "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":2}
//[default,strict,advisory]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"zero_obligation_charged_body_keeps_gap_row","functions_analyzed":3,"functions_verified":0,"total_proved":0,"total_failed":0,"total_unknown":3,"total_timed_out":0,"total_skipped":3,"total_runtime_checked":2,"total_obligations":5}
//[memory_safe,certify]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":3}
//[memory_safe,certify]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":3}
//[memory_safe,certify]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"zero_obligation_charged_body_keeps_gap_row","functions_analyzed":3,"functions_verified":0,"total_proved":0,"total_failed":0,"total_unknown":5,"total_timed_out":0,"total_skipped":3,"total_runtime_checked":2,"total_obligations":7}
//[memory_safe]~? RAW Trust memory-safe verification failed for `zero_obligation_charged_body_keeps_gap_row::q5`: a function called through a fn pointer or handed to generic code as a value
//[memory_safe]~? RAW Trust memory-safe verification failed for `zero_obligation_charged_body_keeps_gap_row::rs`: a function called through a fn pointer or handed to generic code as a value
//[certify]~? RAW Trust strict verification failed for `zero_obligation_charged_body_keeps_gap_row::q5`
//[certify]~? RAW Trust strict verification failed for `zero_obligation_charged_body_keeps_gap_row::rs`
//[memory_safe,certify]~? RAW `std::time::Instant::now` is a std/core/alloc function handed to generic code as a value
//[memory_safe,certify]~? RAW `std::hash::RandomState::new` is a std/core/alloc function handed to generic code as a value
//[default,strict]~? RAW Trust verification advisory for `zero_obligation_charged_body_keeps_gap_row::q5`: 1 obligation(s) were not fully verified
//[default,strict]~? RAW Trust verification advisory for `zero_obligation_charged_body_keeps_gap_row::rs`: 1 obligation(s) were not fully verified
