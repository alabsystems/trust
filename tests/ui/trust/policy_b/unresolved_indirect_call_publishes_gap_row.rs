//@ needs-trust-verify
//@ revisions: advisory hardened_advisory default strict memory_safe certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[hardened_advisory] compile-flags: -Ztrust-policy=advisory -Ztrust-verify-profile=unix_hardened
//@[strict] compile-flags: -Ztrust-policy=strict
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[certify] compile-flags: -Ztrust-policy=certify
//@[advisory] check-pass
//@[hardened_advisory] check-pass
//@[default] check-fail
//@[strict] check-fail
//@[memory_safe] check-fail
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! GLR-1 (2026-10-25, docs/DECISION_QUEUE.md): a call the indirect-call gate refuses
//! publishes a row on every lane.
//!
//! `function_has_unresolved_indirect_call` is the only thing that charges a call
//! through a fn-pointer value; it runs only on the fail-closed lanes, and its failure
//! had no row. So on the advisory lane a body with at least one counted row and a
//! caller's fn-pointer call published its counted rows alone: MEASURED on the shipped
//! Trust 15698 (trustc 20565c325) with this file's shapes, `q` published its proved
//! division row and the skipped global-alloc premise, `call_opt` its proved `unreach`
//! row and the premise, and `q0` (the review's CE1, under the hardened profile targo
//! uses) its proved hardened division row and the premise, each with no row for the
//! call, while `q(boom, 9, 1)` panics. targo's advisory gate read "0 unproved", exit 0.
//!
//! The fix (`unresolved_indirect_call_gap_row`) adds one `unknown`
//! `native-verification-gap` row naming each refused site. The pins below are that row
//! for `q` and `call_opt` in every revision (and for `q0` under the hardened profile),
//! and the crate summary, whose counts also show that `q_ctl` — the same body with the
//! hook replaced by a value — gains no row. The row moves no exit code: the advisory
//! revisions still build, and every fail-closed revision is refused as before.

/// CE1 with a counted row on the default profile: a provable division beside a
/// caller's fn-pointer hook.
pub fn q(g: fn() -> u8, x: u8, d: u8) -> u8 {
    if x > 3 {
        g()
    } else if d != 0 {
        x / d
    } else {
        0
    }
}

/// Negative control: the same body with the hook replaced by a value (no call).
pub fn q_ctl(g: u8, x: u8, d: u8) -> u8 {
    if x > 3 {
        g
    } else if d != 0 {
        x / d
    } else {
        0
    }
}

/// CE1 exactly as the review wrote it: a zero-obligation body on the default profile
/// (it keeps the generic gap row it already had), one hardened row under
/// `unix_hardened`.
pub fn q0(g: fn() -> u8, x: u8) -> u8 {
    if x > 3 { g() } else { x / 2 }
}

/// The optional-pointer shape (`tests/fn-pointer-witness/fragment/f3_optional_pointer.rs`):
/// a proved `unreach` row for the `None` arm beside the call.
pub fn call_opt(f: Option<fn()>) {
    if let Some(g) = f {
        g()
    }
}

// The row, by its reason (which no other row carries), as the LAST row of `q` and of
// `call_opt` (one output line satisfies one `RAW`, so two copies need both lines), with
// each body's counts: its proved row, the skipped premise and the gap row. Without the
// fix each line ends `"unknown":1,...,"total":2}` and no line carries the reason.
//[advisory,default,strict,memory_safe,certify]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
//[advisory,default,strict,memory_safe,certify]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
// The summary: `q_ctl` is the one verified body and carries no gap row (9 rows; 7
// without the fix, and 10 had `q_ctl` gained one). `q0` keeps the generic gap row of a
// zero-obligation body.
//[advisory,default,strict,memory_safe,certify]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"unresolved_indirect_call_publishes_gap_row","functions_analyzed":4,"functions_verified":1,"total_proved":3,"total_failed":0,"total_unknown":6,"total_timed_out":0,"total_skipped":3,"total_runtime_checked":0,"total_obligations":9}
// Under the hardened profile `q0` is CE1 itself: one proved hardened row, so it carries
// the new row too (12 rows; 9 without the fix).
//[hardened_advisory]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":2,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":4}
//[hardened_advisory]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
//[hardened_advisory]~? RAW the advisory lane this row is the gate's only trace [stop:unsupported]"}],"proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
//[hardened_advisory]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"unresolved_indirect_call_publishes_gap_row","functions_analyzed":4,"functions_verified":1,"total_proved":6,"total_failed":0,"total_unknown":6,"total_timed_out":0,"total_skipped":3,"total_runtime_checked":0,"total_obligations":12}
// The refusals are the gate's own, unchanged: the row adds to the counts beside them.
//[default,strict]~? RAW unproved assumption-panic row — an unresolved indirect call — keeps the function fail-closed
//[default,strict]~? RAW unproved assumption-panic row — an unresolved indirect call — keeps the function fail-closed
//[default,strict]~? RAW unproved assumption-panic row — an unresolved indirect call — keeps the function fail-closed
//[memory_safe]~? RAW a function called through a fn pointer or handed to generic code as a value is not a body this compilation verified
//[memory_safe]~? RAW a function called through a fn pointer or handed to generic code as a value is not a body this compilation verified
//[memory_safe]~? RAW a function called through a fn pointer or handed to generic code as a value is not a body this compilation verified
//[default,strict,certify]~? RAW Trust strict verification failed for `unresolved_indirect_call_publishes_gap_row::q`
//[default,strict,certify]~? RAW Trust strict verification failed for `unresolved_indirect_call_publishes_gap_row::call_opt`
