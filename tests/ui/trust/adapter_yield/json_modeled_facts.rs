//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --crate-type lib
//@ compile-flags: --error-format=human
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@[off] forbid-output: "modeled_facts":
//@ dont-check-compiler-stderr
//! D2 tier 1 (2026-09-24): the JSON transport NAMES the modeled fact a
//! function's rows rest on. A consumer of `FunctionTransportResult` sees
//! `modeled_facts: ["ADAPTER_YIELD: …"]` beside proved rows and must never
//! read them as unconditional; a function resting on no modeled fact carries no
//! field at all (the `off` revision, where the closure is refused and nothing
//! is installed).
//!
//! Human error format on purpose: `emit_transport_payload` then writes each
//! `TRUST_JSON:` row as a raw stderr line, which the RAW pin at the bottom
//! reads. Under compiletest's default JSON error format the row would ride
//! inside a `note:` envelope instead (see `json_output_contract_only_no_ice.rs`
//! for the same choice and why the annotation sigil must not appear in prose).
//!
//! The `off` forbid names the JSON FIELD (`"modeled_facts":`): the bare word also
//! matches this file's own name in every row's path. Until 2026-10-02 compiletest
//! matched a `forbid-output` pattern with its leading space, so the bare word was
//! never found either and the gate was vacuous.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): rc=1, the closure
//! row is `failed` and its function row has no such field.

pub fn all_zero(a: &[u8; 8]) -> bool {
    (0..8).all(|i| a[i] == 0)
}

//[on]~? RAW "modeled_facts":["ADAPTER_YIELD: core `Iterator::all` over `0..8` invokes this closure only on items it yields; assumed: item parameter `_2` has value in [0, 8)
//[off]~? RAW Trust strict verification failed for `json_modeled_facts::all_zero::{closure#0}`: 1 obligation(s) were not fully verified
// ZERO-ROW-GATE (2026-10-10) refused `all_zero` in `on` (a zero-row body whose `all` call no
// registry discharged). Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103):
// the gate now reads the drive-only consumer lane's decision for that call
// (VERIFIED-CALLABLE-ZERO-ROW-PARITY), so `on` builds; the `modeled_facts` row above is
// this file's subject and is unchanged.
