//@ needs-trust-verify
//@ revisions: strict default
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: refuses it"}
//! The per-member policy-B row states why it stopped (RUNTIME-CHECKED-NO-STOP-CAUSE-1).
//!
//! `v.chunks(2).count()` keeps a bundled core member's internal Assert under the
//! runtime-checked disposition, so the function publishes one `runtime_checked` row from
//! `trust-std-member-runtime-check`. Before: its reason carried no `[stop:…]` token
//! (pack 16387, 2026-11-13: `... and \`-Ztrust-policy=certify\` refuses it"}`), so
//! `StopCause::of_outcome` read it as `unclassified` and targo ended a clean crate
//! `COULD NOT RUN` (exit 3). The row was never dispatched to a prover, which is the same
//! on every host and every load: `not-dispatched`. Its grade is unchanged — not counted
//! verified, and `certify` refuses it. The clock variant (`wall-backstop`, when the
//! deadline declined the native run) and the stripping of a forged claim are unit-tested
//! in `trust_verify/runtime_checked_std_member/tests.rs` and `trust_verify/tests.rs`.

pub fn h(v: &[u8]) -> usize {
    v.chunks(2).count()
}

//~? RAW "outcome":"runtime_checked","solver":"trust-std-member-runtime-check","time_ms":0,"reason":"bundled std/core/alloc member runtime check (policy B): an internal Assert of an authentic sysroot member that no row of this function discharges is left to rustc's runtime check under vanilla Rust semantics; the function is not counted verified, and `-Ztrust-policy=certify` refuses it [stop:not-dispatched]"}
