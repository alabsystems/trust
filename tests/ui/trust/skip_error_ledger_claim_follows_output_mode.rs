//@ needs-trust-verify
//@ revisions: human json
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[json] compile-flags: -Ztrust-verify-output=json
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@[json] dont-require-annotations: NOTE
//@ check-fail
//! A strict skip error may say "this skip is also recorded as an
//! `assumption:<tag>` transport row" only when that row was WRITTEN.
//!
//! RECORD-THEN-RULE writes the row on every policy's skip path, but the row is
//! a `TRUST_JSON` transport line, so it exists only under JSON (or both) output.
//! Under the default human output nothing is written, and an error that claimed
//! a row there would point a reader at an inventory that does not exist.
//!
//! * `human`: the ledger-claim note must be ABSENT. NOTE annotations are
//!   REQUIRED in this revision, so every note on the error is annotated and an
//!   extra one fails it. (`forbid-output` cannot pin this: the error's span is
//!   the whole function, so its rendered snippet quotes the `json` annotation
//!   below.)
//! * `json`: the same note must be PRESENT, naming the tag of the row written.
//!   (NOTE annotations are not required here only because JSON transport output
//!   also reaches the diagnostic stream as `TRUST_JSON` notes; an annotated note
//!   must still be found.)
//!
//! The decision is `skip_record_plan` / `SkipRecordPlan::ledger_claim`
//! (unit-tested); this fixture pins that `run_pass` actually consults it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::skip]
pub fn opted_out(a: u8) -> u8 {
    //~^ ERROR Trust full verification skipped `skip_error_ledger_claim_follows_output_mode::opted_out`: the source DECLARES this gap
    //~| NOTE full verification policy rejected skip reason `UserOptOut`
    //~| NOTE ATTRIBUTION: this is YOUR declaration, not a gap in Trust
    //~| NOTE this skip is not permitted under strict batteries-on verification
    //[json]~| NOTE this skip is also recorded as an `assumption:user-opt-out` transport row
    a
}
