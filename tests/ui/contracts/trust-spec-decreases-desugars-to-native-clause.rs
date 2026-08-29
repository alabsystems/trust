//! Trust (D4): `#[trust::decreases(e)]` IS `fn f(..) decreases e`.
//!
//! THE DEFECT THIS LOCKS OUT. Design of record v3 rules that the attribute
//! spellings are "compat desugaring only" of the first-class clause surface.
//! For `decreases` that was not true in either direction — MEASURED on the
//! sealed toolchain `trust-e26541e3`, one source file, three surfaces:
//!
//!   surface                                   `decreases n`   `decreases 0`
//!   --------------------------------------    -------------   --------------
//!   native `fn g(..) -> u32 decreases n`      termination/    2x unknown
//!                                             proved          (fail-closed)
//!   `#![register_tool(trust)]` tool attribute  IDENTICAL       IDENTICAL
//!   the same bytes + `--extern trust=<shim>`   E0433           E0433
//!
//! So the clause worked, with exactly native semantics, right up until the
//! crate LINKED the compatibility shim — and then the same source bytes became
//! a hard compile error. ay's verification ratchet passes `--extern trust=`
//! (`scripts/ci/trust_verification_ratchet_gate.sh`), so that was ay's live
//! configuration: a crate that must also build on stock Rust could not state a
//! termination measure at all, because the first-class clause is raw grammar
//! that stock rustc rejects outright and the attribute spelling did not exist.
//!
//! WHY THIS IS A DESUGARING AND NOT A SECOND IMPLEMENTATION. The builtin does
//! not build a clause object of its own. It re-emits the contextual clause
//! ident followed by the author's payload tokens UNWRAPPED, so the parser
//! receives byte-for-byte the token stream a native author would have written.
//! The clause is then parsed by `parse_trust_native_clause`, stored in
//! `FnContract::trust_native_decreases`, and lowered by the one existing path.
//! Divergence is not merely fixed here, it is unrepresentable: there is one
//! parse and one lane.
//!
//! WHAT THIS FILE PROVES. Each case below fails with a diagnostic that ONLY
//! the native clause lane emits. That is the evidence that the desugaring
//! actually reached that lane rather than some attribute-shaped lookalike:
//! before this change the first case was E0433 ("cannot find `decreases` in
//! `trust`") and the scope of the measure was never examined at all.
//!
//! SUPERSEDED `tests/ui/contracts/trust-spec-decreases-not-exported.rs` from
//! branch `fix/trust-invariant-erasure-refusal`, which pinned the E0433 as
//! intended behaviour on the reasoning that any `decreases` export would be a
//! silent passthrough. That reasoning is sound for a PASSTHROUGH and does not
//! hold for a desugaring: the resolver replaces the shim's proc macro with the
//! builtin before expansion, exactly as it already does for `requires` and
//! `ensures`, so the passthrough body never runs when verification is on. The
//! branches met in the D1+D2+D3+D4 integration and that file was deleted there.
//!
//! Compiletest runs the `ui` suite with `-Z trust-verify=off`, and the
//! resolver's substitution is deliberately gated on verification being
//! enabled, so the explicit flag below is load-bearing: without it this file
//! would exercise the shim passthrough and none of these diagnostics fire.
//!
//! WHY REVISIONS AND NOT ONE COMPILATION. The three diagnostics are raised in
//! three DIFFERENT compilation phases, and the first two abort the compiler
//! before the third phase runs:
//!
//!   revision   diagnostic                              raised by
//!   --------   -------------------------------------   ---------------------
//!   `empty`    "expected a predicate expression ..."    the PARSER
//!                                                       (`parse_trust_native_clause`)
//!   `nonfn`    "contract annotations can only be        MACRO EXPANSION
//!               used on functions"                      (`expand_contract_clause`)
//!   `scope`    "source-contract variable `limit`        the MIR-time
//!               is not in scope"                        `TrustVerify` pass
//!
//! MEASURED on stage1 `1.99.0-dev (c713728b4 2026-08-27)`: with all three cases
//! in ONE crate the compiler emits exactly the parse error and the expansion
//! error and then aborts, so `scope` — the case this file calls its primary
//! evidence, the one that shows the measure's SCOPE is examined at all — never
//! fires and cannot be asserted. Compiled one at a time, each of the three
//! fires alone and with the message quoted below. Splitting into `//@ revisions`
//! is therefore not a workaround: it is the only arrangement in which all three
//! claims are actually checked.
//@ revisions: scope empty nonfn
//@ proc-macro: trust.rs
//@ edition: 2021
//@ compile-flags: -Z trust-verify=on

#![allow(dead_code)]

// The measure names something that is not a parameter. The NATIVE lane checks
// clause scope and refuses; the tool-attribute lane silently degrades this to
// an unproved obligation, and the old extern lane never got far enough to look.
#[cfg(scope)]
#[trust::decreases(limit)]
//[scope]~^ ERROR invalid `decreases` clause: source-contract variable `limit` is not in scope
fn out_of_scope(n: u32) -> u32 {
    if n == 0 { 0 } else { out_of_scope(n - 1) }
}

// An authored clause with no predicate is an error, not a silent skip
// (design §1.2-6). This is the native clause parser's own diagnostic, and it
// points at the token that TERMINATED the empty payload — the body's `{` —
// exactly as the first-class surface does in
// `tests/ui/trust/native_clause_empty_payload.rs`.
#[cfg(empty)]
#[trust::decreases()]
fn empty_measure(n: u32) -> u32 {
    //[empty]~^ ERROR expected a predicate expression after the contract clause keyword
    if n == 0 { 0 } else { empty_measure(n - 1) }
}

// Same rule as `requires`/`ensures`: a contract annotation on a non-function
// is refused. `invariant` accepting this shape in TOTAL SILENCE is the
// asymmetry the D1 lane removes; `decreases` must never acquire it.
#[cfg(nonfn)]
#[trust::decreases(n)]
//[nonfn]~^ ERROR contract annotations can only be used on functions
struct NotAFunction {
    n: u32,
}

fn main() {}
