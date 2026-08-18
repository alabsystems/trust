//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-require-annotations: WARN
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "sha256:$$DIGEST"
//@ normalize-stderr: "trust-mc@\d+\.\d+\.\d+" -> "trust-mc@$$ENGINE"
// Digests are content addresses over the serialized bundle/request bytes —
// they shift on EVERY lowering change on either side of a merge (measured
// 2026-08-14: two consecutive digest-only re-pins in one day). Pin structure,
// normalize the addresses.
//! E6 kernel-import, end-to-end (two-language design §3.1, v3). A program
//! function CALLED inside a spec clause is a DEFINITIONAL use: it is admissible
//! only if the whole-crate facet analysis certifies it `Pure ∧ Total ∧
//! Deterministic ∧ NoPanic`, AND its body is a shape the kernel-import
//! elaborator can turn into a defining equation the Clean kernel re-checks. When
//! both hold, the function is IMPORTED into the kernel and passes the E6
//! admission gate; when either fails, the call fails CLOSED.
//!
//! This fixture pins that the admission gate is WIRED for the elaborator body
//! shapes:
//!  - `answer` (constant), `fst` (projection) and `min2` (select/min-max) are
//!    certified and RECOGNIZED, so each passes the admission gate. Their
//!    citations then fail on a SEPARATE, later constraint — the exact-statement
//!    binding (`triv : True` does not prove the clause, and the clause carries
//!    an extra `result` binder) — NOT on the E6 gate.
//!  - `winc` (wrapping arithmetic) passes through a narrower external-call
//!    lane. rustc authenticates the exact inherent `core` primitive DefId and
//!    safe `(uN, uN) -> uN` signature, then stamps a closed marker distinct
//!    from the intrinsic marker. Facet inference and body recognition recheck
//!    that marker and exact width/type agreement. This admits S3/S4 for
//!    `u8`/`u16`/`u32`/`u64`, while unmarked paths, lookalikes, malformed
//!    markers, signed/`usize`/`u128` carriers, and mixed-width chains fail
//!    closed. The stage-2 corpus pins S3 and S4 separately in `f10`/`f21`.
//!
//! That "bindings are not exact" diagnostic is the marker that the
//!    function WAS admitted (contrast `not_pure` below).
//!  - `not_pure` carries a debug overflow `Assert`, so NoPanic is not
//!    established: it fails AT the gate ("not certified: NoPanic"), never
//!    reaching the exact-statement check.
//!
//! IMPORTANT (scope): passing the admission gate is NECESSARY, not sufficient,
//! for verifying a postcondition. The cited functions are IMPORTED into the
//! kernel (definitional use is unblocked), but the citations here still fail
//! closed because `triv : True` does not exactly prove their clauses. The
//! bounded E9 lane can now close a matching `SpecEnsuresUnparseable` sentinel;
//! this fixture deliberately supplies mismatched theorems so it isolates and
//! proves the earlier KERNEL-IMPORT step rather than end-to-end discharge.

clean {
    theorem triv : True := True.intro
}

/// Constant body: `answer() = 42`. All four facets; admitted.
fn answer() -> u64 { 42 }

/// Projection body: `fst(x, y) = x`. All four facets; admitted.
fn fst(x: u64, y: u64) -> u64 { x }

/// Select body (min): `min2(a, b) = if a < b { a } else { b }`. Admitted.
fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

/// Wrapping-arithmetic body: `winc(x) = x.wrapping_add(1)`. The exact core
/// primitive identity supplies the external pure/total/no-panic authority.
fn winc(x: u64) -> u64 { x.wrapping_add(1) }

/// Debug-checked `+` ⇒ overflow `Assert` ⇒ structural NoPanic deficit. NOT
/// admissible; fails AT the E6 gate. (Its own overflow obligation is also
/// unproved, so it independently fails L0 — annotated below.)
fn not_pure(x: u64) -> u64 { x + 1 }
//~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::not_pure`
//~| ERROR Trust strict verification failed for `e6_kernel_import_admits::not_pure`

fn c_const(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_const`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_const`
    ensures answer() <= x by triv
    //~^ ERROR citation `triv` failed the strict Clean statement/certification audit
{ x }

fn c_proj(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_proj`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_proj`
    ensures fst(x, y) <= x by triv
    //~^ ERROR citation `triv` failed the strict Clean statement/certification audit
{ x }

fn c_select(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_select`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_select`
    ensures min2(x, y) <= x by triv
    //~^ ERROR citation `triv` failed the strict Clean statement/certification audit
{ if x < y { x } else { y } }

fn c_arith(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_arith`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_arith`
    ensures winc(x) >= x by triv
    //~^ ERROR citation `triv` failed the strict Clean statement/certification audit
{ x }

fn c_not_pure(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_not_pure`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_not_pure`
    ensures not_pure(x) <= y by triv
    //~^ ERROR at least one E6 structural facet of `not_pure` is not established: NoPanic
{ y }

fn main() {}

// EXPECTATION NOTE (2026-08-13, resolves the e6/e9 open question of
// reports/red-suite-triage-2026-08-13.md): on `not_pure`, the pinned native
// verifier status moved `Failed; failed=1` -> `Inconclusive; unknown=1`, and the
// per-obligation refutation authority moved from the native lane
// (`FAILED (trust-full-verifier); counterexample: verified_counterexample = true`)
// to the in-process bridge
// (`FAILED (ay-in-process); counterexample: _0 = 0, x = 18446744073709551615`).
// That is an INTENDED fail-closed authority change, not a native-lane defect:
// commit 91ce53b4e5 ("fix(semantics): fail closed on unattested refinement
// edges") withdrew public refutation authority from the native typed-CHC lane
// until the compiler emits a positive producer fidelity attestation
// (`trust-trust-mc.typed-chc-obligation.encoding_fidelity=exact`, which it
// "intentionally does not emit yet" — trust-bmc verifier_api,
// `TrustMcChcRefutationAdmissibility::Unattested`). The native trust-mc runner
// STILL refutes this obligation (see the retained "runner refuted obligation
// ...; refusing to emit proof evidence" evidence line); its row is merely
// demoted to Unknown — the demotion diagnostic ("refutation demoted to unknown:
// the submitted ChcVc has no positive producer fidelity attestation ...") is
// the row's 4th evidence diagnostic and is cut by the reporter's
// 3-diagnostics-per-row limit. The refutation the build fails on is now carried
// by ay-in-process WITH a concrete counterexample — strictly stronger evidence
// than the old solver-level `verified_counterexample = true`, which the code
// itself documents as refuting only the ENCODED VC. Every pinned error below
// still fires; the L0 gate still fails closed on the refuted row.
//
// EXPECTATION NOTE (2026-08-14, digest re-pin after the 97-commit upstream
// merge): the `bundle_digest`/`request_digest` values are content addresses —
// sha256 over the serde bytes of the `NativeVerificationBundle` and each
// native request (trust-router `native_trust_ir/index.rs`). The merge unioned
// upstream's ir-bridge lowering work (9e83268acc..221e88f7d3, with the
// trust-ir/trust-mc pin moves) with our lowering commits (1bf0cf45c5,
// 8ca24d4d1b, d9997cbd0b, 06ad94aaad), so the serialized request bytes match
// neither parent's blessing and all 13 digests moved. Every other stderr byte
// is unchanged from the 175e5e4ed5 pin — same admissions, same TermRejected
// term trees, same statuses — a digest-only re-pin, not a behavior change.
