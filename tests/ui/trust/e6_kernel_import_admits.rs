//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-require-annotations: WARN
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
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
//!  - `winc` (wrapping arithmetic) does NOT pass the gate. This comment used to
//!    claim it did, reaching NoPanic "via the call-graph closure over
//!    `wrapping_add`"; the fixture's own expected diagnostic at `c_arith`
//!    contradicts that, saying "at least one E6 structural facet of `winc` is
//!    not established". The Arithmetic shape is built from a CALL, and the
//!    facet gate poisons on any `Terminator::Call`
//!    (`crates/trust-vcgen/src/facets.rs:261`), so the recognizer matches and
//!    admission still refuses — shapes S3 (Arithmetic) and S4 (Composed) are
//!    unreachable today. Independently measured as `admissible=false` by
//!    `tests/e6-fragment-probe/probes/f10_arith_wrapping.rs`.
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

/// Wrapping-arithmetic body: `winc(x) = x.wrapping_add(1)`. NoPanic holds only
/// via the call-graph closure over the trusted external `wrapping_add`, so this
/// is the case that requires minting from the COMPOSED facet table.
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
    //~^ ERROR citation `triv` cannot be validated because this clause is outside the exact statement fragment: at least one E6 structural facet of `winc` is not established
{ x }

fn c_not_pure(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e6_kernel_import_admits::c_not_pure`
    //~| ERROR Trust strict verification failed for `e6_kernel_import_admits::c_not_pure`
    ensures not_pure(x) <= y by triv
    //~^ ERROR at least one E6 structural facet of `not_pure` is not established: NoPanic
{ y }

fn main() {}
