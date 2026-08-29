//@ needs-trust-verify
//@ aux-build:user_written_automatically_derived_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 2 — THE DISCLOSED COST. A genuine `#[derive(..)]`-generated cross-crate
//! impl is NO LONGER bundled, and this file is the receipt.**
//!
//! # What this file used to assert, and why that flipped
//!
//! Until 2026-08-27 this was `check-pass`: it asserted that a real derive keeps
//! being bundled and proved (`proved: 1, failed: 0`, no `absent callee`
//! diagnostic), and it existed so that a fix for
//! `automatically_derived_user_written_not_admitted.rs` could not silently
//! delete that lane. It did not survive. The CONTAINMENT fix for arm 1 deleted
//! the `#[automatically_derived]` conjunct from the cross-crate callee admission
//! in `trust_verify.rs` outright, leaving `resolved_def_id.as_local().is_none()`
//! alone, so **no** foreign body is admitted on that lane any more — derived or
//! not, genuine expansion or hand-typed attribute.
//!
//! # The capability that was given up, stated plainly
//!
//! Calls into a cross-crate `#[derive]`-generated `clone` / `eq` / `default` /
//! `fmt` no longer discharge their panic-freedom by proof. Each now takes the
//! fail-closed absent-callee arm and reports
//! `[trust-absent-callee-assumption] call to absent callee ... may panic`.
//! Concretely, the three calls below — `<Real as Clone>::clone`,
//! `<Real as PartialEq>::eq`, `<Real as Default>::default` — go from one proved
//! row to refusals. Any caller in any crate that clones or compares a
//! dependency's derived type pays this.
//!
//! # Why that is the right trade anyway
//!
//! Because the capability was never real. This file's own previous text already
//! conceded the decisive point: *"it does not claim the derived bodies were
//! verified — they were compiled `-Ztrust-verify=off` like every other
//! dependency unit, and they are admitted on the same 'bundled member mints no
//! obligation' path as `Marked::get`."* A bundled member's `Assert` mints no
//! obligation, so `requested_obligations == 0`, `native_run_is_vacuously_clean`
//! holds, and the caller is reported "trivially panic-free". The row this file
//! used to count as `proved` was therefore an *unchecked assumption wearing a
//! proof's label* — the identical mechanism that let arm 1 issue `Gate: PASS`
//! over a binary that panics with `RUNTIME_EXIT=101`.
//!
//! So the loss is a loss of FALSE completeness. Nothing that was genuinely
//! proved stopped being proved; a class of calls that were silently trusted are
//! now audibly refused. That is strictly more information than before, and it is
//! the direction fail-closed requires.
//!
//! `#[derive]` is also not a panic-freedom argument in the first place. A
//! `#[derive(Clone)]` on a type whose field is a user type with a hand-written
//! panicking `Clone` calls that impl; and a proc-macro derive may expand to
//! arbitrary code, so the "compiler-generated" reading of the attribute buys
//! nothing even when the attribute is honest.
//!
//! # What would restore it — and this file is how you would know
//!
//! The previous text named the fix correctly and it is still correct: *"a fix
//! that makes the bundled member's own obligations REAL keeps this file green
//! and turns arm 1 red-to-green at the same time; a fix that merely narrows
//! which attribute is believed does not."* Containment is neither of those — it
//! is the third option, deleting the lane, taken because arm 1's hole is LIVE
//! and the root fix is not a one-session change.
//!
//! **This file is therefore a standing marker for unfinished work, not a
//! settled expectation.** When bundled members' obligations become real and
//! locally discharged (`reset_native_trust_ir_proof_inventory_to_public_bundle`
//! currently CLEARS the private inventory and rebuilds it ROOT-scoped, which is
//! why a member mints nothing), the correct move is to flip this file back to
//! `check-pass` — and at that point it must pass because the derived bodies were
//! VERIFIED, never because an attribute was believed again.

extern crate user_ad_dep;

use user_ad_dep::Real;

/// Reaches `<Real as Clone>::clone` — a genuinely derive-generated body.
pub fn derived_clone(r: Real) -> Real {
    r.clone()
}

/// Reaches `<Real as PartialEq>::eq` — likewise.
pub fn derived_eq(a: Real, b: Real) -> bool {
    a == b
}

/// Reaches `<Real as Default>::default`.
pub fn derived_default() -> Real {
    Real::default()
}
