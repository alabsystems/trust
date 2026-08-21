//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **I8 — THE COLLISION CONTROL, CLEAN HALF: inline island def vs `.clean`
//! unit def of the same name, same module.**
//!
//! DELIBERATELY NOT `E0428`, and this file is the documentation of why. The
//! crate's Clean environment is ONE header-first batch (`check_all` over
//! every island text, I1), so two Clean `def`s of one name are refused at the
//! CLEAN level — a duplicate declaration — before any mint decision can
//! grant either one. `trust_clean_mint::decide` grants nothing on a rejected
//! batch (a partially registered environment must never mint positive
//! evidence), so no `DefId` exists on either side and rustc's own duplicate
//! detection never gets a pair to compare. Two INLINE islands with the same
//! def name fail in exactly this way today; the unit inheriting that
//! behaviour bit-for-bit IS the identical-graph-entries acceptance control
//! holding on the negative side.
//!
//! The reachable `E0428` — the one that proves minting and placement — is a
//! Clean def against a same-module RUST `fn`: `clean_unit_rust_collision.rs`.
//!
//! Expected: compile-fail, with the Clean-side duplicate rejection from the
//! verify pass naming `dup_pick`, spanned into one of the two declarations.
//! NOTE FOR BLESSING: tighten `error-pattern` to the exact Clean rejection
//! wording on first run; `dup_pick` is the stable substring.

clean {
    def dup_pick (a b : UInt64) : UInt64 := a
    //~^ ERROR `dup_pick` is declared twice in this batch
}

clean mod clean_unit_dup_name_helper;

fn main() {}
//~? ERROR `dup_pick` is declared twice in this batch
