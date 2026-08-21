//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I8 — THE COLLISION CONTROL, RUST HALF.**
//! Mirrors `clean_origin_parity_collision.rs` with the def authored
//! out-of-line. Parity is not "the name resolves"; it is "the two spellings
//! denote the SAME entity", and the observable consequence of sameness inside
//! one module is a duplicate-definition error. This can only fire if the
//! `.clean` unit's decl was MINTED and planted into the ENCLOSING module
//! exactly as an inline island's is — so `E0428` here is the proof that the
//! unit went through `trust_clean_mint::decide` -> `def_collector` ->
//! `define_local` unchanged.
//!
//! (The inline-vs-unit same-name collision is a DIFFERENT error by design —
//! see `clean_unit_inline_duplicate.rs`: two Clean defs of one name are
//! refused by the crate's single header-first Clean environment before any
//! mint exists, for units exactly as for two inline islands.)

clean mod clean_unit_collision_helper;

// Collides with the Clean-origin `f` from `clean_unit_collision_helper.clean`,
// which I8 loads at the out-of-line-module seam and I5 mints into THIS module.
fn f(a: u64) -> u64 { a }

fn main() {
    let _ = f(1);
}
//~? ERROR the name `f` is defined multiple times
