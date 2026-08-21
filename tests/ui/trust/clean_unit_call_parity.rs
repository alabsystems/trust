//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I8 — THE PARITY ACCEPTANCE TEST, CALL HALF (out-of-line unit).**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7, I8:
//! "a `.clean` unit and an inline island must produce identical graph
//! entries".)
//!
//! Mirrors `clean_origin_call_parity.rs`'s final (green) form, with the ONE
//! change I8 exists for: the `def` is authored in its own `.clean` file
//! (`clean_unit_parity_helper.clean`, loaded by `clean mod …;` at the
//! out-of-line-module expansion seam) instead of between braces.
//!
//! What must hold, in order:
//!  * the unit's decl is minted into the ENCLOSING module (here: the crate
//!    root), so the unqualified `crate::pick` path resolves — same placement
//!    rule as an inline island (design §4: decls are siblings under the
//!    enclosing Rust module; the unit name `clean_unit_parity_helper` names
//!    the FILE, never a module scope);
//!  * the emitted body traverses the same kernel-gated `clean_origin_mir`
//!    lane an inline island's def does, and RUNS;
//!  * the value is the projection the Clean `def` denotes.
//!
//! Its sibling `clean_unit_rust_collision.rs` is the sharp half (`E0428`
//! against a same-module Rust `fn`), and `clean_unit_island_equivalence.rs`
//! pins inline-vs-unit equivalence on one def under two revisions.

clean mod clean_unit_parity_helper;

fn main() {
    // MUST resolve exactly as if `def pick` had been written in an inline
    // island right here.
    let g = crate::pick(6u64, 7u64);
    println!("{g}");
    assert_eq!(g, 6, "the emitted body must be the projection the Clean `def` denotes");
}
