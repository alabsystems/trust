//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **G2 — the out-of-line unit spelled as Lean spells it: `.lean`.**
//!
//! `clean mod name;` used to resolve `name.clean` only, so a file authored as
//! `name.lean` — the spelling every Lean tool, editor mode and `targo trust
//! check` already accept — was "file not found". Both spellings now name the
//! same unit (`rustc_expand::module::load_clean_unit`); this fixture is the
//! `.lean` half, `clean_unit_call_parity.rs` remains the `.clean` half, and
//! `clean_unit_both_spellings.rs` pins that having BOTH on disk is refused.

clean mod clean_unit_lean_extension_helper;

fn main() {
    let g = crate::pick_lean(6u64, 7u64);
    println!("{g}");
    assert_eq!(g, 6, "the emitted body must be the projection the Clean `def` denotes");
}
