//@ battery-lane: D-legacy
//@ battery-expect: tippy-emits-lean
//@ battery-flags: --crate-type=lib
//@ battery-tool: tippy
#![feature(register_tool)]
#![register_tool(kani)]
//! LANE D (legacy frontend → Lean) — CONTRACT ATTRIBUTES.
//!
//! The owner's stated target: "legacy frontends (kani) where tippy corrects to
//! Lean". The battery runs TIPPY over this file and asks one question — DOES
//! THE DIAGNOSTIC CONTAIN THE LEAN THE USER SHOULD WRITE INSTEAD?
//!
//! ## Measured (2026-07-25, toolchain c6be27eb88): NO.
//!
//! The lint fires on every attribute and suggests RUST CLAUSES:
//!
//!     warning: legacy contracts attribute; Trust supports first-class
//!              signature clauses
//!     help: move the predicate into the signature:
//!           `fn f(..) requires x < 1000 { .. }`
//!
//! No Lean appears anywhere. That matches the source: `legacy_spec_sugar.rs`
//! is tippy's only Trust lint and emits the literal template `fn f(..)
//! {clause} {predicate} {{ .. }}`; a repo-wide search for Lean vocabulary in
//! `clippy_lints/` returns nothing. So the expectation `tippy-emits-lean` is a
//! SPECIFICATION OF THE TARGET, and its failure is the measurement.
//!
//! Note this lane's directive amends §3.2 of the ratified design (which
//! DELETES these surfaces rather than migrating them) and is PENDING
//! RATIFICATION — so a red row here is a stated goal, not an agreed
//! requirement, and must not be read as a defect.
//!
//! ## Why `register_tool` and no `mod kani`
//!
//! `#[kani::requires(..)]` is a TOOL attribute. Declaring a real `mod kani`
//! (as an earlier version did, to resolve `kani::any()`) makes the path
//! resolve to the MODULE and fail with E0433 — registering the tool does not
//! help, because the module shadows it. The nondet vocabulary therefore lives
//! in `d2_kani_nondet.rs`, which needs the module and has no attributes. Split
//! this way, each file's diagnostic is exactly the lint under test.

#[kani::requires(x < 1000)]
#[kani::ensures(|r| *r >= x)]
pub fn bump(x: u32) -> u32 {
    x + 1
}

#[kani::requires(n > 0)]
#[kani::ensures(|r| *r <= n)]
pub fn halve(n: u32) -> u32 {
    n / 2
}

#[kani::proof]
pub fn check_bump() {
    let _ = bump(1);
}
