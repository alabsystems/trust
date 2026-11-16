//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
// UPDATED 2026-09-21 (W3): this fixture is named for the property that the
// DEFAULT `Global` allocator discharges the dealloc contract, and it did --
// but the body still failed on a separate gap: a bare `Vec`'s drop glue was
// refused because `Ty::Seq` never received the `AdtAuth::TotalDrop` stamp its
// ADT siblings did. With that closed the file compiles clean, which is what
// its name always claimed, so it is now `check-pass` rather than a fixture
// that documented its own unrelated blocker.
//! §5 STEP 5 (`GlobalAlloc::dealloc` caller contract), fixture (a) — the
//! DEFAULT-`Global` direction. Plan of record:
//! docs/design/2026-08-19-verified-sysroot-scoping.md §5 step 5.
//!
//! This crate registers NO `#[global_allocator]`, so every dealloc reachable
//! from its drops is `Global`'s std chain (`Global::deallocate` →
//! `__rust_dealloc` → the std default allocator, library/alloc/src/alloc.rs),
//! which has no panic path. The `contract:global-alloc-dealloc-panic-free`
//! premise charged to `consume` (it drops an allocation-owning `Vec<u8>`) must
//! therefore publish as DISCHARGED (vacuously, `Global`) — and must NOT abort.
//!
//! WHAT MAKES THIS FILE FALSIFYING: the paired fixtures
//! `global_alloc_dealloc_contract_panicking_user_dealloc_refused.rs` /
//! `..._panic_free_user_dealloc_still_refused.rs` pin that a registered user
//! allocator REFUSES with the distinctive "caller contract is refused" error.
//! If the disposition's allocator detection were wrong in either direction —
//! refusing the default-`Global` graph, or discharging a user-allocator graph —
//! exactly one file of the pair gains or loses an error and goes red. Here,
//! a wrong refusal would add a SECOND, unannotated error to `consume`.
//!
//! Measured baseline (stage1 trustc, 2026-08-30): this body still carries ONE
//! pre-existing strict failure — `Vec`'s drop glue DECLINES the structural
//! classifier (the element-erased map/set gate cuts `::vec::Vec` before any
//! PARTS entry is consulted), the same gap
//! `drop_glue_std_container_still_open.rs` pins. That error is annotated
//! below and is NOT this file's subject. When steps 2-3 of the plan close the
//! classifier gap, this file should flip to clean — via the discharged
//! contract, with the proof still conditional on the final link (the body is
//! never registered in the interprocedural panic-free registry).
pub fn consume(v: Vec<u8>) -> usize {
    v.len()
}
