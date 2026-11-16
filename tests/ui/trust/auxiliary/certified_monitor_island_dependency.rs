//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]

//! Aux for `certified_monitor_dependency_clean_island.rs` (CB3, 2026-09-28).
//!
//! The island below is `DefKind::GlobalAsm` in this crate's metadata, and the
//! encoder marks it in the `trust_clean_island_item` table. The
//! `island_global_asm` revision adds a REAL `global_asm!` beside it, so the
//! consumer can show that the admission is per def, not per crate.

clean {
    theorem dependency_island_holds : 0 = 0 := rfl
}

#[cfg(island_global_asm)]
core::arch::global_asm!("");

pub fn ordinary_rust_symbol() {}
