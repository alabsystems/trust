//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//! A `Drop`-bearing ADT whose DESTRUCTOR proves panic-free is credited.
//!
//! ## THE `impl Drop` IS THE ASSERTION — DELETING IT GUTS THIS TEST
//!
//! Without it `Q` has no destructor, `has_dtor` is false, and the ORIGINAL
//! `collect_structural_drop_adts` already recorded it — the file would pass for a
//! reason that predates this rule and could never regress.
//!
//! Before this rule, `has_drop` cut EVERY `Drop`-bearing ADT unconditionally:
//!     |ty| matches!(ty.kind(), ty::Adt(adt_def, _) if adt_def.has_dtor(tcx))
//! so `Q` was refused and its user landed an unproved
//! `[trust-drop-glue-assumption]` row. The cut is now conditional on the
//! destructor clearing the same evidence bar every other premise uses.
//!
//! Paired with `drop_glue_panicking_drop_stays_closed.rs`, which plants a
//! PANICKING `Drop` and must keep failing. Neither file is meaningful alone: one
//! shows the rule fires, the other shows it discriminates.
pub struct Q {
    a: u8,
}
impl Drop for Q {
    fn drop(&mut self) {}
}
pub fn take(q: Q) -> u8 {
    q.a
}
