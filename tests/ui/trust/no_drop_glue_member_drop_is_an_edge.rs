//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A `Drop` of a monomorphic type with no drop glue is a plain edge.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (n08, p24, q06):
//! `Iterator::max` is a generic std body that drops its `Self`; bundled for
//! `v.windows(2).map(|w| ..).max()`, that `Self` is `Map<Windows<'_, u8>, {closure}>`,
//! which has no drop glue at all (rustc's `needs_drop` is false and codegen emits
//! nothing). The bridge's `Ty::Adt` carries no drop bit, so the drop kept the row
//! "drop glue for `Map` has unproven panic-freedom (user Drop impls may panic)" and
//! refused the program. The extractor now lowers such a drop to a `Goto`
//! (`convert_terminator`); a type that needs drop, or still has a parameter in it,
//! keeps its `Drop` — `no_drop_glue_member_drop_is_an_edge_refused.rs`.
//!
//! What this pins is that the programs BUILD: each function's one row, the bundled
//! `max`'s own panic-freedom, keeps its runtime check on the default lane.

pub fn first_max(v: &[u8]) -> Option<u8> {
    v.windows(2).map(|w| w[0]).max()
}

pub fn pair_max(v: &[u32]) -> Option<u32> {
    v.windows(2).map(|w| w[0].max(w[1])).max()
}

pub fn triple_max(v: &[u32]) -> Option<u32> {
    v.windows(3).map(|w| w[0].max(w[1]).max(w[2])).max()
}
