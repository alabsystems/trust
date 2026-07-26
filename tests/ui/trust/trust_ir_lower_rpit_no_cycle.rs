//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Regression for the trust-ir producer's RPIT query cycle (E0391): with
//! `-Z trust-ir-lower`, lowering a body whose signature mentions its own
//! not-yet-revealed opaque (`-> Result<impl Iterator, _>`) used to demand
//! `layout_of(opaque)` from INSIDE `mir_built` — the demand chain
//! `map_ty → enum_repr_ty → enum_payload_ty → is_drop_free_zst → layout_of`
//! normalizes under the revealing `TypingEnv::fully_monomorphized()`, which
//! forces `type_of(opaque)` → borrowck of the defining body → `mir_built` of
//! the same body: a FATAL cycle, not the recoverable `LayoutError` the
//! fail-closed call sites assumed.
//!
//! The fix is the `cycle_safe_{layout_of,needs_drop,normalize,is_copy}`
//! wrappers in `trust-thir-lower` (refuse the demand on `has_opaque_types()`
//! up front, O(1) type-flags check), applied at every pre-borrowck demand
//! site. An RPIT-signature body now lowers fail-open (recorded coverage gap)
//! instead of aborting the compile. Mirrors the exact shape observed in
//! `regex-syntax`'s `unicode::ages`.
pub struct Range {
    pub lo: u32,
    pub hi: u32,
}

pub fn ages(x: &str) -> Result<impl Iterator<Item = Range>, ()> {
    let v = vec![Range { lo: 0, hi: x.len() as u32 }];
    Ok(v.into_iter())
}

// The differential/to_mir side of the same hazard: an RPIT type flowing
// through param/return classification (`needs_drop`/`is_copy` guards).
pub fn caller() -> usize {
    match ages("x") {
        Ok(it) => it.count(),
        Err(()) => 0,
    }
}

fn main() {}
