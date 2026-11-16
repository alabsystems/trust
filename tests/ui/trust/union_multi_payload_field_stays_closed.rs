//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! THE RAIL FOR THE 2026-09-20 SINGLE-PAYLOAD UNION CARVE-OUT.
//!
//! `field_type` refuses a field projection on a union because trust-ir's
//! aggregate spelling has INDEPENDENT fields where a union's OVERLAP, so a
//! projection would invent struct semantics. That refusal now has one exception:
//! a union with exactly ONE field that has any bytes, where there is no second
//! field to collide with and the payload IS the union's bytes at offset 0.
//!
//! THIS UNION HAS TWO. `a` and `b` both occupy byte 0, so the hazard the refusal
//! exists for is live here — `union_field_address_fails_closed_without_a_union_
//! type` records the measured form of it: the layout-less fallback once handed
//! field 1 the address `base + 1`, which is wrong for every union ever written.
//!
//! If this file ever passes, the carve-out has stopped counting payload fields
//! and is admitting overlapping ones. The unit test named above pins the same
//! property on a synthetic ADT; this pins it on real Rust, through the whole
//! extractor, where a change to `ty_convert`'s `adt_kind` stamping would also
//! show up.
pub union Overlapping {
    pub a: u32,
    pub b: f32,
}

pub fn read_it(u: &Overlapping) -> u32 {
    unsafe { u.a }
}
