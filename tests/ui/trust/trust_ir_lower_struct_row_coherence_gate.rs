//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! Trust (the incoherent-declared-layout residue; reproducer from 8bd29c63c3, 2026-09-09):
//! `register_struct` must not declare rustc's `size`/`align`/offsets beside a field that NAMES a
//! registered struct row carrying no declared layout. trust-ir's `shape.rs` sizes a struct by
//! sizing every field, and such a field is `MissingStructSize`, so the parent is unresolvable
//! whatever bytes it declares — yet a parent that keeps rustc's bytes looks SIZED to
//! `enum_variant_field_admissible`, `register_enum` gives the holding enum a descriptor, and the
//! enum layout validator refuses the module.
//!
//! THE CASCADE. `Option<(usize, Vec<u8>)>` has a tuple payload, so `register_enum` declines it
//! and the option-flag lane spells the array element `Ty::Bool`. The `repr(transparent)` row
//! `UnsafeCell<[Option<(usize, Vec<u8>)>; 2]>` then declares a 2-byte carrier beside rustc's
//! 64 / 8, and main's transparent-carrier rule (2026-09-22) correctly blanks it. But the rows
//! ABOVE it kept rustc's bytes: `RefCell<..>` (72 / 8) over the blanked `UnsafeCell`, `Cache`
//! (80 / 8) over `RefCell`, and the enum `Store` over `Cache` got a descriptor bounding a
//! payload no one can size. Measured RED on seal trust-7d5533b2 and on the 2026-09-24 batch-2
//! stage 1 (both built from main):
//!
//!   error: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [ConstTypeMismatch]: ConstTypeMismatch { location: "enum.0 (Store) layout", ... }
//!
//! THE FIX (`ty_names_unsized_struct_row`, read by `register_struct`'s field-model rule): a
//! field that names an unsized struct row, directly or as an array element, blanks the parent.
//! `struct_field_tys` registers every field before its parent is minted and `pending_structs`
//! rows are never edited after the push, so the blank propagates one level per registration:
//! `RefCell`, then `Cache`, and `Store` is DECLINED as an enum (`enum_variant_field_admissible`
//! refuses a payload with no size) — coverage, never a verdict.
//!
//! WHAT `check-pass` OBSERVES: that the emitted module is VALID, nothing more. Under
//! `-Ztrust-verify=off` a final validation error is a WARNING and the exit stays 0
//! (verify_off_invalid_module_is_a_warning.rs); this test still fails on it, because compiletest
//! requires an annotation for every warning and this file has none. Compiled by hand, read the
//! TEXT (`semantic finalization failed`), not the exit status. It cannot see over-blanking — a
//! row losing its layout only removes a claim, and every consumer DECLINES rather than errors.
//! The two neighbour bands therefore guard the other direction only by hand: under
//! `-Ztrust-dump=ir:<dir>` the `Faithful` row (a `[u8; 2]` carrier that IS rustc's) and the
//! `Direct` row (the declined `Option` spelled `Ty::Bool` with no transparent wrapper, which fits
//! inside rustc's 40 bytes) must both keep `size=`/`align=`.
//!
//! THE DESCRIPTOR-LESS ENUM ARM (2026-10-17, ported from ad03b3a0fe4, seal line row 39). The
//! field-model rule used to ADMIT every field whose image it could not derive, and a
//! descriptor-less enum is one whose image the authority DOES derive: trust-ir's canonical
//! tagged-union layout, a tag lane then the payload, larger than rustc's niche image. Rustc's
//! offsets beside it overlap, and the validator refuses the module with
//! `StructLayoutInconsistent { reason: "fields overlap" }` (autocfg, cc and ay-tla-bridge were
//! refused this way on 2026-09-22, through a niche the wave-LC strip had removed). The bands
//! below build both populations from one base enum:
//!
//! * `Uncoverable` (the shape of trust_ir_lower_uncoverable_niche_decline.rs): rustc
//!   niche-encodes it in 1 byte, with `V2` uninhabited and outside the niche interval, so
//!   `producer_enum_layout_descriptor` declines its descriptor. Canonically it is 2 bytes.
//! * `Option<Uncoverable>`, the OPTION-WRAPPED case: rustc gives it a niche in 1 byte, and the
//!   wave-LC strip removes that descriptor because its payload `Uncoverable` has none.
//!   Canonically it is at least 3 bytes.
//!
//! Each holder is 2 bytes to rustc with its two fields at offsets 0 and 1, in either order, so
//! any canonical field image of 2 bytes or more overlaps its neighbour. PREDICTED red before
//! the port and green after it; NEITHER direction was run when this band was written. After
//! the port, `ty_spells_unsettled_field` blanks both holder rows, and `NicheStore` /
//! `DeclinedStore` then decline as enums, exactly as `Store` does above. The hand check under
//! `-Ztrust-dump=ir:<dir>` is that `struct @NicheHolder` and `struct @DeclinedHolder` carry no
//! `size=`.

#![allow(dead_code)]

use std::cell::RefCell;

// ---- THE DEFECT: a `repr(transparent)` wrapper whose declared carrier is the option-flag
// ---- lane's `Ty::Bool`, inside a struct that is an enum payload. RED on the pre-fix seal.

pub struct Cache {
    slots: RefCell<[Option<(usize, Vec<u8>)>; 2]>,
    n: usize,
}

pub enum Store {
    Mem(Cache),
    Disk(Cache),
}

pub fn store_is_none(s: &Option<Store>) -> bool {
    matches!(s, None)
}

// ---- THE NEIGHBOURS: green before, and the census says green after. See the header.

pub struct Faithful {
    slots: RefCell<[u8; 2]>,
    n: usize,
}

pub enum FaithfulStore {
    Mem(Faithful),
    Disk(Faithful),
}

pub fn faithful_is_none(s: &Option<FaithfulStore>) -> bool {
    matches!(s, None)
}

pub struct Direct {
    o: Option<(usize, Vec<u8>)>,
    n: usize,
}

pub enum DirectStore {
    Mem(Direct),
    Disk(Direct),
}

pub fn direct_is_none(s: &Option<DirectStore>) -> bool {
    matches!(s, None)
}

// ---- THE DESCRIPTOR-LESS ENUM ARM: a struct row over an enum that has no layout descriptor.
// ---- PREDICTED red before the ad03b3a0fe4 port ("fields overlap"). See the header.

pub enum Void {}

pub enum Uncoverable {
    V1 { f: bool },
    V2 { f: Void },
    V3,
    V4,
}

// The Option-wrapped case: `Option<Uncoverable>`'s niche descriptor is stripped.
pub struct NicheHolder {
    a: Option<Uncoverable>,
    b: Option<Uncoverable>,
}

pub enum NicheStore {
    Mem(NicheHolder),
    Disk(NicheHolder),
}

pub fn niche_store_is_none(s: &Option<NicheStore>) -> bool {
    matches!(s, None)
}

// The declined case: `Uncoverable`'s own descriptor is declined.
pub struct DeclinedHolder {
    a: Uncoverable,
    b: Uncoverable,
}

pub enum DeclinedStore {
    Mem(DeclinedHolder),
    Disk(DeclinedHolder),
}

pub fn declined_store_is_none(s: &Option<DeclinedStore>) -> bool {
    matches!(s, None)
}

fn main() {}
