//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! Trust (ny-tensor niche defect): an enum carrying a NICHE descriptor may only REGISTER when
//! its DECLARED untagged payload can be PROVEN to cover the niche lane.
//!
//! THE DEFECT. `register_enum` fills `EnumLayoutDescriptor` from rustc's TRUE layout
//! (`producer_enum_layout_descriptor`) but declares the variant FIELD TYPES from `map_ty`, and
//! those two disagree whenever a payload took an OPAQUE LANE. `map_ty` collapses an enum
//! `register_enum` declined to a fail-closed placeholder: `Ty::Bool` — the DISCRIMINANT — for
//! `Option` under the wave-SEAM lane, `Ty::Unit` for every other enum. Here
//! `Option<(Vec<u8>, usize)>` declines (a `Ty::Tuple` variant field is not in
//! `enum_variant_field_admissible`), so the enclosing `Result`'s Ok field is declared
//! `Ty::Bool` — ONE byte — while rustc niche-encodes the `Result` with untagged variant 0 and
//! an 8-byte lane at offset 0 of that 32-byte payload. The v31 enum-layout validator then
//! correctly refuses the module. The pre-existing wave-LC strip beside the fill does NOT catch
//! it: it asks whether each declared payload's layout is RESOLVABLE, and a one-byte scalar
//! trivially has one.
//!
//! THE SPELLING IS `Ty::Bool`, NOT `Ty::Unit`. `option_flag_lanes_enabled` is ON BY DEFAULT,
//! and the distinction decides whether the defect exists at all: under
//! `TRUST_OPTION_FLAG_LANES=0` this whole file compiles CLEAN on the PRE-FIX seal, and its
//! `-Ztrust-dump=ir` module contains no `Result` row for either offending shape — only the
//! three rows the covering neighbours below contribute (the one-function reproducer's module
//! holds ZERO enum rows). Measured 2026-09-08 on seal trust-a1fe10ee. The reason is that the
//! flag-off placeholder `Ty::Unit` is already refused one gate earlier — the `Ty::Unit` arm of
//! `enum_variant_field_admissible` is `ty::Param`-only — so the `Result` never registers. The
//! default lane's `Ty::Bool` is a SCALAR and `seed_constant` admits every scalar; that is the
//! one route by which a fail-closed placeholder becomes a declared variant field.
//!
//! MEASURED. ny 0.5.0 `ny-tensor` TEST unit, seal trust-b43aa66d (2026-09-08), also failing the
//! ny release gate; reproduced standalone on seal trust-a1fe10ee (2026-09-08) with
//! `trustc --crate-type lib --edition 2021 -Ztrust-verify=off -Ztrust-ir-lower=on`:
//!
//!   error: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [ConstTypeMismatch]: ConstTypeMismatch { location: "enum.0 (Result) layout",
//!   expected: "the niche lane covered by a non-ZST field of the untagged variant",
//!   actual: "untagged_variant 0" }
//!
//! In ny the shape is `BoundedTensor::intersection_per_element_with_poll`, which returns
//! `Result<Option<(BoundedTensor, usize)>, NyError>` (`enum.41`); the crate's LIB unit is green
//! and only the TEST unit lowers the body that registers the type. The class became reachable
//! with the valtree DECODE fix, which registers types that used to stay opaque.
//!
//! THE FIX. The declared FIELD TYPES are the wrong side — the lane, the untagged-variant index
//! and every offset are faithful to rustc — so `register_enum` re-runs the validator's own
//! coverage rule over the DECLARED field sizes (`declared_niche_lane_covered` over
//! `declared_ty_size_bytes`, an under-approximating mirror of `Module::ty_layout_shape`) and
//! DECLINES the whole enum when coverage is not proven; its users take the wave-EL opaque lane,
//! the same floor every other `register_enum` admission gate uses.
//!
//! WHY DECLINE RATHER THAN STRIP THE DESCRIPTOR. Because "an absent descriptor only costs
//! precision" is false: `to_mir.rs`'s `enum_flip_direct_only` reads `layout: None` as `true`
//! (a fail-open its own comment records and declines to change without a census), so stripping
//! would ADMIT into the flip lane exactly the niche-encoded enums the rule has just declared
//! unprovable. Declining adds ZERO members to the descriptor-less corpus, so no flip admission
//! changes and no census is owed. The price is coverage, not verdicts: `-Ztrust-ir-lower` is
//! non-strict under verification, and on the differential channel the pair lands on the
//! documented cross-kind `Err` arm (coverage-only) that every other declined enum already uses.
//! The one lane that pays more is the opt-in `-Ztrust-cg-frontend=trust-ir`, which refuses a
//! crate on any declined item — the same price every other `register_enum` decline charges it.
//!
//! WHAT THIS PIN GUARDS, AND WHAT IT DOES NOT. It is RED before the fix and green after it, on
//! the defect's own channel: under `-Ztrust-ir-lower` (any mode, `on` included) the crate
//! finalizer runs final module validation and every validation error is fatal —
//! `crate_module.rs`'s `final_module_validation_errors` feeds `summary.errors`, and
//! rustc_mir_build's `trust_ir_crate_finalize` turns a non-empty list into `dcx().fatal`. The
//! guarded property is exactly that: the module the producer emits is VALID. `check-pass`
//! observes NOTHING ELSE — not which per-body tags these functions record, not that the
//! neighbours below kept their descriptors, and not that the rule declines narrowly. A change
//! that declined every enum in the corpus would still pass this file; over-declining has to be
//! caught by a coverage/clean-rate census, not here.

#![allow(dead_code)]

// ---- the reduced ny-tensor shape: an Option with a TUPLE payload (declines registration,
// ---- collapsing to the one-byte `Ty::Bool` discriminant lane) in the Ok slot of a
// ---- niche-encoded Result.

pub fn opaque_ok_payload(x: bool) -> Result<Option<(Vec<u8>, usize)>, bool> {
    if x { Err(true) } else { Ok(None) }
}

// ---- the same shape with a named error enum and a named payload struct, the spelling ny
// ---- actually has (`Result<Option<(BoundedTensor, usize)>, NyError>`).

pub struct Tensor {
    lower: Vec<f32>,
    upper: Vec<f32>,
}

pub enum TensorError {
    Shape(String),
    Deadline(String),
}

pub fn intersection_with_poll(x: bool) -> Result<Option<(Tensor, usize)>, TensorError> {
    if x { Err(TensorError::Shape(String::new())) } else { Ok(None) }
}

// ---- neighbours whose untagged payload IS a declared, non-ZST, covering field. They compile
// ---- clean both before and after the fix, so this file also pins that the new rule does not
// ---- turn a working shape into a hard error; whether they keep their DESCRIPTORS is not
// ---- observable here (see WHAT THIS PIN GUARDS above).

pub fn struct_ok_payload(x: bool) -> Result<Option<Vec<u8>>, bool> {
    if x { Err(true) } else { Ok(None) }
}

pub fn ptr_payload(x: bool) -> Option<Box<u8>> {
    if x { None } else { Some(Box::new(0)) }
}

// ---- the RESIDUE the fix deliberately does not repair: a ONE-byte lane is "proven" by the
// ---- one-byte `Ty::Bool` stand-in for a wider real payload, so this shape keeps its
// ---- descriptor. It is VALID (the validator's rule is satisfied) but the spelling is still a
// ---- fiction; making the placeholder itself inadmissible is a broader, unmeasured change.

pub fn one_byte_lane_residue(x: bool) -> Result<Option<(bool, bool)>, bool> {
    if x { Err(true) } else { Ok(None) }
}

fn main() {}
