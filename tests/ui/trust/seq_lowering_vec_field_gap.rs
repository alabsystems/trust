//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ check-pass
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// It compiles, and under the default policy that is a PASS -- but not a
// silent one, and the remaining rows are why the WARN directives are here:
// `2 proved, 0 failed, 0 unknown, 1 runtime-checked, 1 skipped out of 4`.
// The drop-glue rows this file was blocked on are the two that became
// proved; what is left is a runtime-checked row and a skipped one, which
// policy B reports rather than fails. Do NOT read this fixture as a claim
// that `vec![..]` is fully PROVED -- it is a claim that its DROP GLUE no
// longer fails the build, which is the gap this file was opened for.
// CLOSED 2026-09-21 (W3). This was `known-bug` + `failure-status: 1`: a
// struct with `Vec<f32>` FIELDS built from `vec![..]` did not verify. The
// cause was never the sequence lowering itself -- it was that
// `ty_convert` replaces `Vec<T, A>` with `Ty::Seq` AHEAD of the site that
// stamps `AdtAuth::TotalDrop`, and `Ty::Seq` had no slot for the stamp, so
// the bridge's drop classifier had nothing to read and fell to its
// fail-closed arm. That is why `Option<Vec<u32>>` verified while a bare
// `Vec<u32>` did not, though the wrapper's glue CALLS the wrapped one's.
// `Ty::Seq` now carries the stamp, computed by the same `tcx_drop_is_total`
// on the FULL concrete type -- element AND allocator.
//! THE `vec![..]` CONSTRUCTION GAP — what is LEFT of the sequence-lowering gap.
//!
//! THE SEQUENCE HALF IS CLOSED. Read that first, because this file used to say
//! the opposite and a reader who believes the old text will go and rebuild a
//! lane that already exists. Typed-TrustIr lowering had NO `Ty::Seq` arm, so any
//! body whose signature so much as mentioned a `Vec` was refused with
//!
//!     error: Trust full verification failed for `...`: native typed-TrustIr
//!     lowering did not complete, so the panic-freedom of an unmodeled construct
//!     could not be established
//!     note: ... unsupported type: Seq { elem: Float { width: 32 } }
//!
//! `trust-ir-bridge`'s `map_type_ctx` now spells the owned sequence with the
//! format's own first-class `Ty::Sequence(elem TyId)` — element interned, no
//! layout claimed, every structural walk over it still fail-closed. Measured on
//! a stage1 driver built from this tree (`rustc 1.99.0-dev (47d326f2d)`), ALL of
//! these now compile `exit 0` under strict verification, and every one of them
//! was `exit 1` with the `Seq` blocker before:
//!
//!     pub fn move_struct(s: SequenceFields) -> SequenceFields { s }
//!     pub fn read_scale(s: &SequenceFields) -> f32 { s.scale }
//!     pub fn move_vec(v: Vec<f32>) -> Vec<f32> { v }
//!     pub fn make_empty() -> Vec<f32> { Vec::new() }
//!
//! They are pinned as a `check-pass` companion, `seq_carrier_vec_shapes.rs`, so
//! the win cannot silently regress into this file's `known-bug` tolerance.
//!
//! WHAT THIS FILE STILL PINS, and it is a DIFFERENT defect with a different
//! name: the `vec![$e]` macro path. Measured on the same driver, `build()` below
//! reports `2 proved, 0 failed, ... 1 skipped out of 3` and then fails with
//!
//!     note: ... unsupported operation: field projection on union
//!           core::mem::maybe_uninit::MaybeUninit requires a trust-ir union
//!           representation
//!
//! — the `Box<[T]> -> Vec<T>` construction walks a `MaybeUninit` UNION field,
//! and `field_type` refuses a union projection centrally (a union's fields
//! overlap; the trust-ir aggregate spelling's do not, so any projection would
//! invent struct semantics). That refusal is correct and deliberate; closing it
//! is a trust-ir union-representation task, not a sequence task.
//!
//! WHEN THIS STARTS PASSING, that is the win — delete the `known-bug` header,
//! turn it into a `check-pass`, and re-measure nn and ny, which are the two
//! repos that were waiting on the sequence half and are now waiting on this one.
//! Do NOT re-title it "the sequence gap" on the way past: that gap is closed and
//! saying otherwise sends the next reader to the wrong crate.

pub struct SequenceFields {
    pub scale: f32,
    pub lower: Vec<f32>,
    pub upper: Vec<f32>,
}

pub fn build() -> SequenceFields {
    SequenceFields { scale: 0.01, lower: vec![1.0], upper: vec![2.0] }
}
