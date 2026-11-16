//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ check-pass
//! THE OWNED-SEQUENCE CARRIER, pinned as a PASS.
//!
//! Every function here was `exit 1` before `trust-ir-bridge`'s `map_type_ctx`
//! learned to spell `trust_types::Ty::Seq { elem }` as trust-ir's own
//! `Ty::Sequence(elem TyId)`. The refusal was not subtle and not narrow — the
//! type wall fired on the SIGNATURE, so a body did not have to touch the `Vec`
//! at all to be refused:
//!
//!     error: Trust full verification failed for `...`: native typed-TrustIr
//!     lowering did not complete, so the panic-freedom of an unmodeled construct
//!     could not be established
//!     note: ... unsupported type: Seq { elem: Int { width: 64, signed: false } }
//!
//! This file is the anti-regression half of `seq_lowering_vec_field_gap.rs`,
//! which stays `known-bug` for the SEPARATE `vec![..]`/`MaybeUninit`-union
//! blocker. Without this pin, removing the carrier would simply widen that
//! file's tolerance and nothing would go red.
//!
//! It pins only what is TRUE, not what would be convenient: each body here is
//! panic-free by inspection (a move, a scalar field read beside a sequence
//! field, or the allocation-free `Vec::new`). A `Sequence` is transport — it
//! carries the element type across the boundary and claims no layout — so a
//! body with a REAL unproved obligation must still be refused; that direction is
//! pinned by `tests/run-make/trust-ir-emit-clean-origin`'s
//! `seq_carrier_control.rs` half, which must keep failing.

pub struct SequenceFields {
    pub scale: f32,
    pub lower: Vec<f32>,
    pub upper: Vec<f32>,
}

/// A whole-value move of a struct whose fields are owned sequences.
pub fn move_struct(s: SequenceFields) -> SequenceFields {
    s
}

/// A scalar field read through a shared reference, beside two sequence fields —
/// the "a struct is poisoned merely by CONTAINING a sequence" shape.
pub fn read_scale(s: &SequenceFields) -> f32 {
    s.scale
}

/// The bare signature case: the sequence is never touched, only moved.
pub fn move_vec(v: Vec<u64>) -> Vec<u64> {
    v
}

/// Construction that allocates nothing.
pub fn make_empty() -> Vec<f32> {
    Vec::new()
}
