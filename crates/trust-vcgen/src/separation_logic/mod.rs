// trust_vcgen/separation_logic/mod.rs: Separation logic primitives for unsafe Rust verification
//
// Implements separation logic formulas (PointsTo, SepStar, SepWand, Emp, Pure)
// and translates them to first-order logic with explicit heap encoding for
// SMT solving. Generates VCs for common unsafe operations: raw pointer deref,
// raw pointer write, and transmute.
//
// The heap is modeled as an SMT array (Int -> Int) with explicit disjointness
// constraints for the separating conjunction (*). This follows the standard
// symbolic heap encoding from separation logic literature (Reynolds 2002,
// O'Hearn/Pym 1999).
//
// Extended in #191 with:
// - Provenance tracking for raw pointers (SymbolicPointer, ProvenanceId)
// - Frame rule application for modular unsafe code verification
// - Symbolic heap representation (SymbolicHeap) for tracking heap state
// - Integration with UnsafeOpKind from unsafe_vc.rs
//
// Part of #191: Unsafe code verification via separation logic / provenance engine
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod encoding;
mod formula;
mod frame;
mod heap;
mod provenance;
pub(crate) mod unsafe_ops;
mod vc_gen;

#[cfg(test)]
mod tests;

/// Put every separation-logic-owned SMT leaf in a namespace no Rust source
/// identifier can retain through MIR extraction.  Production separation VCs
/// are conjoined with ordinary source path definitions/guards, so a cosmetic
/// prefix such as `ptr_` is not sufficient: a legal scalar source binding can
/// carry that exact name and falsely discharge an unrelated pointer check.
/// The shared source-name classifier reserves every `__` spelling.
pub(crate) fn generated_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("sep", unqualified)
}

// Re-export all public API items to preserve the existing module interface.
pub use encoding::{encode_heap_disjointness, encode_unsafe_block, sep_to_formula};
pub use formula::SepFormula;
pub use frame::{apply_frame_rule, encode_framed_unsafe_block};
pub use heap::{HeapCell, SymbolicHeap};
pub use provenance::{PointerPermission, ProvenanceId, SymbolicPointer};
#[cfg(test)]
pub(crate) use unsafe_ops::vcs_from_unsafe_op;
pub use unsafe_ops::{address_of_sep_vc, ffi_call_sep_vc, unsafe_fn_call_sep_vc};
pub use vc_gen::{deref_vc, raw_write_vc, transmute_vc};
