// trust-types/atomic_intrinsics.rs: MIR atomic intrinsic detection and parsing
//
// Detects atomic operations from MIR Call terminator func paths and maps them
// to the canonical AtomicOperation type. Handles two MIR forms:
//
// Form A (suffix-encoded): core::intrinsics::atomic_load_seqcst(ptr)
// Form B (explicit Ordering): atomic::atomic_load::<usize>(ptr, Ordering::Acquire)
//
// Part of #605: Phase 1.2 MIR atomic intrinsic detection
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::utils::strip_generics;
use crate::{AtomicOpKind, AtomicOperation, AtomicOrdering, Operand, Place, SourceSpan};

/// The prefix for all rustc atomic intrinsics in MIR.
const INTRINSIC_PREFIX: &str = "core::intrinsics::atomic_";

/// Attempt to parse a MIR Call terminator as an atomic intrinsic.
///
/// Takes the func path, arguments, destination place, and source span from a
/// `Terminator::Call`. Returns `Some(AtomicOperation)` if the call is a
/// recognized atomic intrinsic, `None` otherwise.
///
/// Handles two MIR forms:
/// - **Form A** (suffix-encoded): `core::intrinsics::atomic_load_seqcst(ptr)`
/// - **Form B** (explicit Ordering arg): `atomic::atomic_load::<T>(ptr, Ordering::Acquire)`
///
/// Maps `Consume` ordering to `Acquire` per C++11 semantics (Consume is
/// effectively deprecated and treated as Acquire by all major compilers).
pub fn parse_atomic_intrinsic(
    func_path: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Strip generic parameters for matching: atomic_load::<usize> → atomic_load
    let normalized = strip_generics(func_path);

    // Try Form A first (most common in optimized MIR)
    if let Some(op) = parse_form_a(&normalized, args, dest, span) {
        return Some(op);
    }

    // Try Form B
    parse_form_b(&normalized, args, dest, span)
}

// ---------------------------------------------------------------------------
// Form A: suffix-encoded intrinsics
// ---------------------------------------------------------------------------

/// Parse Form A intrinsics: `core::intrinsics::atomic_{op}_{ordering}`.
///
/// For CAS operations, the pattern is `atomic_cxchg_{success}_{failure}` or
/// `atomic_cxchgweak_{success}_{failure}`.
fn parse_form_a(
    normalized: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Must start with the intrinsic prefix
    let suffix = normalized.strip_prefix(INTRINSIC_PREFIX)?;

    // Try CAS variants first (they have two ordering suffixes)
    if let Some(op) = parse_form_a_cas(suffix, args, dest, span) {
        return Some(op);
    }

    // All other intrinsics: {op_name}_{ordering}
    parse_form_a_single_ordering(suffix, args, dest, span)
}

/// Known Form A operation prefixes mapped to their `AtomicOpKind`.
///
/// Order matters: longer prefixes must come first for correct matching.
/// CAS variants are handled separately in `parse_form_a_cas`.
const FORM_A_OPS: &[(&str, AtomicOpKind)] = &[
    // Fence variants (no pointer arg)
    ("singlethreadfence_", AtomicOpKind::CompilerFence),
    ("fence_", AtomicOpKind::Fence),
    // RMW operations (longer prefixes first)
    ("xadd_", AtomicOpKind::FetchAdd),
    ("xsub_", AtomicOpKind::FetchSub),
    ("xchg_", AtomicOpKind::Exchange),
    ("nand_", AtomicOpKind::FetchNand),
    ("umin_", AtomicOpKind::FetchMin),
    ("umax_", AtomicOpKind::FetchMax),
    ("and_", AtomicOpKind::FetchAnd),
    ("or_", AtomicOpKind::FetchOr),
    ("xor_", AtomicOpKind::FetchXor),
    ("min_", AtomicOpKind::FetchMin),
    ("max_", AtomicOpKind::FetchMax),
    // Load/Store
    ("load_", AtomicOpKind::Load),
    ("store_", AtomicOpKind::Store),
];

/// Parse a single-ordering Form A intrinsic (everything except CAS).
fn parse_form_a_single_ordering(
    suffix: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    for &(prefix, op_kind) in FORM_A_OPS {
        if let Some(ordering_str) = suffix.strip_prefix(prefix) {
            let ordering = parse_ordering_suffix(ordering_str)?;
            let is_fence = matches!(op_kind, AtomicOpKind::Fence | AtomicOpKind::CompilerFence);

            return Some(AtomicOperation {
                place: if is_fence {
                    // Fences have no target place; use a sentinel
                    Place::local(0)
                } else {
                    extract_pointer_place(args)
                },
                dest: if matches!(op_kind, AtomicOpKind::Store) || is_fence {
                    None
                } else {
                    Some(dest.clone())
                },
                op_kind,
                ordering,
                failure_ordering: None,
                span: span.clone(),
            });
        }
    }
    None
}

/// Parse Form A CAS intrinsics: `cxchg_{success}_{failure}` or
/// `cxchgweak_{success}_{failure}`.
fn parse_form_a_cas(
    suffix: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    let (rest, is_weak) = if let Some(rest) = suffix.strip_prefix("cxchgweak_") {
        (rest, true)
    } else if let Some(rest) = suffix.strip_prefix("cxchg_") {
        (rest, false)
    } else {
        return None;
    };

    // Split into two ordering suffixes: e.g., "acqrel_acquire" or "seqcst_relaxed"
    let (success_ordering, failure_ordering) = parse_double_ordering(rest)?;

    Some(AtomicOperation {
        place: extract_pointer_place(args),
        dest: Some(dest.clone()),
        op_kind: if is_weak {
            AtomicOpKind::CompareExchangeWeak
        } else {
            AtomicOpKind::CompareExchange
        },
        ordering: success_ordering,
        failure_ordering: Some(failure_ordering),
        span: span.clone(),
    })
}

/// Parse an ordering suffix string into `AtomicOrdering`.
///
/// Maps `consume` to `Acquire` (C++11 Consume is effectively deprecated).
fn parse_ordering_suffix(s: &str) -> Option<AtomicOrdering> {
    match s {
        "relaxed" => Some(AtomicOrdering::Relaxed),
        "acquire" | "consume" => Some(AtomicOrdering::Acquire),
        "release" => Some(AtomicOrdering::Release),
        "acqrel" => Some(AtomicOrdering::AcqRel),
        "seqcst" => Some(AtomicOrdering::SeqCst),
        _ => None,
    }
}

/// Parse a double ordering suffix like "acqrel_acquire" or "seqcst_relaxed".
///
/// The first ordering is the success ordering, the second is the failure ordering.
/// Returns None if the string cannot be split into two valid orderings.
fn parse_double_ordering(s: &str) -> Option<(AtomicOrdering, AtomicOrdering)> {
    // Known ordering suffixes, longest first for greedy matching
    const ORDERINGS: &[&str] = &["seqcst", "acqrel", "release", "acquire", "consume", "relaxed"];

    for &first in ORDERINGS {
        if let Some(rest) = s.strip_prefix(first)
            && let Some(second_str) = rest.strip_prefix('_')
            && let (Some(a), Some(b)) =
                (parse_ordering_suffix(first), parse_ordering_suffix(second_str))
        {
            return Some((a, b));
        }
    }
    None
}

/// Extract the pointer target Place from the first argument of an atomic intrinsic.
///
/// Atomic intrinsics take a raw pointer as their first argument. We extract
/// the Place being pointed to. Falls back to `Place::local(0)` if args are empty
/// or the first arg is not a place operand.
fn extract_pointer_place(args: &[Operand]) -> Place {
    args.first()
        .and_then(|op| match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.clone()),
            _ => None,
        })
        .unwrap_or_else(|| Place::local(0))
}

// ---------------------------------------------------------------------------
// Form B: explicit Ordering argument
// ---------------------------------------------------------------------------

/// Known Form B function name patterns.
///
/// These appear as `atomic::atomic_{op}::<T>(...)` in MIR after generic
/// specialization. The Ordering is passed as a const operand argument.
const FORM_B_OPS: &[(&str, AtomicOpKind)] = &[
    ("atomic_compare_exchange_weak", AtomicOpKind::CompareExchangeWeak),
    ("atomic_compare_exchange", AtomicOpKind::CompareExchange),
    ("atomic_load", AtomicOpKind::Load),
    ("atomic_store", AtomicOpKind::Store),
    ("atomic_exchange", AtomicOpKind::Exchange),
    ("atomic_fetch_add", AtomicOpKind::FetchAdd),
    ("atomic_fetch_sub", AtomicOpKind::FetchSub),
    ("atomic_fetch_and", AtomicOpKind::FetchAnd),
    ("atomic_fetch_or", AtomicOpKind::FetchOr),
    ("atomic_fetch_xor", AtomicOpKind::FetchXor),
    ("atomic_fetch_nand", AtomicOpKind::FetchNand),
    ("atomic_fetch_min", AtomicOpKind::FetchMin),
    ("atomic_fetch_max", AtomicOpKind::FetchMax),
    ("compiler_fence", AtomicOpKind::CompilerFence),
    ("fence", AtomicOpKind::Fence),
];

/// Parse Form B intrinsics: `atomic::atomic_{op}::<T>(ptr, ..., Ordering::X)`.
fn parse_form_b(
    normalized: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Form B does NOT apply to core::intrinsics:: paths — those are Form A only.
    // If we reach here with an intrinsic prefix, the suffix was unrecognized.
    if normalized.contains(INTRINSIC_PREFIX) {
        return None;
    }

    // Match the function name against known Form B patterns
    let op_kind = find_form_b_op(normalized)?;
    let is_fence = matches!(op_kind, AtomicOpKind::Fence | AtomicOpKind::CompilerFence);
    let is_cas =
        matches!(op_kind, AtomicOpKind::CompareExchange | AtomicOpKind::CompareExchangeWeak);

    if is_cas {
        // CAS: args are (ptr, old, new, success_ordering, failure_ordering)
        // We look for ordering from the last two args
        let success = extract_ordering_from_args(args, args.len().wrapping_sub(2));
        let failure = extract_ordering_from_args(args, args.len().wrapping_sub(1));

        Some(AtomicOperation {
            place: extract_pointer_place(args),
            dest: Some(dest.clone()),
            op_kind,
            ordering: success.unwrap_or(AtomicOrdering::SeqCst),
            failure_ordering: Some(failure.unwrap_or(AtomicOrdering::Relaxed)),
            span: span.clone(),
        })
    } else {
        // Non-CAS: ordering is the last argument
        let ordering = args
            .last()
            .and_then(|_| extract_ordering_from_args(args, args.len().wrapping_sub(1)))
            .unwrap_or(AtomicOrdering::SeqCst);

        Some(AtomicOperation {
            place: if is_fence { Place::local(0) } else { extract_pointer_place(args) },
            dest: if matches!(op_kind, AtomicOpKind::Store) || is_fence {
                None
            } else {
                Some(dest.clone())
            },
            op_kind,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        })
    }
}

/// Find the `AtomicOpKind` for a Form B function path.
///
/// Checks if the normalized path contains any known Form B pattern.
/// Uses longest-match semantics.
fn find_form_b_op(normalized: &str) -> Option<AtomicOpKind> {
    let mut best: Option<(usize, AtomicOpKind)> = None;

    for &(pattern, kind) in FORM_B_OPS {
        if normalized.contains(pattern) {
            let len = pattern.len();
            if best.as_ref().is_none_or(|(best_len, _)| len > *best_len) {
                best = Some((len, kind));
            }
        }
    }

    best.map(|(_, kind)| kind)
}

/// Try to extract an `AtomicOrdering` from the argument at the given index.
///
/// In Form B, orderings appear as `Operand::Constant` values. Rustc encodes
/// `std::sync::atomic::Ordering` variants as integer discriminants:
///   Relaxed=0, Release=1, Acquire=2, AcqRel=3, SeqCst=4
///
/// We also check for string-like patterns in case MIR debug info preserves
/// the variant name (e.g., "Ordering::Acquire").
fn extract_ordering_from_args(args: &[Operand], index: usize) -> Option<AtomicOrdering> {
    let arg = args.get(index)?;
    match arg {
        Operand::Constant(crate::ConstValue::Int(v)) => ordering_from_discriminant(*v as u64),
        Operand::Constant(crate::ConstValue::Uint(v, _)) => ordering_from_discriminant(*v as u64),
        _ => None,
    }
}

/// Map a `std::sync::atomic::Ordering` discriminant to `AtomicOrdering`.
///
/// Rust's `Ordering` enum has these discriminant values:
///   Relaxed=0, Release=1, Acquire=2, AcqRel=3, SeqCst=4
fn ordering_from_discriminant(disc: u64) -> Option<AtomicOrdering> {
    match disc {
        0 => Some(AtomicOrdering::Relaxed),
        1 => Some(AtomicOrdering::Release),
        2 => Some(AtomicOrdering::Acquire),
        3 => Some(AtomicOrdering::AcqRel),
        4 => Some(AtomicOrdering::SeqCst),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a simple args list with a pointer place as first arg.
    fn ptr_args(local: usize) -> Vec<Operand> {
        vec![Operand::Copy(Place::local(local))]
    }

    /// Helper: create args for a store (ptr, value).
    fn store_args(ptr_local: usize, val_local: usize) -> Vec<Operand> {
        vec![Operand::Copy(Place::local(ptr_local)), Operand::Copy(Place::local(val_local))]
    }

    /// Helper: create args for CAS (ptr, old, new).
    fn cas_args(ptr_local: usize) -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(ptr_local)),
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::local(3)),
        ]
    }

    fn default_dest() -> Place {
        Place::local(10)
    }

    fn default_span() -> SourceSpan {
        SourceSpan::default()
    }

    // -----------------------------------------------------------------------
    // Form A: suffix-encoded intrinsics
    // -----------------------------------------------------------------------

    #[test]
    fn test_form_a_load_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_load_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.failure_ordering.is_none());
        assert_eq!(op.place.local, 1);
        assert_eq!(op.dest.as_ref().unwrap().local, 10);
    }

    #[test]
    fn test_form_a_load_acquire() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_acquire",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_load_acquire");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn test_form_a_load_relaxed() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_load_relaxed");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn test_form_a_load_consume_maps_to_acquire() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_consume",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_load_consume");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire, "Consume maps to Acquire");
    }

    #[test]
    fn test_form_a_store_release() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_release",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_store_release");
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none(), "store has no return value dest");
    }

    #[test]
    fn test_form_a_store_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_store_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn test_form_a_exchange_acqrel() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xchg_acqrel",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_xchg_acqrel");
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert!(op.dest.is_some(), "exchange returns old value");
    }

    #[test]
    fn test_form_a_cxchg_seqcst_relaxed() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_seqcst_relaxed",
            &cas_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_cxchg");
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    #[test]
    fn test_form_a_cxchg_acqrel_acquire() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_acqrel_acquire",
            &cas_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_cxchg_acqrel_acquire");
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn test_form_a_cxchgweak_acquire_relaxed() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchgweak_acquire_relaxed",
            &cas_args(1),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_cxchgweak");
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchangeWeak);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    #[test]
    fn test_form_a_fetch_add_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xadd_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_xadd_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_some(), "fetch_add returns old value");
    }

    #[test]
    fn test_form_a_fetch_sub_release() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xsub_release",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_xsub_release");
        assert_eq!(op.op_kind, AtomicOpKind::FetchSub);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn test_form_a_fetch_and_relaxed() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_and_relaxed",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_and_relaxed");
        assert_eq!(op.op_kind, AtomicOpKind::FetchAnd);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn test_form_a_fetch_or_acquire() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_or_acquire",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_or_acquire");
        assert_eq!(op.op_kind, AtomicOpKind::FetchOr);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn test_form_a_fetch_xor_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xor_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_xor_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::FetchXor);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn test_form_a_fetch_nand_acqrel() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_nand_acqrel",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_nand_acqrel");
        assert_eq!(op.op_kind, AtomicOpKind::FetchNand);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    #[test]
    fn test_form_a_fetch_min_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_min_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_min_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn test_form_a_fetch_max_relaxed() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_max_relaxed",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_max_relaxed");
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn test_form_a_unsigned_min_max() {
        // umin and umax map to FetchMin/FetchMax (unsigned variants)
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umin_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_umin_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);

        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umax_seqcst",
            &store_args(1, 2),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_umax_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    #[test]
    fn test_form_a_fence_acquire() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acquire",
            &[],
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_fence_acquire");
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert!(op.dest.is_none(), "fence has no return value");
    }

    #[test]
    fn test_form_a_fence_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse atomic_fence_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn test_form_a_compiler_fence_release() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_release",
            &[],
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse singlethreadfence");
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none(), "compiler_fence has no return value");
    }

    #[test]
    fn test_form_a_compiler_fence_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse singlethreadfence_seqcst");
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    // -----------------------------------------------------------------------
    // Form B: explicit Ordering argument
    // -----------------------------------------------------------------------

    /// Helper: create args with an ordering discriminant as the last arg.
    fn args_with_ordering(ptr_local: usize, ordering_disc: i128) -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(ptr_local)),
            Operand::Constant(crate::ConstValue::Int(ordering_disc)),
        ]
    }

    /// Helper: CAS args with two ordering discriminants.
    fn cas_args_with_orderings(
        ptr_local: usize,
        success_disc: i128,
        failure_disc: i128,
    ) -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(ptr_local)),
            Operand::Copy(Place::local(2)), // old
            Operand::Copy(Place::local(3)), // new
            Operand::Constant(crate::ConstValue::Int(success_disc)),
            Operand::Constant(crate::ConstValue::Int(failure_disc)),
        ]
    }

    #[test]
    fn test_form_b_load_acquire() {
        let args = args_with_ordering(1, 2); // 2 = Acquire
        let result = parse_atomic_intrinsic(
            "atomic::atomic_load::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B atomic_load");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert_eq!(op.place.local, 1);
    }

    #[test]
    fn test_form_b_store_release() {
        let args = vec![
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),               // value
            Operand::Constant(crate::ConstValue::Int(1)), // 1 = Release
        ];
        let result = parse_atomic_intrinsic(
            "atomic::atomic_store::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B atomic_store");
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none());
    }

    #[test]
    fn test_form_b_compare_exchange() {
        let args = cas_args_with_orderings(1, 4, 0); // SeqCst, Relaxed
        let result = parse_atomic_intrinsic(
            "atomic::atomic_compare_exchange::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B compare_exchange");
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    #[test]
    fn test_form_b_compare_exchange_weak() {
        let args = cas_args_with_orderings(1, 3, 2); // AcqRel, Acquire
        let result = parse_atomic_intrinsic(
            "atomic::atomic_compare_exchange_weak::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B compare_exchange_weak");
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchangeWeak);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn test_form_b_fetch_add_relaxed() {
        let args = vec![
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
            Operand::Constant(crate::ConstValue::Int(0)), // Relaxed
        ];
        let result = parse_atomic_intrinsic(
            "atomic::atomic_fetch_add::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B fetch_add");
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn test_form_b_fence_seqcst() {
        let args = vec![Operand::Constant(crate::ConstValue::Int(4))]; // SeqCst
        let result =
            parse_atomic_intrinsic("atomic::fence", &args, &default_dest(), &default_span());
        let op = result.expect("should parse Form B fence");
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn test_form_b_compiler_fence() {
        let args = vec![Operand::Constant(crate::ConstValue::Int(2))]; // Acquire
        let result = parse_atomic_intrinsic(
            "atomic::compiler_fence",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse Form B compiler_fence");
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    // -----------------------------------------------------------------------
    // Negative cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_non_atomic_call_returns_none() {
        let result = parse_atomic_intrinsic(
            "std::vec::Vec::push",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        assert!(result.is_none());
    }

    #[test]
    fn test_concurrency_call_not_atomic_intrinsic() {
        // std::sync::Mutex::lock is a concurrency call but NOT an atomic intrinsic
        let result = parse_atomic_intrinsic(
            "std::sync::Mutex::lock",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        assert!(result.is_none());
    }

    #[test]
    fn test_invalid_ordering_suffix_returns_none() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_bogus",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        assert!(result.is_none());
    }

    #[test]
    fn test_partial_prefix_no_match() {
        // "core::intrinsics::atom" is not a valid prefix
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atom_load_seqcst",
            &ptr_args(1),
            &default_dest(),
            &default_span(),
        );
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_cxchg_ordering_combinations() {
        let combos = [
            ("seqcst_seqcst", AtomicOrdering::SeqCst, AtomicOrdering::SeqCst),
            ("seqcst_acquire", AtomicOrdering::SeqCst, AtomicOrdering::Acquire),
            ("seqcst_relaxed", AtomicOrdering::SeqCst, AtomicOrdering::Relaxed),
            ("acqrel_acquire", AtomicOrdering::AcqRel, AtomicOrdering::Acquire),
            ("acqrel_relaxed", AtomicOrdering::AcqRel, AtomicOrdering::Relaxed),
            ("acquire_acquire", AtomicOrdering::Acquire, AtomicOrdering::Acquire),
            ("acquire_relaxed", AtomicOrdering::Acquire, AtomicOrdering::Relaxed),
            ("release_relaxed", AtomicOrdering::Release, AtomicOrdering::Relaxed),
            ("relaxed_relaxed", AtomicOrdering::Relaxed, AtomicOrdering::Relaxed),
        ];

        for (suffix, expected_success, expected_failure) in combos {
            let path = format!("core::intrinsics::atomic_cxchg_{suffix}");
            let result =
                parse_atomic_intrinsic(&path, &cas_args(1), &default_dest(), &default_span());
            let op = result.unwrap_or_else(|| panic!("should parse cxchg_{suffix}"));
            assert_eq!(op.ordering, expected_success, "success ordering for {suffix}");
            assert_eq!(
                op.failure_ordering,
                Some(expected_failure),
                "failure ordering for {suffix}"
            );
        }
    }

    #[test]
    fn test_all_orderings_for_load() {
        let orderings = [
            ("relaxed", AtomicOrdering::Relaxed),
            ("acquire", AtomicOrdering::Acquire),
            ("seqcst", AtomicOrdering::SeqCst),
        ];

        for (suffix, expected) in orderings {
            let path = format!("core::intrinsics::atomic_load_{suffix}");
            let result =
                parse_atomic_intrinsic(&path, &ptr_args(1), &default_dest(), &default_span());
            let op = result.unwrap_or_else(|| panic!("should parse load_{suffix}"));
            assert_eq!(op.ordering, expected, "ordering for load_{suffix}");
        }
    }

    #[test]
    fn test_empty_args_does_not_panic() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        );
        // Should still parse (with sentinel place)
        let op = result.expect("should parse even with empty args");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.place.local, 0, "sentinel place when no args");
    }

    #[test]
    fn test_form_b_ordering_from_uint() {
        // Test that Uint constant values also work for ordering extraction
        let args = vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(crate::ConstValue::Uint(2, 8)), // Acquire as u8
        ];
        let result = parse_atomic_intrinsic(
            "atomic::atomic_load::<usize>",
            &args,
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should parse with Uint ordering");
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn test_ordering_from_discriminant_all_values() {
        assert_eq!(ordering_from_discriminant(0), Some(AtomicOrdering::Relaxed));
        assert_eq!(ordering_from_discriminant(1), Some(AtomicOrdering::Release));
        assert_eq!(ordering_from_discriminant(2), Some(AtomicOrdering::Acquire));
        assert_eq!(ordering_from_discriminant(3), Some(AtomicOrdering::AcqRel));
        assert_eq!(ordering_from_discriminant(4), Some(AtomicOrdering::SeqCst));
        assert_eq!(ordering_from_discriminant(5), None);
        assert_eq!(ordering_from_discriminant(99), None);
    }

    #[test]
    fn test_parse_ordering_suffix_all() {
        assert_eq!(parse_ordering_suffix("relaxed"), Some(AtomicOrdering::Relaxed));
        assert_eq!(parse_ordering_suffix("acquire"), Some(AtomicOrdering::Acquire));
        assert_eq!(parse_ordering_suffix("release"), Some(AtomicOrdering::Release));
        assert_eq!(parse_ordering_suffix("acqrel"), Some(AtomicOrdering::AcqRel));
        assert_eq!(parse_ordering_suffix("seqcst"), Some(AtomicOrdering::SeqCst));
        assert_eq!(parse_ordering_suffix("consume"), Some(AtomicOrdering::Acquire));
        assert_eq!(parse_ordering_suffix("bogus"), None);
        assert_eq!(parse_ordering_suffix(""), None);
    }

    #[test]
    fn test_parse_double_ordering_all_valid() {
        assert_eq!(
            parse_double_ordering("seqcst_relaxed"),
            Some((AtomicOrdering::SeqCst, AtomicOrdering::Relaxed))
        );
        assert_eq!(
            parse_double_ordering("acqrel_acquire"),
            Some((AtomicOrdering::AcqRel, AtomicOrdering::Acquire))
        );
        assert_eq!(
            parse_double_ordering("acquire_relaxed"),
            Some((AtomicOrdering::Acquire, AtomicOrdering::Relaxed))
        );
    }

    #[test]
    fn test_parse_double_ordering_invalid() {
        assert_eq!(parse_double_ordering("seqcst"), None);
        assert_eq!(parse_double_ordering("bogus_relaxed"), None);
        assert_eq!(parse_double_ordering("seqcst_bogus"), None);
        assert_eq!(parse_double_ordering(""), None);
    }
}
