//! Agentic guidance: per-obligation, AI-actionable remediation.
//!
//! Trust is a *feedback partner*, not a source editor. When an obligation cannot
//! be discharged, Trust returns **guidance**: the property that must hold, the
//! failure mode (illustrated by a concrete counterexample when the solver
//! produced one), and a ranked set of source-level changes — each with a proof
//! sketch of *why* it discharges the obligation. An AI coding loop consumes this
//! to improve the code; on the next build the obligation discharges and the
//! guard disappears (the "compilation as improvement" flywheel).
//!
//! This lives in `trust-types` (next to [`VcKind`]) so every layer — the
//! verifier, the report, the LSP — produces identical guidance from the same
//! source of truth, and so it is unit-testable without the full compiler.

use serde::{Deserialize, Serialize};

use crate::VcKind;

/// Structured, AI-actionable guidance for a single proof obligation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AgenticGuidance {
    /// The property that must hold for the obligation to discharge, in prose
    /// (e.g. "the copy count must be `<=` the destination allocation size").
    pub must_hold: String,
    /// How the obligation fails — the shape of a violating execution. When a
    /// concrete counterexample is available it is woven in by
    /// [`AgenticGuidance::with_counterexample`].
    pub failure_mode: String,
    /// Concrete, ranked source-level changes that would discharge the
    /// obligation. The first entry is the recommended fix.
    pub suggested_fixes: Vec<SuggestedFix>,
    /// Why the recommended fix discharges the obligation — a proof sketch the
    /// AI (or a human reviewer) can check.
    pub proof_sketch: String,
}

/// One concrete remediation the consuming agent can apply.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SuggestedFix {
    /// Stable machine tag for the kind of change
    /// (e.g. "bounds_check", "revalidate_length", "precondition").
    pub kind: String,
    /// A concrete instruction an agent can act on.
    pub change: String,
    /// Confidence in `[0.0, 1.0]` that this change discharges the obligation,
    /// stored as a string for serialization stability (matching the crate's
    /// convention for non-`f64`-stable report fields).
    pub confidence: String,
}

impl SuggestedFix {
    fn new(kind: &str, change: &str, confidence: f64) -> Self {
        Self {
            kind: kind.to_string(),
            change: change.to_string(),
            confidence: format!("{confidence:.2}"),
        }
    }
}

impl AgenticGuidance {
    /// Enrich the failure mode with a concrete counterexample rendering
    /// (e.g. `"len = 4096, live_size = 512"`). Returns `self` for chaining.
    #[must_use]
    pub fn with_counterexample(mut self, counterexample: &str) -> Self {
        if !counterexample.trim().is_empty() {
            self.failure_mode =
                format!("{} Concrete counterexample: {counterexample}.", self.failure_mode);
        }
        self
    }
}

impl VcKind {
    /// AI-actionable guidance for this obligation, or `None` when Trust has no
    /// specific remediation beyond the obligation description itself.
    ///
    /// Guidance is keyed off the obligation *kind* so it is identical wherever
    /// it is produced. Callers that have a solver counterexample should refine
    /// the result with [`AgenticGuidance::with_counterexample`].
    #[must_use]
    pub fn agentic_guidance(&self) -> Option<AgenticGuidance> {
        match self {
            VcKind::CopyBoundsViolation { direction, callee, .. } => {
                let side = if direction == "src" { "source" } else { "destination" };
                let verb = if direction == "src" { "read past" } else { "write past" };
                Some(AgenticGuidance {
                    must_hold: format!(
                        "the element/byte count of `{callee}` must be provably `<=` the {side} \
                         allocation's size (`ptr + count <= base + size`)."
                    ),
                    failure_mode: format!(
                        "the count is derived from data the function does not bound, so it can \
                         {verb} the {side} allocation — an out-of-bounds {} and undefined behavior.",
                        if direction == "src" { "read" } else { "write" }
                    ),
                    suggested_fixes: vec![
                        SuggestedFix::new(
                            "bounds_check",
                            &format!(
                                "before the `{callee}`, return an error (or clamp) unless \
                                 `count <= {side}_capacity`; compute the capacity from the \
                                 {side} slice/allocation length, not from the input."
                            ),
                            0.9,
                        ),
                        SuggestedFix::new(
                            "precondition",
                            &format!(
                                "add `requires count <= {side}.len()` to the function \
                                 signature so the obligation is discharged at every call \
                                 site."
                            ),
                            0.7,
                        ),
                    ],
                    proof_sketch: format!(
                        "with `count <= {side}_capacity` established on the path reaching the \
                         copy, `ptr + count <= base + size` holds, so the {side} access stays \
                         in bounds and the obligation is UNSAT (no violating model)."
                    ),
                })
            }
            VcKind::ExternallyMutableAllocationBounds { allocation_kind, live_size, .. } => {
                Some(AgenticGuidance {
                    must_hold: format!(
                        "the length captured when the {allocation_kind} view was created must be \
                         proven `<=` its live size (`{live_size}`) at every dereference."
                    ),
                    failure_mode: format!(
                        "the backing size can change after the view is created (e.g. another \
                         process truncates the file), so a length captured once is stale; a later \
                         access reads past the live region — SIGBUS or an out-of-bounds read."
                    ),
                    suggested_fixes: vec![
                        SuggestedFix::new(
                            "revalidate_length",
                            &format!(
                                "re-read `{live_size}` immediately before each access and \
                                 validate the offset/length against it with checked arithmetic; \
                                 return an error on shrink instead of slicing."
                            ),
                            0.85,
                        ),
                        SuggestedFix::new(
                            "single_writer_invariant",
                            "enforce (and document) exclusive ownership of the backing object for \
                             the lifetime of the mapping, e.g. an advisory lock, so the size \
                             cannot change underneath the view.",
                            0.6,
                        ),
                        SuggestedFix::new(
                            "fault_handler",
                            "install a SIGBUS handler scoped to the mapping that converts the \
                             fault into a recoverable error (last resort; weaker than \
                             re-validation).",
                            0.4,
                        ),
                    ],
                    proof_sketch: format!(
                        "re-reading `{live_size}` and checking `offset + len <= {live_size}` on \
                         the access path makes the captured length a *checked* bound rather than \
                         a *trusted* one, so `len <= {live_size}` holds at the dereference and the \
                         obligation discharges."
                    ),
                })
            }
            VcKind::ArithmeticOverflow { op, .. } => Some(AgenticGuidance {
                must_hold: format!("the `{op:?}` result must fit in its integer type."),
                failure_mode:
                    "operands can reach magnitudes whose result wraps (or panics in debug)."
                        .to_string(),
                suggested_fixes: vec![
                    SuggestedFix::new(
                        "checked_arithmetic",
                        "use `checked_*`/`saturating_*`/`try_into` and handle the overflow case, \
                         or constrain the operands with a precondition.",
                        0.85,
                    ),
                ],
                proof_sketch:
                    "a `checked_*` path makes overflow an explicit, handled value, so no execution \
                     reaches the wrapping result and the obligation is UNSAT."
                        .to_string(),
            }),
            VcKind::DivisionByZero | VcKind::RemainderByZero => Some(AgenticGuidance {
                must_hold: "the divisor must be provably non-zero at the operation.".to_string(),
                failure_mode: "the divisor can be zero on some path, which is UB/panic.".to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "nonzero_guard",
                    "guard with `if d != 0` (or use `NonZero*`/`checked_div`) and handle the zero \
                     case before dividing.",
                    0.9,
                )],
                proof_sketch:
                    "with `d != 0` dominating the division, every reaching state has a non-zero \
                     divisor, discharging the obligation."
                        .to_string(),
            }),
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => Some(AgenticGuidance {
                must_hold: "the index must be provably `< len` at the access.".to_string(),
                failure_mode: "the index can reach or exceed `len`, an out-of-bounds access."
                    .to_string(),
                suggested_fixes: vec![
                    SuggestedFix::new(
                        "bounds_check",
                        "check `i < slice.len()` before indexing, or use `.get(i)` and handle \
                         `None`.",
                        0.9,
                    ),
                    SuggestedFix::new(
                        "loop_invariant",
                        "if `i` is a loop variable, add an invariant `i < len` so the obligation \
                         is discharged inductively.",
                        0.7,
                    ),
                ],
                proof_sketch:
                    "establishing `i < len` on the access path makes the bounds predicate hold, \
                     so no model violates it."
                        .to_string(),
            }),
            VcKind::ShiftOverflow { .. } => Some(AgenticGuidance {
                must_hold: "the shift amount must be `<` the bit width of the type.".to_string(),
                failure_mode: "the shift amount can reach or exceed the bit width (UB / wraps)."
                    .to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "mask_or_check",
                    "mask the shift amount (`amt & (BITS - 1)`) or guard `amt < BITS`, or use \
                     `checked_shl`/`checked_shr` and handle the `None`.",
                    0.85,
                )],
                proof_sketch:
                    "constraining the shift amount below the bit width makes the shift well-defined, \
                     so the obligation discharges."
                        .to_string(),
            }),
            VcKind::CastOverflow { .. } => Some(AgenticGuidance {
                must_hold: "the source value must fit in the destination type.".to_string(),
                failure_mode: "an `as` cast can truncate/wrap when the value exceeds the target range."
                    .to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "try_into",
                    "use `TryInto`/`try_from` and handle the error, or add a range check before the \
                     cast.",
                    0.85,
                )],
                proof_sketch:
                    "a checked conversion makes out-of-range an explicit, handled value, so no \
                     reaching state truncates."
                        .to_string(),
            }),
            // NegationOverflow covers BOTH `-x` and `iN::abs(x)`: both overflow at
            // `T::MIN` because it has no positive representation (`abs` is the negation
            // of a negative, so `abs(MIN)` = `-MIN` overflows identically). The guidance
            // names both so the suggested fix matches the actual call site.
            VcKind::NegationOverflow { .. } => Some(AgenticGuidance {
                must_hold: "the operand must not be the type's minimum value at negation / `abs`."
                    .to_string(),
                failure_mode: "negating or taking `abs` of `T::MIN` overflows (no positive \
                               representation)."
                    .to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "checked_neg / checked_abs",
                    "use `checked_neg`/`wrapping_neg` (for `-x`) or `checked_abs`/`wrapping_abs`/\
                     `unsigned_abs` (for `.abs()`) deliberately, or guard against `T::MIN` before \
                     the operation.",
                    0.85,
                )],
                proof_sketch: "excluding `T::MIN` on the negation / `abs` path makes the result \
                               representable, discharging the obligation."
                    .to_string(),
            }),
            VcKind::UseAfterFree => Some(AgenticGuidance {
                must_hold: "the allocation must still be live at this access.".to_string(),
                failure_mode: "the pointer is dereferenced after its allocation was freed."
                    .to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "lifetime_or_ownership",
                    "tie the pointer's use to the owner's lifetime (borrow instead of raw pointer), \
                     or move the free after the last use; null the pointer on free and check it.",
                    0.8,
                )],
                proof_sketch:
                    "ordering every access strictly before the free (enforced by ownership/lifetimes) \
                     makes a use-after-free unreachable."
                        .to_string(),
            }),
            VcKind::DoubleFree => Some(AgenticGuidance {
                must_hold: "each allocation must be freed at most once.".to_string(),
                failure_mode: "the same allocation reaches `free`/`drop` on two paths.".to_string(),
                suggested_fixes: vec![SuggestedFix::new(
                    "single_owner",
                    "give the allocation a single owner (RAII/`Drop`), or take ownership of the \
                     pointer on free (`Option::take`) so a second free sees `None`.",
                    0.8,
                )],
                proof_sketch: "a single-owner discipline makes a second free unreachable.".to_string(),
            }),
            VcKind::AliasingViolation { mutable } => Some(AgenticGuidance {
                must_hold: "a `&mut` must be exclusive — no other live reference may alias it."
                    .to_string(),
                failure_mode: if *mutable {
                    "two `&mut` to the same location are live at once (UB).".to_string()
                } else {
                    "a `&mut` coexists with a live shared `&` (UB).".to_string()
                },
                suggested_fixes: vec![SuggestedFix::new(
                    "split_or_sequence",
                    "split the borrows (disjoint fields / `split_at_mut`), sequence them so they \
                     don't overlap, or use a `Cell`/`RefCell` for interior mutability.",
                    0.75,
                )],
                proof_sketch:
                    "making the `&mut`'s region disjoint from every other live reference restores \
                     exclusivity, discharging the obligation."
                        .to_string(),
            }),
            VcKind::NonTermination { context, measure } => Some(AgenticGuidance {
                must_hold: format!(
                    "the {context} must have a measure that strictly decreases and is bounded below."
                ),
                failure_mode: format!("`{measure}` may not decrease, so the {context} can run forever."),
                suggested_fixes: vec![SuggestedFix::new(
                    "decreases_clause",
                    if context == "recursion" {
                        "add a function-level `decreases <measure>` clause that provably \
                         shrinks at every recursive call (and is `>= 0`), or restructure the \
                         recursion so progress is explicit."
                    } else {
                        "add a loop-local `decreases <measure>` clause whose unsigned measure \
                         step executes on every backedge, or restructure the loop so progress is \
                         explicit."
                    },
                    0.7,
                )],
                proof_sketch: "a well-founded decreasing measure rules out an infinite descent, so \
                               the function terminates."
                    .to_string(),
            }),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copy_bounds_guidance_is_actionable_for_dst() {
        let g = VcKind::CopyBoundsViolation {
            callee: "copy_nonoverlapping".into(),
            direction: "dst".into(),
            detail: "x".into(),
        }
        .agentic_guidance()
        .expect("copy bounds must have guidance");
        assert!(g.must_hold.contains("destination"));
        assert!(g.failure_mode.contains("write past"));
        assert_eq!(g.suggested_fixes[0].kind, "bounds_check");
        assert!(!g.proof_sketch.is_empty());
    }

    #[test]
    fn external_mutable_guidance_recommends_revalidation() {
        let g = VcKind::ExternallyMutableAllocationBounds {
            allocation_kind: "mmap_file".into(),
            live_size: "live_file_len".into(),
            detail: "x".into(),
        }
        .agentic_guidance()
        .expect("external-mutable bounds must have guidance");
        // The top-ranked fix for a truncatable mmap is to re-validate the length.
        assert_eq!(g.suggested_fixes[0].kind, "revalidate_length");
        assert!(g.must_hold.contains("live_file_len"));
        assert!(g.failure_mode.contains("SIGBUS"));
    }

    #[test]
    fn counterexample_is_woven_into_failure_mode() {
        let g = VcKind::ExternallyMutableAllocationBounds {
            allocation_kind: "mmap_file".into(),
            live_size: "live_file_len".into(),
            detail: "x".into(),
        }
        .agentic_guidance()
        .unwrap()
        .with_counterexample("mapped_len = 4096, live_file_len = 512");
        assert!(g.failure_mode.contains("Concrete counterexample"));
        assert!(g.failure_mode.contains("4096"));
    }

    #[test]
    fn guidance_serializes_to_json() {
        let g = VcKind::DivisionByZero.agentic_guidance().unwrap();
        let json = serde_json::to_string(&g).unwrap();
        let back: AgenticGuidance = serde_json::from_str(&json).unwrap();
        assert_eq!(g, back);
    }

    #[test]
    fn kinds_without_specific_guidance_return_none() {
        assert!(VcKind::Postcondition.agentic_guidance().is_none());
    }

    #[test]
    fn extended_l0_kinds_have_actionable_guidance() {
        use crate::Ty;
        let cases: Vec<VcKind> = vec![
            VcKind::ShiftOverflow { op: crate::BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
            VcKind::CastOverflow { from_ty: Ty::u64(), to_ty: Ty::u8() },
            VcKind::NegationOverflow { ty: Ty::i32() },
            VcKind::UseAfterFree,
            VcKind::DoubleFree,
            VcKind::AliasingViolation { mutable: true },
            VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
        ];
        for k in cases {
            let g = k.agentic_guidance().unwrap_or_else(|| panic!("{k:?} must have guidance"));
            assert!(!g.must_hold.is_empty(), "{k:?} must_hold empty");
            assert!(!g.suggested_fixes.is_empty(), "{k:?} has no suggested fix");
            assert!(!g.proof_sketch.is_empty(), "{k:?} proof_sketch empty");
        }
    }

    #[test]
    fn termination_guidance_uses_native_function_and_loop_clauses() {
        let loop_guidance = VcKind::NonTermination {
            context: "loop".into(),
            measure: "n".into(),
        }
        .agentic_guidance()
        .unwrap();
        assert!(
            loop_guidance.suggested_fixes[0].change.contains("loop-local `decreases <measure>`")
        );
        assert!(!loop_guidance.suggested_fixes[0].change.contains("#[decreases"));

        let recursion_guidance = VcKind::NonTermination {
            context: "recursion".into(),
            measure: "n".into(),
        }
        .agentic_guidance()
        .unwrap();
        assert!(
            recursion_guidance.suggested_fixes[0]
                .change
                .contains("function-level `decreases <measure>`")
        );
        assert!(!recursion_guidance.suggested_fixes[0].change.contains("#[decreases"));
    }
}
