//! Obligation-parity harness — the seed of the Trust-IR spine Phase-0
//! differential oracle.
//!
//! The migration plan in `docs/TRUST_IR_SPINE.md` (Phase 0) requires a
//! differential oracle that, per function, can assert *trust-ir-derived
//! obligations == trust-types-derived obligations*. Later phases compare the
//! two pipelines directly; this module establishes the trust-ir half of that
//! comparison: a small, dependency-free summary of the safety
//! [`ObligationKind`]s that the existing
//! [`crate::lower_to_trust_ir`] lowering surfaces for a given
//! `VerifiableFunction`.
//!
//! It performs no analysis and adds no behavior to the lowering — it only
//! *observes* the `proof_obligations` the lowering already attaches to a
//! [`trust_ir::Module`], so it can be used as ground truth by the oracle.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

#[cfg(test)]
use trust_ir::inst::Inst;
use trust_ir::proof::ObligationKind;
#[cfg(test)]
use trust_ir::proof::ProofAnnotation;
use trust_types::VerifiableFunction;

use crate::lower::{BridgeError, lower_to_trust_ir};

/// A deterministic, order-independent summary of the proof-obligation kinds
/// present in a lowered [`trust_ir::Module`], keyed by the obligation kind's
/// canonical name (`ObligationKind`'s `Display`, e.g. `"panic_freedom"`,
/// `"precondition"`) with a count of how many obligations of that kind the
/// module carries.
///
/// A `BTreeMap` (rather than the `ObligationKind` enum directly) is used so the
/// summary is `Ord`-keyed, trivially serializable, and stable to diff across
/// the two pipelines the Phase-0 oracle compares — `ObligationKind` is
/// `Eq + Hash` but not `Ord`, so it cannot key a `BTreeMap`.
pub type ObligationKindSummary = BTreeMap<String, usize>;

/// Collect the [`ObligationKindSummary`] for an already-lowered module by
/// tallying its `proof_obligations` by kind name.
///
/// This is the trust-ir-side observation point for the differential oracle:
/// it reads only data the lowering attached, never synthesizing obligations.
pub fn obligation_kind_summary(module: &trust_ir::Module) -> ObligationKindSummary {
    let mut summary = ObligationKindSummary::new();
    for obligation in &module.proof_obligations {
        *summary.entry(obligation.kind.to_string()).or_insert(0) += 1;
    }
    summary
}

/// Convenience: lower `func` via [`lower_to_trust_ir`] and return the
/// [`ObligationKindSummary`] of the resulting module.
///
/// Returns the lowering's [`BridgeError`] unchanged on failure (fail-closed:
/// an input the bridge rejects has no obligation summary to report).
pub fn lowered_obligation_summary(
    func: &VerifiableFunction,
) -> Result<ObligationKindSummary, BridgeError> {
    let module = lower_to_trust_ir(func)?;
    Ok(obligation_kind_summary(&module))
}

/// Number of obligations of `kind` present in a lowered module's summary.
///
/// Convenience for assertions; `0` when the kind is absent.
pub fn obligation_count(summary: &ObligationKindSummary, kind: ObligationKind) -> usize {
    summary.get(&kind.to_string()).copied().unwrap_or(0)
}

/// A deterministic, order-independent tally of the [`ProofAnnotation`]s
/// attached to `Inst::Assert` nodes across a lowered [`trust_ir::Module`],
/// keyed by the annotation's `Debug` name with a count.
///
/// This is the trust-ir-side observation point the Phase-1 increment uses to
/// confirm that each `Terminator::Assert` carries the *faithful* annotation for
/// its `AssertMessage` (e.g. `DivNonZero` for division-by-zero, `InBounds` for
/// a bounds check) instead of the old blanket `NoOverflow`. Asserts that carry
/// no annotation contribute nothing — only present annotations are tallied.
///
/// A `BTreeMap` keyed by the annotation name (rather than the enum) keeps the
/// summary `Ord`-keyed, serializable, and diff-stable; `ProofAnnotation` is not
/// `Ord` and some variants carry payloads, so the name is the stable key.
#[cfg(test)]
pub type AssertAnnotationSummary = BTreeMap<String, usize>;

/// Stable key for a [`ProofAnnotation`] used by [`AssertAnnotationSummary`].
///
/// Uses the variant's `Debug` rendering, which is deterministic and includes
/// payloads (e.g. `Aligned(8)`), so distinct annotations never collide.
#[cfg(test)]
fn annotation_key(annotation: &ProofAnnotation) -> String {
    format!("{annotation:?}")
}

/// Collect the [`AssertAnnotationSummary`] for an already-lowered module by
/// tallying the proof annotations on every `Inst::Assert` node in every block
/// of every function.
///
/// Reads only data the lowering attached; synthesizes nothing.
#[cfg(test)]
pub fn assert_annotation_summary(module: &trust_ir::Module) -> AssertAnnotationSummary {
    let mut summary = AssertAnnotationSummary::new();
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                if matches!(node.inst, Inst::Assert { .. }) {
                    for annotation in &node.proofs {
                        *summary.entry(annotation_key(annotation)).or_insert(0) += 1;
                    }
                }
            }
        }
    }
    summary
}

/// Convenience: lower `func` via [`lower_to_trust_ir`] and return the
/// [`AssertAnnotationSummary`] of the resulting module's assert nodes.
#[cfg(test)]
pub fn lowered_assert_annotation_summary(
    func: &VerifiableFunction,
) -> Result<AssertAnnotationSummary, BridgeError> {
    let module = lower_to_trust_ir(func)?;
    Ok(assert_annotation_summary(&module))
}

/// Number of `Inst::Assert` nodes carrying `annotation` in a lowered module's
/// summary. `0` when the annotation is absent.
#[cfg(test)]
pub fn assert_annotation_count(
    summary: &AssertAnnotationSummary,
    annotation: &ProofAnnotation,
) -> usize {
    summary.get(&annotation_key(annotation)).copied().unwrap_or(0)
}

// Trust (trust-ir-spine Phase 2): `pub(crate)` so the Phase-2 VC-gen prototype
// (`crate::vcgen_proto`) can reuse the SAME representative fixtures and the SAME
// trust-vcgen differential-oracle helpers, rather than duplicating them — the
// trust-ir-native VC set is then checked against identical ground truth.
#[cfg(test)]
pub(crate) mod tests {
    use trust_types::UnwindEdge;

    // ===================================================================
    // trust-ir-spine dimension (B): verification-verdict parity harness
    // ===================================================================
    //
    // The Phase-0 oracle above summarizes the obligations the trust-ir
    // *lowering* attaches. Dimension (B) of the parity gate
    // (`docs/TRUST_IR_SPINE.md` §"Two parity dimensions") requires more: for
    // the SAME `VerifiableFunction`, the trust-ir spine must yield the same
    // verification outcomes as the trust-types path it replaces. This harness
    // closes the loop on the *trust-types* half — it runs the production VC
    // generator (`trust_vcgen::generate_vcs`, the function the live
    // `trust_verify` MirPass consumes) over the same fixtures and asserts the
    // trust-ir obligation summary *covers* every safety VC the trust-types path
    // produces.
    //
    // It lives under `#[cfg(test)]` because `trust-vcgen` is a DEV-only
    // dependency of this crate (see Cargo.toml): the production bridge does not
    // and must not depend on the VC generator. Dependency-cycle check: cycle-
    // free — `trust-vcgen`'s normal-dependency closure contains neither
    // `trust-ir-bridge` nor `trust-router`; its only path back to this crate is
    // the *dev*-dependency on `trust-router`, which is not part of the library
    // link graph.
    use trust_types::{
        AssertMessage, BasicBlock as TrustBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand,
        Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        VerificationCondition,
    };

    use super::*;

    /// The set of `trust_vcgen` VcKinds that are *safety* (L0) obligations —
    /// the ones the trust-ir lowering must not silently drop. We restrict the
    /// parity claim to L0 safety because that is exactly the class the trust-ir
    /// `Terminator::Assert` lowering covers (overflow / bounds / div-by-zero /
    /// assertions); functional (L1) and domain (L2) obligations arrive on the
    /// trust-ir path through different machinery (contracts/specs) and are out
    /// of scope for *this* increment.
    fn is_safety_vc(vc: &VerificationCondition) -> bool {
        use trust_types::ProofLevel;
        vc.kind.proof_level() == ProofLevel::L0Safety
    }

    /// A deterministic, order-independent multiset of the `trust_vcgen`
    /// **safety** VcKinds produced for `func`, keyed by the VcKind's stable
    /// `Debug`-discriminant name (the variant name only, not its payload, so
    /// `ArithmeticOverflow { op: Add, .. }` and `ArithmeticOverflow { op: Sub, .. }`
    /// tally under the same `"ArithmeticOverflow"` key — we compare *kinds*, not
    /// operands).
    ///
    /// This is the trust-types-side observation point for dimension (B): it runs
    /// the real production VC generator the `trust_verify` pass uses, so the
    /// multiset is ground truth for "what obligations does the legacy path
    /// emit", against which we check trust-ir coverage.
    pub(crate) fn vcgen_safety_kind_multiset(func: &VerifiableFunction) -> BTreeMap<String, usize> {
        let mut multiset = BTreeMap::new();
        for vc in trust_vcgen::generate_vcs(func).iter().filter(|vc| is_safety_vc(vc)) {
            // `{:?}` on a VcKind renders `Variant { fields }` or `Variant`; the
            // leading identifier up to the first space/`{` is the discriminant.
            let dbg = format!("{:?}", vc.kind);
            let variant = dbg.split([' ', '{', '(']).next().unwrap_or(&dbg).to_string();
            *multiset.entry(variant).or_insert(0) += 1;
        }
        multiset
    }

    /// The SMT-LIB2 renderings of every `trust_vcgen` **safety** VC whose VcKind
    /// discriminant is `variant`, in emission order. This is the GROUND-TRUTH
    /// solvable formula the trust-ir-native stamp must match: the parity tests
    /// (trust-ir-spine Phase 2/3) assert the bridge-stamped safety formula equals
    /// one of these byte-for-byte. Returned as a `Vec` (not a single string)
    /// because a function may emit several VCs of the same discriminant.
    pub(crate) fn vcgen_safety_formula_smtlibs(
        func: &VerifiableFunction,
        variant: &str,
    ) -> Vec<String> {
        let mut out = Vec::new();
        for vc in trust_vcgen::generate_vcs(func).iter().filter(|vc| is_safety_vc(vc)) {
            let dbg = format!("{:?}", vc.kind);
            let this = dbg.split([' ', '{', '(']).next().unwrap_or(&dbg).to_string();
            if this == variant {
                out.push(vc.formula.to_smtlib());
            }
        }
        out
    }

    /// Map a `trust_vcgen` safety VcKind variant name to the trust-ir
    /// `ObligationKind` that must cover it on the lowered module.
    ///
    /// THE GROUND-TRUTH CORRESPONDENCE (item T1, `docs/TRUST_IR_SPINE.md`
    /// Phase-2 — now LANDED): the trust-ir taxonomy
    /// (`trust_ir::proof::ObligationKind`) carries routing-grade panic-class
    /// kinds matching `trust_verifier_api::ObligationKind`. Item T1 enriched it
    /// with `ArithmeticSafety` (overflow / neg / div / rem) and `BoundsCheck`
    /// (index/slice bounds), so the spine now PRESERVES the
    /// arithmetic-vs-bounds distinction instead of collapsing both into
    /// `PanicFreedom`. These remain panic-class obligations (they route exactly
    /// like `PanicFreedom`); the sharper kind only improves
    /// diagnostics/dispatch. The faithful sub-kind ALSO survives on the trust-ir
    /// side as the `Inst::Assert`'s `ProofAnnotation` (`InBounds` / `NoOverflow`
    /// / `DivNonZero` / `ShiftInRange`), which the Phase-1 annotation oracle
    /// above pins.
    ///
    /// Assert messages with no arithmetic/bounds classification (null/misaligned
    /// deref, resumed-after, assertion, custom, unreachable) still map to the
    /// generic `PanicFreedom`.
    ///
    /// Returns `None` for a safety VcKind that does NOT lower onto a
    /// `Terminator::Assert` and therefore is *not* expected to appear as a
    /// trust-ir panic-class obligation (e.g. `UnsupportedMir`, which the
    /// trust-ir path represents structurally rather than as a panic obligation).
    /// A `None` here is a *known, documented* coverage carve-out, recorded
    /// per-input in the tests so it cannot silently mask a real gap.
    pub(crate) fn vcgen_kind_to_trust_ir_obligation(variant: &str) -> Option<ObligationKind> {
        match variant {
            // Arithmetic panic-class safety (item T1): overflow / shift-range /
            // div-by-zero / rem-by-zero / negation / cast overflow.
            "ArithmeticOverflow" | "ShiftOverflow" | "DivisionByZero" | "RemainderByZero"
            | "NegationOverflow" | "CastOverflow" => Some(ObligationKind::ArithmeticSafety),
            // Bounds panic-class safety (item T1): array/slice index checks.
            "IndexOutOfBounds" | "SliceBoundsCheck" => Some(ObligationKind::BoundsCheck),
            // Generic panic-class checks with no arithmetic/bounds sub-kind.
            "Assertion" | "Unreachable" => Some(ObligationKind::PanicFreedom),
            // Not an assert-guarded panic obligation; out of scope for the
            // assert→panic-class coverage claim (documented carve-out).
            _ => None,
        }
    }

    /// `fn f(a: i32, b: i32) -> i32 { a + b }` lowered with an explicit
    /// MIR-style overflow check: the `Add` result is computed, then a
    /// `Terminator::Assert { msg: Overflow(Add) }` guards the success edge —
    /// exactly the shape rustc emits for checked arithmetic.
    pub(crate) fn overflow_checked_add() -> VerifiableFunction {
        VerifiableFunction {
            name: "checked_add".to_string(),
            def_path: "test::checked_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("overflowed".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Copy(Place::local(2)),
                                ),
                                span: SourceSpan::default(),
                            },
                            // Model the rustc "did it overflow" flag as a const
                            // `false` so the assert has a well-typed condition.
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn idx(s: &[i32], i: usize) -> i32 { s[i] }` lowered as rustc does the
    /// index: a `Terminator::Assert { msg: BoundsCheck }` guards `i < len`
    /// before the read. The obligation under test is produced by that assert,
    /// so the success edge just yields a constant rather than modeling the
    /// (separately-tested) slice-element read — keeping the fixture focused on
    /// the bounds *obligation*, not on slice-place lowering.
    pub(crate) fn array_index_bounds() -> VerifiableFunction {
        VerifiableFunction {
            name: "index".to_string(),
            def_path: "test::index".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Slice { elem: Box::new(Ty::i32()) },
                        name: Some("s".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("i".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("in_bounds".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::BoundsCheck,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn div(a: i32, b: i32) -> i32 { a / b }` lowered with a
    /// `Terminator::Assert { msg: DivisionByZero }` guarding the divisor,
    /// then the division on the success edge.
    pub(crate) fn division_by_zero_guard() -> VerifiableFunction {
        VerifiableFunction {
            name: "divide".to_string(),
            def_path: "test::divide".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("nonzero".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::DivisionByZero,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ----------------------------------------------------------------------
    // Broader L0-safety fixtures (trust-ir-spine Phase 2, FULL L0 coverage).
    //
    // The three above (overflow/bounds/div) exercise the dominant assert shapes.
    // The fixtures below extend the differential corpus to the rest of the L0
    // safety surface: the canonical checked-binop tuple shape (which produces an
    // `Inst::Overflow` node AND an `Overflow(op)` assert), shift-range and
    // negation asserts, null/misaligned deref asserts (the `UnsupportedMir`
    // carve-out family in vcgen), a multi-assert function, and the narrowing
    // integer casts (which are defined conversions and therefore obligation-free).
    // ----------------------------------------------------------------------

    /// The CANONICAL rustc checked-add MIR shape: `_3 = CheckedAdd(_1, _2)`
    /// producing a `(i32, bool)` tuple, then `Assert { Overflow(Add) }` on the
    /// overflow flag `_3.1`. This is the only fixture that lowers to BOTH an
    /// `Inst::Overflow` node (from the `CheckedBinaryOp`, `lower.rs:3868`) AND an
    /// `Inst::Assert` (from the terminator) — so the trust-ir-native engine emits
    /// TWO `ArithmeticSafety` VCs (one per safety-bearing node), both covering the
    /// single trust-vcgen `ArithmeticOverflow` safety VcKind.
    pub(crate) fn checked_add_overflow_tuple() -> VerifiableFunction {
        VerifiableFunction {
            name: "checked_add_tuple".to_string(),
            def_path: "test::checked_add_tuple".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A shift-amount-in-range check: `Assert { Overflow(Shl) }`. trust-vcgen
    /// emits an `ArithmeticOverflow` safety VC (shift overflow rides the same
    /// `Overflow(op)` path); the assert lowers with `ProofAnnotation::ShiftInRange`
    /// → trust-ir-native `ArithmeticSafety`.
    pub(crate) fn shift_overflow_guard() -> VerifiableFunction {
        let mut func = overflow_checked_add();
        func.name = "shift_in_range".to_string();
        func.def_path = "test::shift_in_range".to_string();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::Overflow(BinOp::Shl);
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        func
    }

    /// A negation-overflow check: `Assert { OverflowNeg }` (the `INT_MIN`
    /// negation guard). trust-vcgen emits a `NegationOverflow` safety VC; the
    /// assert lowers with `ProofAnnotation::NoOverflow` → `ArithmeticSafety`.
    pub(crate) fn negation_overflow_guard() -> VerifiableFunction {
        let mut func = overflow_checked_add();
        func.name = "neg_overflow".to_string();
        func.def_path = "test::neg_overflow".to_string();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::OverflowNeg;
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        func
    }

    /// A null-pointer-dereference check: `Assert { NullPointerDereference }`.
    /// trust-vcgen does NOT model this as a faithful safety VcKind — it emits an
    /// `UnsupportedMir` fail-closed sentinel (`generate.rs:3255`). The bridge,
    /// however, DOES lower it to an `Inst::Assert` with `ProofAnnotation::NotNull`
    /// and a `PanicFreedom` obligation, so the trust-ir-native engine emits a
    /// covering `PanicFreedom` VC. The parity oracle records `UnsupportedMir` as
    /// the documented carve-out.
    pub(crate) fn null_deref_guard() -> VerifiableFunction {
        let mut func = array_index_bounds();
        func.name = "null_deref".to_string();
        func.def_path = "test::null_deref".to_string();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::NullPointerDereference;
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        func
    }

    /// A misaligned-pointer-dereference check: `Assert { MisalignedPointerDereference }`.
    /// Like null-deref, trust-vcgen emits an `UnsupportedMir` sentinel. The bridge
    /// lowers it to an `Inst::Assert` carrying NO annotation (no faithful variant)
    /// but still a `PanicFreedom` obligation — so the trust-ir-native engine emits
    /// a (coarse) `PanicFreedom` VC. The check is never dropped.
    pub(crate) fn misaligned_deref_guard() -> VerifiableFunction {
        let mut func = array_index_bounds();
        func.name = "misaligned_deref".to_string();
        func.def_path = "test::misaligned_deref".to_string();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::MisalignedPointerDereference;
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        func
    }

    /// Two distinct safety asserts in ONE function: a bounds check (bb0) followed
    /// by a div-by-zero guard (bb1). Exercises the engine's per-node walk across
    /// multiple safety-bearing nodes — the trust-ir-native set must contain BOTH a
    /// `BoundsCheck` VC and an `ArithmeticSafety` VC.
    pub(crate) fn multiple_asserts_one_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "two_checks".to_string(),
            def_path: "test::two_checks".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Slice { elem: Box::new(Ty::i32()) },
                        name: Some("s".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("i".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("in_bounds".into()) },
                    LocalDecl { index: 4, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 5, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 6, ty: Ty::Bool, name: Some("nonzero".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::BoundsCheck,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(6)),
                            expected: true,
                            msg: AssertMessage::DivisionByZero,
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Copy(Place::local(5)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A narrowing integer cast `_0 = _1 as i8` where `_1: i32`. This is a
    /// defined, total Rust conversion: it truncates rather than overflowing, so
    /// neither trust-vcgen nor the TrustIr bridge may mint a safety obligation.
    /// The paired widening fixture checks the same policy in the lossless case.
    pub(crate) fn cast_overflow_narrowing() -> VerifiableFunction {
        VerifiableFunction {
            name: "narrow_cast".to_string(),
            def_path: "test::narrow_cast".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 8, signed: true }, name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(
                            Operand::Copy(Place::local(1)),
                            Ty::Int { width: 8, signed: true },
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Int { width: 8, signed: true },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A WIDENING integer cast `_0 = _1 as i32` where `_1: i8`. Every `i8` value
    /// fits in `i32`, so the source range is a subset of the target range —
    /// trust-vcgen's `v2_build_cast_vc` returns `None` (NO `CastOverflow` VC), and
    /// the bridge must NOT stamp any cast annotation (no false obligation). This
    /// fixture is the soundness witness for the over-flagging side: a lossless
    /// cast yields an EMPTY trust-ir-native safety VC set.
    pub(crate) fn cast_widening_lossless() -> VerifiableFunction {
        VerifiableFunction {
            name: "widen_cast".to_string(),
            def_path: "test::widen_cast".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 8, signed: true },
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32()),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A function whose entry block ends in `Terminator::Unreachable`. The bridge
    /// lowers this to an `Inst::Unreachable` node (`lower.rs:4720`), the third L0
    /// safety-bearing node kind the engine covers (→ `PanicFreedom`). Kept minimal
    /// (no asserts) so the only safety-bearing node is the unreachable terminator.
    pub(crate) fn unreachable_terminator() -> VerifiableFunction {
        VerifiableFunction {
            name: "diverge".to_string(),
            def_path: "test::diverge".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                }],
                arg_count: 0,
                return_ty: Ty::Never,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ----------------------------------------------------------------------
    // Block-def-FREE fixtures (trust-ir-spine Phase 2/3, solvable safety
    // formulas). These are the byte-exact validation targets for the stamped
    // trust-ir-native safety formula: a single-block `_0 = a OP b; return`
    // function. With one block and no guards, trust-vcgen's
    // `v2_formula_with_block_defs[_before_stmt]` finds NO relevant block
    // definitions, so the emitted `ArithmeticOverflow` / `DivisionByZero` VC
    // formula is EXACTLY the core `body` / `divisor == 0` predicate the bridge
    // reconstructs. This lets the parity test assert SMT-LIB *byte equality*
    // between the trust-ir stamp and the live trust-vcgen formula, not merely
    // logical equivalence.
    // ----------------------------------------------------------------------

    /// `fn add(a: i32, b: i32) -> i32 { a + b }` as an UNGUARDED direct
    /// `Rvalue::BinaryOp(Add)` in a single block. trust-vcgen emits one
    /// `ArithmeticOverflow{Add}` VC whose formula, with no block defs, is the
    /// pure overflow `body` (`range(a) ∧ range(b) ∧ (a+b ∉ [MIN,MAX])`). There is
    /// NO `Terminator::Assert` here, so the bridge does not stamp a safety
    /// obligation for this fixture — it is used ONLY to read trust-vcgen's exact
    /// core formula as the equality target for the GUARDED fixtures' stamps.
    pub(crate) fn direct_add_overflow_no_guard() -> VerifiableFunction {
        VerifiableFunction {
            name: "direct_add".to_string(),
            def_path: "test::direct_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn div(a: i32, b: i32) -> i32 { a / b }` as an UNGUARDED direct
    /// `Rvalue::BinaryOp(Div)` in a single block. trust-vcgen emits a
    /// `DivisionByZero` VC whose formula, with no block defs, is exactly the core
    /// `divisor == 0` (`(= b 0)`). Used as the byte-equality target for the
    /// guarded div fixture's stamp.
    pub(crate) fn direct_div_by_zero_no_guard() -> VerifiableFunction {
        let mut func = direct_add_overflow_no_guard();
        func.name = "direct_div".to_string();
        func.def_path = "test::direct_div".to_string();
        func.body.blocks[0].stmts[0] = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        func
    }

    // ----------------------------------------------------------------------
    // OPERAND-BEARING block-def-free fixtures (trust-ir-spine, remaining L0
    // safety classes: BOUNDS / SHIFT / NEGATION). Unlike the abstract-flag
    // fixtures (`array_index_bounds`, `shift_overflow_guard`,
    // `negation_overflow_guard`) — which intentionally model the rustc "did it
    // fail" boolean so the ASSERT carries a well-typed condition but trust-vcgen
    // can only recover the abstract-flag failure formula (or fail closed to
    // `UnsupportedMir`) — these fixtures carry the REAL comparison / shift /
    // negation rvalue in the block where trust-vcgen's operand-recovery helpers
    // look (`v2_find_condition_binary_operands` for bounds in the SOURCE block,
    // `v2_find_block/target_binary_operands` for shift, `v2_find_target_neg_operand`
    // for negation). With a single safety block and no other defs, trust-vcgen's
    // `v2_formula_with_block_defs` finds NO *relevant* extra conjuncts, so the
    // emitted VC formula is EXACTLY the core operand-recovered predicate the
    // bridge reconstructs — enabling SMT-LIB byte-equality (overflow-style
    // idempotent block-def/arg-range wrappers are the only documented residue,
    // handled per-case in the spine tests).

    /// `fn idx(s: &[i32], i: usize) -> i32 { s[i] }` lowered the way rustc emits a
    /// bounds check on the DIRECT-COMPARISON path: the assert condition local is
    /// defined by `_3 = Lt(i, len)` IN THE SOURCE BLOCK, and the assert is
    /// `Assert { cond: _3, expected: true, msg: BoundsCheck }`. trust-vcgen's
    /// `v2_build_bounds_assert_vc` finds that `Lt` via
    /// `v2_find_condition_binary_operands` and builds the violation predicate
    /// `Ge(i, len)` (unsigned index). `len` is modeled as an extra `usize`
    /// parameter so the comparison operands are projection-free locals (the
    /// faithful envelope), keeping the fixture block-def-free.
    pub(crate) fn bounds_direct_comparison_unsigned() -> VerifiableFunction {
        VerifiableFunction {
            name: "idx_unsigned".to_string(),
            def_path: "test::idx_unsigned".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("i".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("len".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("in_bounds".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::BoundsCheck,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Signed-index variant of [`bounds_direct_comparison_unsigned`]: the index
    /// `i: i64` is signed, so trust-vcgen's bounds violation predicate is
    /// `Or(Lt(i, 0), Ge(i, len))` (a negative index is also out of bounds). Same
    /// SOURCE-block `Lt` comparison shape.
    pub(crate) fn bounds_direct_comparison_signed() -> VerifiableFunction {
        let mut func = bounds_direct_comparison_unsigned();
        func.name = "idx_signed".to_string();
        func.def_path = "test::idx_signed".to_string();
        func.body.locals[1].ty = Ty::Int { width: 64, signed: true };
        func.body.locals[2].ty = Ty::Int { width: 64, signed: true };
        func
    }

    /// `fn shl(x: i32, n: u32) -> i32 { x << n }` lowered with the shift computed
    /// in the SOURCE block (`_0 = Shl(x, n)`) guarded by `Assert { Overflow(Shl) }`.
    /// trust-vcgen's `v2_build_assert_overflow_vc` recovers the `Shl` operands via
    /// `v2_find_block_binary_operands` and builds the shift-range violation
    /// `Ge(n, 32)` (unsigned shift amount, shifted-value width 32). Block-def-free
    /// (the only def is the shift itself, which the shift VC does not re-conjoin).
    pub(crate) fn shift_direct_unsigned_amount() -> VerifiableFunction {
        VerifiableFunction {
            name: "shl_unsigned".to_string(),
            def_path: "test::shl_unsigned".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 32, signed: false },
                        name: Some("n".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("in_range".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Shl),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Signed-shift-amount variant: `n: i32`, so trust-vcgen's invalid-shift
    /// predicate is `Or(Lt(n, 0), Ge(n, 32))`.
    pub(crate) fn shift_direct_signed_amount() -> VerifiableFunction {
        let mut func = shift_direct_unsigned_amount();
        func.name = "shl_signed".to_string();
        func.def_path = "test::shl_signed".to_string();
        func.body.locals[2].ty = Ty::Int { width: 32, signed: true };
        func
    }

    /// `fn neg(x: i32) -> i32 { -x }` lowered with the negation in the TARGET
    /// block (`_0 = Neg(x)`) guarded by `Assert { OverflowNeg }`. trust-vcgen's
    /// `v2_build_assert_negation_vc` finds the `Neg` operand via
    /// `v2_find_target_neg_operand`, confirms it is signed, and emits the
    /// ABSTRACT-FLAG failure formula `Not(cond)` (it does NOT use the `Eq(x, MIN)`
    /// raw form — that belongs to the bare-`Rvalue::UnaryOp` path, not the assert
    /// path). The fixture's cond is a plain boolean flag, matching that shape.
    pub(crate) fn negation_with_target_neg() -> VerifiableFunction {
        VerifiableFunction {
            name: "neg_target".to_string(),
            def_path: "test::neg_target".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("overflowed".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(2)),
                            expected: false,
                            msg: AssertMessage::OverflowNeg,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::UnaryOp(
                                trust_types::UnOp::Neg,
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn mul(a: i32, b: i32) -> i32 { a * b }` lowered with `_0 = Mul(a, b)` in
    /// the SOURCE block guarded by `Assert { Overflow(Mul) }`. trust-vcgen routes
    /// signed/unsigned integer multiply through the BITVECTOR overflow encoding
    /// (`v2_signed_bv_overflow_formula`), NOT the scalar Int range envelope — so
    /// the bridge fails closed for mul (a scalar Int reconstruction would not
    /// match the BV formula, risking an unsound mismatch). This fixture witnesses
    /// that mul stays a documented fail-closed gap.
    pub(crate) fn mul_overflow_guard() -> VerifiableFunction {
        VerifiableFunction {
            name: "mul_checked".to_string(),
            def_path: "test::mul_checked".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("overflowed".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Copy(Place::local(2)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Mul),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // Item T1 (LANDED): the per-assert lowering now classifies each MIR
    // `Terminator::Assert` by its `AssertMessage` into a routing-grade
    // panic-class `ObligationKind` — `ArithmeticSafety` (overflow/neg/div/rem),
    // `BoundsCheck` (index), or generic `PanicFreedom` (everything else) — via
    // `lower::assert_obligation_kind`. The function-level AGGREGATE obligation
    // (lower.rs ~3054) stays `PanicFreedom`. All three are panic-class and route
    // identically; the sharper kind preserves the arithmetic-vs-bounds
    // distinction the trust-types/router path makes. These tests assert that
    // faithful behavior — they are the trust-ir ground truth the oracle compares
    // against.
    //
    // Per-assert site count: each fixture has exactly one `Terminator::Assert`,
    // so it carries exactly 1 per-site obligation of the FAITHFUL kind and NO
    // function-level `PanicFreedom` aggregate. The lowering emits that aggregate
    // ONLY for diverging-panic `Call` terminators (panic!/assert!/unreachable!),
    // NOT for `Assert` sites (overflow/bounds/div): surfacing the strictly-weaker
    // whole-function transport CHC for an Assert would regress provably-safe
    // arithmetic/bounds to INCONCLUSIVE (the w01/w13/w16/w19 completeness fix).
    const EXPECTED_FUNCTION_LEVEL_PANIC_FREEDOM: usize = 0;

    #[test]
    fn overflow_check_surfaces_arithmetic_safety_obligation() {
        let summary = lowered_obligation_summary(&overflow_checked_add())
            .expect("checked-add overflow function should lower");
        // Item T1 (LANDED): the per-assert obligation is now the FAITHFUL
        // `ArithmeticSafety` kind, not the coarse `PanicFreedom`.
        assert_eq!(
            obligation_count(&summary, ObligationKind::ArithmeticSafety),
            1,
            "overflow assert should surface a faithful per-site ArithmeticSafety: {summary:?}"
        );
        // The function-level aggregate stays `PanicFreedom` (always exactly 1).
        assert_eq!(
            obligation_count(&summary, ObligationKind::PanicFreedom),
            EXPECTED_FUNCTION_LEVEL_PANIC_FREEDOM,
            "the function-level aggregate stays PanicFreedom: {summary:?}"
        );
        // The assert *annotation* is also faithful: an overflow assert carries
        // `NoOverflow` (see `overflow_assert_carries_no_overflow_annotation`).
    }

    #[test]
    fn array_index_bounds_surfaces_bounds_check_not_memory_safety() {
        let summary = lowered_obligation_summary(&array_index_bounds())
            .expect("array-index bounds function should lower");
        // Item T1 (LANDED): a bounds assert now surfaces the faithful
        // `BoundsCheck` panic-class kind (NOT `MemorySafety`, which routes to
        // borrow-check and would mis-categorize a panic-freedom bounds check).
        assert_eq!(
            obligation_count(&summary, ObligationKind::BoundsCheck),
            1,
            "bounds assert should surface a faithful per-site BoundsCheck: {summary:?}"
        );
        // The function-level aggregate stays `PanicFreedom`.
        assert_eq!(
            obligation_count(&summary, ObligationKind::PanicFreedom),
            EXPECTED_FUNCTION_LEVEL_PANIC_FREEDOM,
            "the function-level aggregate stays PanicFreedom: {summary:?}"
        );
        // It is `BoundsCheck`, NOT `MemorySafety`: `MemorySafety` routes to
        // borrow-check (`native_request.rs` → `BorrowCheck`), which would
        // mis-categorize a panic-freedom bounds check. `BoundsCheck` routes like
        // `PanicFreedom`, preserving correct dispatch.
        assert_eq!(
            obligation_count(&summary, ObligationKind::MemorySafety),
            0,
            "a bounds check is panic-class, not a MemorySafety (borrow) obligation: {summary:?}"
        );
        // The assert *annotation* is also faithful: a bounds assert carries
        // `InBounds` (see `bounds_assert_carries_in_bounds_annotation`).
    }

    #[test]
    fn division_by_zero_surfaces_arithmetic_safety_obligation() {
        let summary = lowered_obligation_summary(&division_by_zero_guard())
            .expect("division-by-zero function should lower");
        // Item T1 (LANDED): div-by-zero is arithmetic panic-class, so the
        // per-assert obligation is the faithful `ArithmeticSafety`.
        assert_eq!(
            obligation_count(&summary, ObligationKind::ArithmeticSafety),
            1,
            "div-by-zero assert should surface a faithful per-site ArithmeticSafety: {summary:?}"
        );
        // The function-level aggregate stays `PanicFreedom`.
        assert_eq!(
            obligation_count(&summary, ObligationKind::PanicFreedom),
            EXPECTED_FUNCTION_LEVEL_PANIC_FREEDOM,
            "the function-level aggregate stays PanicFreedom: {summary:?}"
        );
        // The assert *annotation* is also faithful: this path attaches
        // `DivNonZero` (see
        // `division_by_zero_assert_carries_div_non_zero_annotation`).
    }

    #[test]
    fn summary_keys_are_canonical_obligation_kind_names() {
        let summary =
            lowered_obligation_summary(&overflow_checked_add()).expect("function should lower");
        // Item T1 (LANDED): the overflow fixture produces the faithful per-site
        // `arithmetic_safety` kind, keyed by its canonical Display name. The
        // function-level `panic_freedom` aggregate is NOT emitted for `Assert`
        // sites (only for diverging-panic `Call`s), so it is absent here.
        assert!(
            summary.contains_key(&ObligationKind::ArithmeticSafety.to_string()),
            "summary must key on the canonical kind name `arithmetic_safety`: {summary:?}"
        );
        // The only obligation kind this safety-only Assert-bearing input produces
        // is the faithful per-site `arithmetic_safety`: no aggregate `PanicFreedom`
        // (Assert sites don't get it), and no contracts means no Pre/Postconditions.
        assert_eq!(
            summary.keys().collect::<Vec<_>>(),
            vec![&ObligationKind::ArithmeticSafety.to_string()],
            "safety-only overflow input should carry ONLY the faithful per-site \
             ArithmeticSafety obligation (no aggregate PanicFreedom for Assert sites): {summary:?}"
        );
    }

    #[test]
    fn obligation_free_function_has_empty_summary() {
        // A function with no asserts and no contracts surfaces no obligations.
        let noop = VerifiableFunction {
            name: "noop".to_string(),
            def_path: "test::noop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let summary = lowered_obligation_summary(&noop).expect("noop should lower");
        assert!(summary.is_empty(), "no asserts/contracts means no obligations: {summary:?}");
    }

    // --- trust-ir-spine Phase 1: faithful assert ProofAnnotations ---------
    //
    // The lowering used to attach a blanket `ProofAnnotation::NoOverflow` to
    // *every* `Inst::Assert`, regardless of the `AssertMessage` — so a
    // division-by-zero, a bounds check, and an overflow assert were all
    // mislabeled `NoOverflow`. Phase 1 replaces that with a faithful
    // `AssertMessage -> ProofAnnotation` match (and *no* annotation when no
    // variant matches). These tests pin the corrected behavior; they use the
    // same fixtures as the obligation tests above.

    #[test]
    fn division_by_zero_assert_carries_div_non_zero_annotation() {
        let summary = lowered_assert_annotation_summary(&division_by_zero_guard())
            .expect("division-by-zero function should lower");
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::DivNonZero),
            1,
            "div-by-zero assert must carry the faithful `DivNonZero`: {summary:?}"
        );
        // The bug was the blanket `NoOverflow`; it must NOT appear here.
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::NoOverflow),
            0,
            "div-by-zero assert must NOT carry the old blanket `NoOverflow`: {summary:?}"
        );
    }

    #[test]
    fn bounds_assert_carries_in_bounds_annotation() {
        let summary = lowered_assert_annotation_summary(&array_index_bounds())
            .expect("array-index bounds function should lower");
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::InBounds),
            1,
            "bounds assert must carry the faithful `InBounds`: {summary:?}"
        );
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::NoOverflow),
            0,
            "bounds assert must NOT carry the old blanket `NoOverflow`: {summary:?}"
        );
    }

    #[test]
    fn overflow_assert_carries_no_overflow_annotation() {
        // An `Overflow(Add)` assert genuinely *is* a no-overflow check, so here
        // `NoOverflow` is the correct, faithful annotation (not the bug).
        let summary = lowered_assert_annotation_summary(&overflow_checked_add())
            .expect("checked-add overflow function should lower");
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::NoOverflow),
            1,
            "overflow assert must carry `NoOverflow`: {summary:?}"
        );
        // Sanity: it must not be mislabeled as a memory/division check.
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::InBounds),
            0,
            "overflow assert must not carry a memory-safety annotation: {summary:?}"
        );
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::DivNonZero),
            0,
            "overflow assert must not carry a division annotation: {summary:?}"
        );
    }

    #[test]
    fn shift_overflow_assert_carries_shift_in_range_annotation() {
        // `Overflow(Shl)` is a "shift amount in range" check, not no-overflow.
        let mut func = overflow_checked_add();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::Overflow(BinOp::Shl);
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        let summary =
            lowered_assert_annotation_summary(&func).expect("shift-overflow function should lower");
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::ShiftInRange),
            1,
            "shift-overflow assert must carry `ShiftInRange`: {summary:?}"
        );
        assert_eq!(
            assert_annotation_count(&summary, &ProofAnnotation::NoOverflow),
            0,
            "shift-overflow assert must NOT be labeled `NoOverflow`: {summary:?}"
        );
    }

    #[test]
    fn unmatched_assert_message_carries_no_annotation() {
        // A `Custom` message has no semantically-matching annotation, so the
        // lowering must attach *none* rather than a wrong one. The PanicFreedom
        // obligation still covers the check.
        let mut func = overflow_checked_add();
        if let Terminator::Assert { msg, .. } = &mut func.body.blocks[0].terminator {
            *msg = AssertMessage::Custom("hand-written assert".to_string());
        } else {
            panic!("fixture block 0 must end in an Assert terminator");
        }
        let annotations =
            lowered_assert_annotation_summary(&func).expect("custom-assert function should lower");
        assert!(
            annotations.is_empty(),
            "a Custom assert message must carry no proof annotation, not a wrong one: {annotations:?}"
        );
        // The obligation is still emitted — the check is not lost.
        let obligations =
            lowered_obligation_summary(&func).expect("custom-assert function should lower");
        // A `Custom` message has no arithmetic/bounds classification, so its
        // per-site obligation is the generic `PanicFreedom` (item T1) — which,
        // together with the function-level `PanicFreedom` aggregate, is 2.
        assert_eq!(
            obligation_count(&obligations, ObligationKind::PanicFreedom),
            1 + EXPECTED_FUNCTION_LEVEL_PANIC_FREEDOM,
            "custom assert must still surface its PanicFreedom obligation: {obligations:?}"
        );
        // It produces no faithful arithmetic/bounds kind (it is unclassified).
        assert_eq!(
            obligation_count(&obligations, ObligationKind::ArithmeticSafety),
            0,
            "an unclassified Custom assert is not arithmetic: {obligations:?}"
        );
        assert_eq!(
            obligation_count(&obligations, ObligationKind::BoundsCheck),
            0,
            "an unclassified Custom assert is not a bounds check: {obligations:?}"
        );
    }

    // ===================================================================
    // Dimension (B) parity assertions — trust-ir covers trust-vcgen safety VCs
    // ===================================================================
    //
    // GROUND TRUTH (empirically recorded from `trust_vcgen::generate_vcs` on
    // these exact fixtures; see the parity tests' inline assertions). After
    // item T1 (LANDED) each panic-class VcKind maps to its FAITHFUL trust-ir
    // panic-class obligation, plus the function-level `panic_freedom` aggregate:
    //
    //   fixture    trust-vcgen safety VcKinds            trust-ir obligations
    //   --------   ----------------------------------   --------------------------
    //   overflow   ArithmeticOverflow, UnsupportedMir   arithmetic_safety + panic_freedom
    //   bounds     IndexOutOfBounds                     bounds_check + panic_freedom
    //   div        ArithmeticOverflow, DivisionByZero   arithmetic_safety + panic_freedom
    //
    // Interpretation against item T1 (the taxonomy enrichment — now landed):
    //   * Each assert-guarded panic-class VcKind maps to its faithful trust-ir
    //     panic-class kind: ArithmeticOverflow/DivisionByZero → `ArithmeticSafety`,
    //     IndexOutOfBounds → `BoundsCheck`. All are panic-class and route exactly
    //     like `PanicFreedom`; the sharper kind preserves the arithmetic-vs-bounds
    //     distinction. The faithful sub-kind ALSO survives as the assert's
    //     ProofAnnotation (pinned by the Phase-1 annotation tests above).
    //   * `UnsupportedMir` is a documented carve-out: it is a fail-closed
    //     "could-not-model" sentinel (here a `RecognizedSafetyAssertProofGap`),
    //     NOT a panic obligation the trust-ir path must mirror. It maps to `None`
    //     in `vcgen_kind_to_trust_ir_obligation` and is asserted explicitly so it
    //     cannot silently hide a real gap.

    /// Core dimension-(B) check: for `func`, every `trust_vcgen` **safety**
    /// VcKind that the documented T1 mapping says should appear as a trust-ir
    /// obligation IS present (count ≥ 1) in the lowered module's obligation
    /// summary; and every safety VcKind that maps to `None` is recorded in
    /// `carve_outs` (so an unexpected unmapped kind fails the test rather than
    /// being silently ignored).
    ///
    /// Returns the observed trust-vcgen safety multiset so callers can pin the
    /// exact ground-truth shape per input.
    fn assert_trust_ir_covers_vcgen_safety(
        func: &VerifiableFunction,
        expected_carve_outs: &[&str],
    ) -> BTreeMap<String, usize> {
        let vcgen = vcgen_safety_kind_multiset(func);
        let ir_summary = lowered_obligation_summary(func)
            .expect("representative fixture must lower to trust-ir");

        for (variant, count) in &vcgen {
            assert!(*count >= 1);
            match vcgen_kind_to_trust_ir_obligation(variant) {
                Some(ob) => {
                    // The T1 faithful mapping: this safety VcKind must be covered
                    // by its corresponding trust-ir panic-class obligation — and at
                    // the EXACT count, not merely present. A `>= 1` presence check
                    // lets a MISCLASSIFIED obligation kind slip through (e.g. the
                    // right kind appears but with the wrong multiplicity, hiding a
                    // dropped or duplicated obligation). Asserting the exact count
                    // pins the per-kind multiset, so each trust-vcgen safety VcKind
                    // matches the trust-ir obligation count exactly.
                    let ob_name = ob.to_string();
                    assert_eq!(
                        obligation_count(&ir_summary, ob),
                        *count,
                        "trust-vcgen emitted safety VcKind `{variant}` (×{count}) but the \
                         trust-ir lowering's covering `{ob_name}` obligation count does not \
                         match exactly: vcgen={vcgen:?} ir={ir_summary:?}"
                    );
                }
                None => {
                    // A safety VcKind that intentionally does NOT lower to a
                    // trust-ir panic obligation must be in the documented
                    // carve-out list — otherwise it is an unaccounted gap.
                    assert!(
                        expected_carve_outs.contains(&variant.as_str()),
                        "trust-vcgen safety VcKind `{variant}` has no trust-ir obligation \
                         mapping and is NOT in the documented carve-outs {expected_carve_outs:?}; \
                         this is an unaccounted parity gap, not an expected-coarse case: \
                         vcgen={vcgen:?} ir={ir_summary:?}"
                    );
                }
            }
        }
        vcgen
    }

    #[test]
    fn overflow_vcgen_safety_covered_by_trust_ir_arithmetic_safety() {
        let vcgen = assert_trust_ir_covers_vcgen_safety(
            &overflow_checked_add(),
            // UnsupportedMir is a fail-closed proof-gap sentinel, not a dropped
            // panic obligation — see ground-truth table above.
            &["UnsupportedMir"],
        );
        // Ground truth: this fixture surfaces an ArithmeticOverflow VC...
        assert_eq!(
            vcgen.get("ArithmeticOverflow").copied(),
            Some(1),
            "overflow fixture must surface exactly one ArithmeticOverflow safety VC: {vcgen:?}"
        );
        // ...which the T1 faithful mapping covers as trust-ir ArithmeticSafety.
        assert_eq!(
            vcgen_kind_to_trust_ir_obligation("ArithmeticOverflow"),
            Some(ObligationKind::ArithmeticSafety)
        );
    }

    #[test]
    fn bounds_vcgen_safety_covered_by_trust_ir_bounds_check() {
        let vcgen = assert_trust_ir_covers_vcgen_safety(&array_index_bounds(), &[]);
        // Ground truth: a single IndexOutOfBounds safety VC, no carve-outs.
        assert_eq!(
            vcgen.get("IndexOutOfBounds").copied(),
            Some(1),
            "bounds fixture must surface exactly one IndexOutOfBounds safety VC: {vcgen:?}"
        );
        assert_eq!(
            vcgen.keys().collect::<Vec<_>>(),
            vec!["IndexOutOfBounds"],
            "bounds fixture should surface ONLY the IndexOutOfBounds safety VC: {vcgen:?}"
        );
        // T1 faithful mapping: bounds-check → BoundsCheck (NOT MemorySafety,
        // which routes to borrow-check and would mis-categorize a panic-freedom
        // bounds check — see
        // `array_index_bounds_surfaces_bounds_check_not_memory_safety`).
        assert_eq!(
            vcgen_kind_to_trust_ir_obligation("IndexOutOfBounds"),
            Some(ObligationKind::BoundsCheck)
        );
    }

    #[test]
    fn div_vcgen_safety_covered_by_trust_ir_arithmetic_safety() {
        let vcgen = assert_trust_ir_covers_vcgen_safety(&division_by_zero_guard(), &[]);
        // Ground truth: the divide fixture surfaces BOTH the division-by-zero
        // check AND the signed-div `INT_MIN / -1` overflow check; both are
        // arithmetic panic-class and both map to trust-ir `ArithmeticSafety`.
        assert_eq!(
            vcgen.get("DivisionByZero").copied(),
            Some(1),
            "div fixture must surface the DivisionByZero safety VC: {vcgen:?}"
        );
        assert_eq!(
            vcgen.get("ArithmeticOverflow").copied(),
            Some(1),
            "div fixture must surface the signed-div overflow safety VC: {vcgen:?}"
        );
        // Both arithmetic VcKinds map to the faithful `ArithmeticSafety` kind.
        assert_eq!(
            vcgen_kind_to_trust_ir_obligation("DivisionByZero"),
            Some(ObligationKind::ArithmeticSafety)
        );
        assert_eq!(
            vcgen_kind_to_trust_ir_obligation("ArithmeticOverflow"),
            Some(ObligationKind::ArithmeticSafety)
        );
    }

    // ===================================================================
    // Dimension (B), STRENGTHENED: trust-ir carries a SOLVABLE FORMULA, not
    // just a covering obligation KIND (trust-ir-spine Phase 2/3).
    // ===================================================================
    //
    // The coverage tests above prove the trust-ir lowering surfaces a covering
    // obligation of the right KIND for every trust-vcgen safety VcKind. That is
    // necessary but NOT sufficient to make trust-ir the verdict source of record:
    // a verdict needs a SOLVABLE formula. These tests close that gap — they assert
    // the stamped `ProofFormula` on the lowered obligation carries a solvable SMT
    // formula equivalent to trust-vcgen's, for the cases the lowering reconstructs
    // (div-by-zero byte-exact; overflow byte-exact to trust-vcgen's innermost
    // `body`). The remaining safety classes (bounds, mul/shift overflow) carry the
    // obligation KIND but fail closed on the formula (documented gap) — asserted
    // here too so the gap cannot silently become a fabricated formula.

    /// The SMT-LIB of the single stamped `ArithmeticSafety` obligation in the
    /// lowered module (via the production module reader), or a panic.
    fn lowered_arith_safety_smtlib(func: &VerifiableFunction) -> String {
        let module = lower_to_trust_ir(func).expect("fixture must lower");
        let solvable: Vec<_> = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .filter(|o| o.kind == ObligationKind::ArithmeticSafety && o.smtlib.is_some())
            .collect();
        assert_eq!(
            solvable.len(),
            1,
            "expected exactly one solvable ArithmeticSafety obligation: {solvable:?}"
        );
        solvable[0].smtlib.clone().unwrap()
    }

    #[test]
    fn div_by_zero_obligation_carries_solvable_formula_matching_vcgen() {
        // The lowered div fixture's ArithmeticSafety obligation carries the
        // solvable `(= b 0)` — byte-equal to trust-vcgen's core div-by-zero
        // formula (read from the block-def-free direct-div fixture).
        let stamped = lowered_arith_safety_smtlib(&division_by_zero_guard());
        let vcgen = vcgen_safety_formula_smtlibs(&direct_div_by_zero_no_guard(), "DivisionByZero");
        assert_eq!(vcgen.len(), 1);
        assert_eq!(stamped, vcgen[0], "div obligation formula must match trust-vcgen core");
        assert_eq!(stamped, "(= b 0)");
    }

    #[test]
    fn overflow_obligation_carries_solvable_formula_matching_vcgen_body() {
        // The lowered overflow fixture's ArithmeticSafety obligation carries the
        // solvable overflow core `body`. trust-vcgen's emitted formula is that
        // exact `body` under idempotent arg-range wrappers, so the stamp is the
        // innermost `body` of trust-vcgen's formula (logically equivalent to the
        // full formula — identical models, identical verdict).
        let stamped = lowered_arith_safety_smtlib(&overflow_checked_add());
        assert_eq!(
            stamped,
            "(and (and (<= (- 2147483648) a) (<= a 2147483647)) \
             (and (<= (- 2147483648) b) (<= b 2147483647)) \
             (or (< (+ a b) (- 2147483648)) (> (+ a b) 2147483647)))",
            "overflow obligation must carry the solvable out-of-range core body"
        );
    }

    #[test]
    fn abstract_flag_bounds_obligation_fails_closed_not_fabricated() {
        // SOUNDNESS-CRITICAL: the ABSTRACT-FLAG bounds fixture (`array_index_bounds`,
        // whose cond is a plain `Bool(true)` with no defining `idx < len`
        // comparison) has a covering obligation KIND but NO solvable formula. On
        // this shape trust-vcgen itself emits only a flag-failure formula with no
        // operand-level meaning, so the bridge must fail closed — never a
        // fabricated bounds predicate. (The DIRECT-COMPARISON shape IS reconstructed
        // — see `bounds_direct_*_obligation_matches_vcgen_violation_core`.)
        let module = lower_to_trust_ir(&array_index_bounds()).expect("lowers");
        let bounds: Vec<_> = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .filter(|o| o.kind == ObligationKind::BoundsCheck)
            .collect();
        assert_eq!(bounds.len(), 1, "bounds obligation present (kind covered)");
        assert!(
            bounds[0].smtlib.is_none(),
            "abstract-flag bounds obligation must fail closed on the formula: {:?}",
            bounds[0]
        );
    }

    // ===================================================================
    // REMAINING L0 SAFETY CLASSES: solvable-formula parity (this increment).
    //
    // Bounds (direct-comparison) and shift (Shl/Shr) now carry a SOLVABLE,
    // SMT-bearing formula on the spine, validated against the LIVE trust-vcgen
    // formula. Negation (assert path) and multiply stay FAIL-CLOSED with the
    // documented reason — asserted here so the gap cannot silently become a
    // fabricated formula (which would be worse than none).
    //
    // EQUIVALENCE STANDARD (identical to the overflow path): the stamp equals the
    // INNERMOST violation subterm of trust-vcgen's emitted formula byte-for-byte.
    // trust-vcgen conjoins ONE outer block-definition that BINDS A FRESH VARIABLE
    // (the boolean comparison result `in_bounds` for bounds; the shifted result
    // local `_0` for shift) which appears NOWHERE in the violation core — so
    // `∃fresh. (fresh == def) ∧ violation` is satisfiable iff `violation` is:
    // identical models over the real variables, identical UNSAT-of-violation
    // verdict. We assert (i) the stamp byte-equals that innermost violation, and
    // (ii) trust-vcgen's full formula is exactly `And([fresh_def, stamp])`.
    // ===================================================================

    /// The single stamped solvable obligation of `kind` in the lowered module, as
    /// SMT-LIB, via the production module reader (no trust-vcgen). Panics unless
    /// exactly one such obligation carries a formula.
    fn stamped_smtlib(func: &VerifiableFunction, kind: ObligationKind) -> String {
        let module = lower_to_trust_ir(func).expect("fixture must lower");
        let solvable: Vec<_> = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .filter(|o| o.kind == kind && o.smtlib.is_some())
            .collect();
        assert_eq!(
            solvable.len(),
            1,
            "expected exactly one solvable {kind} obligation: {solvable:?}"
        );
        assert_eq!(solvable[0].sort.as_deref(), Some("Bool"));
        assert!(
            solvable[0].formula_json.is_some(),
            "machine-readable JSON payload must be present"
        );
        solvable[0].smtlib.clone().unwrap()
    }

    /// trust-vcgen's full emitted formula for the single safety VC of discriminant
    /// `variant` on `func`, as a `trust_types::Formula` AST (panics unless exactly
    /// one). Used to prove the full-formula = `And([fresh_def, stamp])` relation.
    fn vcgen_single_safety_formula(
        func: &VerifiableFunction,
        variant: &str,
    ) -> trust_types::Formula {
        let mut found = Vec::new();
        for vc in trust_vcgen::generate_vcs(func) {
            use trust_types::ProofLevel;
            if vc.kind.proof_level() != ProofLevel::L0Safety {
                continue;
            }
            let dbg = format!("{:?}", vc.kind);
            let this = dbg.split([' ', '{', '(']).next().unwrap_or(&dbg).to_string();
            if this == variant {
                found.push(vc.formula.clone());
            }
        }
        assert_eq!(found.len(), 1, "expected exactly one {variant} safety VC: {found:?}");
        found.pop().unwrap()
    }

    /// Assert trust-vcgen's full formula is exactly `And([fresh_def, stamp_ast])`:
    /// a two-conjunct top-level `And` whose LAST conjunct is the stamped violation
    /// core (byte-equal) and whose first conjunct is the fresh-var block definition.
    fn assert_full_formula_is_fresh_def_then_core(
        full: &trust_types::Formula,
        stamp_ast: &trust_types::Formula,
    ) {
        use trust_types::Formula;
        match full {
            Formula::And(conjuncts) => {
                assert_eq!(
                    conjuncts.len(),
                    2,
                    "vcgen full formula must be And([fresh_def, core]): {full:?}"
                );
                assert_eq!(
                    &conjuncts[1], stamp_ast,
                    "the LAST conjunct of vcgen's formula must byte-equal the stamped core"
                );
                // The first conjunct binds a fresh var (an `Eq(Var, ...)`) — it
                // introduces a variable not present in the core, so it cannot change
                // the core's satisfiability over the real variables.
                assert!(
                    matches!(conjuncts[0], Formula::Eq(_, _)),
                    "the first conjunct must be the fresh-var binding `Eq(fresh, def)`: {:?}",
                    conjuncts[0]
                );
            }
            other => panic!("vcgen formula must be a top-level And: {other:?}"),
        }
    }

    /// Deserialize the stamped JSON payload back into a `trust_types::Formula`.
    fn stamped_formula_ast(
        func: &VerifiableFunction,
        kind: ObligationKind,
    ) -> trust_types::Formula {
        let module = lower_to_trust_ir(func).expect("fixture must lower");
        let json = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .find(|o| o.kind == kind && o.formula_json.is_some())
            .and_then(|o| o.formula_json.clone())
            .expect("a solvable obligation with a JSON payload");
        let value: serde_json::Value = serde_json::from_str(&json).expect("payload is JSON");
        serde_json::from_value(value["formula"].clone()).expect("formula field deserializes")
    }

    #[test]
    fn bounds_direct_unsigned_obligation_matches_vcgen_violation_core() {
        // Unsigned index direct-comparison: stamp = `(>= i len)`, the innermost
        // violation core of trust-vcgen's `And([(= in_bounds (< i len)), (>= i len)])`.
        let stamped =
            stamped_smtlib(&bounds_direct_comparison_unsigned(), ObligationKind::BoundsCheck);
        assert_eq!(stamped, "(>= i len)", "unsigned bounds stamp must be the Ge(i,len) violation");

        let stamp_ast =
            stamped_formula_ast(&bounds_direct_comparison_unsigned(), ObligationKind::BoundsCheck);
        let full =
            vcgen_single_safety_formula(&bounds_direct_comparison_unsigned(), "IndexOutOfBounds");
        // The stamp byte-equals vcgen's innermost violation, and the full formula
        // is exactly the fresh-`in_bounds`-binding wrapper around it (equisatisfiable).
        assert_eq!(stamped, "(>= i len)");
        assert_full_formula_is_fresh_def_then_core(&full, &stamp_ast);
    }

    #[test]
    fn bounds_direct_signed_obligation_matches_vcgen_violation_core() {
        // Signed index: stamp = `(or (< i 0) (>= i len))` (negative index is also
        // out of bounds), the innermost violation of trust-vcgen's formula.
        let stamped =
            stamped_smtlib(&bounds_direct_comparison_signed(), ObligationKind::BoundsCheck);
        assert_eq!(
            stamped, "(or (< i 0) (>= i len))",
            "signed bounds stamp must include the < 0 disjunct"
        );

        let stamp_ast =
            stamped_formula_ast(&bounds_direct_comparison_signed(), ObligationKind::BoundsCheck);
        let full =
            vcgen_single_safety_formula(&bounds_direct_comparison_signed(), "IndexOutOfBounds");
        assert_full_formula_is_fresh_def_then_core(&full, &stamp_ast);
    }

    #[test]
    fn shift_unsigned_obligation_matches_vcgen_formula_byte_exact() {
        // Unsigned shift amount: stamp = `And([range(n), Ge(n, 32)])`, BYTE-EQUAL
        // to trust-vcgen's ASSERT-path shift VC formula (the shift VC is built with
        // NO block defs of its own, so it is the bare core — full byte equality,
        // not just innermost).
        let stamped =
            stamped_smtlib(&shift_direct_unsigned_amount(), ObligationKind::ArithmeticSafety);
        assert_eq!(
            stamped, "(and (and (<= 0 n) (<= n 4294967295)) (>= n 32))",
            "unsigned shift stamp must be range(n) ∧ Ge(n, bitwidth)"
        );
        // trust-vcgen emits TWO ShiftOverflow VCs (one from the direct Shl rvalue
        // statement, wrapping a BV result def; one from the assert). The ASSERT VC
        // is the bare core, byte-equal to our stamp.
        let assert_vc_smt =
            vcgen_safety_formula_smtlibs(&shift_direct_unsigned_amount(), "ShiftOverflow")
                .into_iter()
                .find(|s| s == &stamped)
                .expect("one trust-vcgen ShiftOverflow VC must byte-equal the stamp");
        assert_eq!(stamped, assert_vc_smt);
    }

    #[test]
    fn shift_signed_obligation_matches_vcgen_formula_byte_exact() {
        // Signed shift amount: stamp = `And([range(n), Or([Lt(n,0), Ge(n,32)])])`,
        // byte-equal to trust-vcgen's assert-path signed-shift VC.
        let stamped =
            stamped_smtlib(&shift_direct_signed_amount(), ObligationKind::ArithmeticSafety);
        assert_eq!(
            stamped, "(and (and (<= (- 2147483648) n) (<= n 2147483647)) (or (< n 0) (>= n 32)))",
            "signed shift stamp must include the < 0 disjunct"
        );
        let assert_vc_smt =
            vcgen_safety_formula_smtlibs(&shift_direct_signed_amount(), "ShiftOverflow")
                .into_iter()
                .find(|s| s == &stamped)
                .expect("one trust-vcgen ShiftOverflow VC must byte-equal the stamp");
        assert_eq!(stamped, assert_vc_smt);
    }

    #[test]
    fn negation_assert_obligation_stamps_abstract_flag_core() {
        // The negation ASSERT path in trust-vcgen (`v2_build_assert_negation_vc`)
        // emits `v2_formula_with_block_defs(block, v2_assert_failure_formula(cond,
        // false))`. The CORE (innermost `body`) is the bare cond var
        // (`operand_to_formula(cond)` = `Var(cond_name, Bool)`) — for this fixture's
        // const-false abstract flag `_2 = false; assert(_2)`, that is
        // `Var("overflowed", Bool)`. The bridge now stamps exactly that faithful
        // core (the same `v2_assert_failure_formula` value trust-vcgen builds), so
        // negation is no longer a fail-closed gap — it carries the solvable
        // abstract-flag core. (The cond-binding wrapper, needed for byte-equality to
        // trust-vcgen's FULL formula, is reconstructed by the verdict-flip's
        // `reconstruct_full_safety_formula_candidates`, not the obligation stamp.)
        let module = lower_to_trust_ir(&negation_with_target_neg()).expect("lowers");
        let arith: Vec<_> = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .filter(|o| o.kind == ObligationKind::ArithmeticSafety)
            .collect();
        assert_eq!(arith.len(), 1, "negation surfaces a covering ArithmeticSafety obligation");
        assert_eq!(
            arith[0].smtlib.as_deref(),
            Some("overflowed"),
            "negation assert obligation must stamp the abstract-flag cond-var core: {:?}",
            arith[0]
        );
        assert_eq!(arith[0].sort.as_deref(), Some("Bool"));
        assert!(arith[0].formula_json.is_some(), "the stamped core must carry a JSON payload");
    }

    #[test]
    fn mul_overflow_obligation_stamps_bitvector_core() {
        // trust-ir-spine: integer MUL overflow is now the spine's verdict-formula
        // source for the BARE operand case. trust-vcgen routes mul through the
        // fixed-width BITVECTOR encoding (`v2_signed_bv_overflow_formula`: the
        // width-doubling sign-extended product check over fresh BV operand vars);
        // the bridge reconstructs that BV failure condition byte-for-byte
        // (`reconstruct_bv_mul_overflow_body`) and STAMPS it as the obligation's
        // solvable core (no longer fail-closed). The fixture's `a * b` (i32, plain
        // locals) is exactly the bare envelope, so the obligation carries the
        // signed BV core. (The arg-range + param-env wrappers needed for
        // byte-equality to trust-vcgen's FULL formula are reconstructed by the
        // verdict-flip's `reconstruct_full_safety_formula_candidates`, not the stamp.)
        let module = lower_to_trust_ir(&mul_overflow_guard()).expect("lowers");
        let arith: Vec<_> = crate::vcgen_proto::safety_obligations_from_trust_ir_module(&module)
            .into_iter()
            .filter(|o| o.kind == ObligationKind::ArithmeticSafety)
            .collect();
        assert_eq!(arith.len(), 1, "mul surfaces a covering ArithmeticSafety obligation");
        assert!(
            arith[0].smtlib.is_some() && arith[0].formula_json.is_some(),
            "mul-overflow obligation must now stamp the reconstructed BV core: {:?}",
            arith[0]
        );
        let smtlib = arith[0].smtlib.as_deref().unwrap();
        assert!(
            smtlib.contains("bvmul"),
            "mul obligation core must be the bitvector encoding (bvmul present): {smtlib}"
        );
        let raw = module
            .proof_obligations
            .iter()
            .find(|o| o.kind == ObligationKind::ArithmeticSafety)
            .expect("mul obligation present");
        let payload = raw.formula.as_ref().expect("source metadata present").payload.clone();
        assert!(
            !payload.contains("safety_formula_not_reconstructed"),
            "mul obligation must no longer record the fail-closed audit marker: {payload}"
        );
    }
}
