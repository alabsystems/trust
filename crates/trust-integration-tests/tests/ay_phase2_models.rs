// trust-integration-tests/tests/ay_phase2_models.rs: Phase 2 ay function model-check showcase
//
// Showcase: Trust builds VerifiableFunction models of selected ay solver
// functions and dispatches VCs through the pipeline, optionally to real ay.
//
// Models 3 real ay functions:
//   1. Literal encoding (ay-sat/src/literal.rs:51-66) — shift safety
//   2. LEB128 decoder  (ay-proof-common/src/leb128.rs:9-28) — shift overflow under invariant
//   3. VSIDS rescale   (ay-sat/src/vsids/mod.rs:589-605, heap.rs:34-58) — float overflow guard
//
// Issue: #631 | Epic: #549
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::ay_test_support::require_ay;
use trust_router::VerificationBackend;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationResult,
};

// ---------------------------------------------------------------------------
// Model 1: ay Literal Encoding — Literal::positive and Literal::negative
//
// Source: ~/ay/crates/ay-sat/src/literal.rs:51-66
//   pub fn positive(var: Variable) -> Self { Self(var.0 << 1) }
//   pub fn negative(var: Variable) -> Self { Self((var.0 << 1) | 1) }
//
// The shift `var.0 << 1` on u32 uses a constant in-range shift amount, so it
// is safe as a Rust shift operation. ay still guards `var.0 <= i32::MAX as u32`
// in `assert_encodable_variable` to preserve literal encoding invariants; that
// guard is not a Rust shift-overflow guard.
//
// Additionally we model the guarded version: with precondition var <= i32::MAX,
// the shift is safe.
// ---------------------------------------------------------------------------

/// Build model of `Literal::positive(var)` — `Self(var.0 << 1)`.
///
/// For u32, shifting left by one has an in-range shift amount, so this model
/// demonstrates that the raw Rust shift operation is safe. ay's
/// `assert!(var.0 <= i32::MAX)` guard protects the literal encoding invariant,
/// not the shift operator's RHS bound.
///
/// CANONICAL CHECKED-SHIFT SPELLING (2026-08-21): `CheckedBinaryOp(Shl)` does
/// not exist — admission outlaws it (only Add/Sub/Mul produce the audited
/// `(value, bool)` carrier, and the extractor never emits checked shifts).
/// rustc guards a shift with the Lt-condition assert (opposite polarity to the
/// flag asserts), then performs the PLAIN shift in the assert's target block.
///
/// MIR layout:
///   _0: u32  (return — the encoded literal)
///   _1: u32  (arg: var.0)
///   _2: u32  (_1 << 1 — the shifted value)
///   _3: bool (shift-amount-in-range condition)
///
/// bb0: _3 = Lt(1, 32); assert(_3, expected: true, Overflow(Shl)) -> bb1
/// bb1: _2 = Shl(_1, 1); _0 = _2; return
///
/// VCs: ShiftOverflow { op: Shl, operand_ty: u32, shift_ty: u32 }
fn build_literal_positive_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "literal_positive".to_string(),
        def_path: "ay::literal::Literal::positive".to_string(),
        span: SourceSpan {
            file: "ay/crates/ay-sat/src/literal.rs".to_string(),
            line_start: 51,
            col_start: 5,
            line_end: 54,
            col_end: 6,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("var_id".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: None },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("shift_ok".into()) },
            ],
            blocks: vec![
                // bb0: _3 = Lt(1, 32); assert(_3, true, Overflow(Shl)) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Constant(ConstValue::Uint(1, 32)),
                            Operand::Constant(ConstValue::Uint(32, 32)),
                        ),
                        span: SourceSpan {
                            file: "ay/crates/ay-sat/src/literal.rs".to_string(),
                            line_start: 53,
                            col_start: 14,
                            line_end: 53,
                            col_end: 26,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(3)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _2 = Shl(_1, 1); _0 = _2; return
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-sat/src/literal.rs".to_string(),
                                line_start: 53,
                                col_start: 14,
                                line_end: 53,
                                col_end: 26,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Build model of `Literal::negative(var)` — `Self((var.0 << 1) | 1)`.
///
/// Same canonical shift model as `positive`: `(var.0 << 1) | 1`, spelled as the
/// Lt-condition assert plus the plain shift in the target block (see
/// `build_literal_positive_model` for why `CheckedBinaryOp(Shl)` is outlawed).
/// The shift amount is the in-range constant 1. The BitOr with 1 does not
/// overflow (it just sets the lowest bit).
///
/// MIR layout:
///   _0: u32  (return — the encoded literal)
///   _1: u32  (arg: var.0)
///   _2: bool (shift-amount-in-range condition)
///   _3: u32  (_1 << 1 — the doubled value)
///   _4: u32  (_3 | 1 — the final literal encoding)
///
/// bb0: _2 = Lt(1, 32); assert(_2, expected: true, Overflow(Shl)) -> bb1
/// bb1: _3 = Shl(_1, 1); _4 = _3 | 1; _0 = _4; return
///
/// VCs: ShiftOverflow { op: Shl, operand_ty: u32, shift_ty: u32 }
fn build_literal_negative_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "literal_negative".to_string(),
        def_path: "ay::literal::Literal::negative".to_string(),
        span: SourceSpan {
            file: "ay/crates/ay-sat/src/literal.rs".to_string(),
            line_start: 63,
            col_start: 5,
            line_end: 66,
            col_end: 6,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("var_id".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("shift_ok".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                // bb0: _2 = Lt(1, 32); assert(_2, true, Overflow(Shl)) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Constant(ConstValue::Uint(1, 32)),
                            Operand::Constant(ConstValue::Uint(32, 32)),
                        ),
                        span: SourceSpan {
                            file: "ay/crates/ay-sat/src/literal.rs".to_string(),
                            line_start: 65,
                            col_start: 14,
                            line_end: 65,
                            col_end: 30,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _3 = Shl(_1, 1); _4 = _3 | 1; _0 = _4; return
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-sat/src/literal.rs".to_string(),
                                line_start: 65,
                                col_start: 14,
                                line_end: 65,
                                col_end: 30,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::BitOr,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Model 2: ay LEB128 Decoder — read_u64 loop body shift safety
//
// Source: ~/ay/crates/ay-proof-common/src/leb128.rs:9-28
//   value |= u64::from(byte & 0x7f) << shift;
//   shift += 7;
//   if shift >= 64 { return Err(Leb128Overflow) }
//
// The shift `<< shift` is safe when `shift < 64`. The guard fires AFTER
// shift += 7, so the shift values at the point of the shift expression are
// {0, 7, 14, 21, 28, 35, 42, 49, 56, 63} — all < 64.
//
// Model: takes `shift: u32` and `byte: u8` (modeled as u32 with mask).
// Precondition: shift < 64 AND shift % 7 == 0 (loop invariant).
// Computes: (byte & 0x7f) cast to u64, then << shift.
// Expected: shift overflow VC is UNSAT (shift is safe under the invariant).
//
// We model the shift on a u64 value with u32 shift amount.
// ---------------------------------------------------------------------------

/// Build model of LEB128 read_u64 loop body shift.
///
/// Canonical checked-shift spelling (see `build_literal_positive_model`): the
/// Lt-condition assert guards the shift amount against the SHIFTED value's
/// width (u64 → 64), then the plain shift executes in the target block.
///
/// MIR layout:
///   _0: u64  (return — unused, we care about the shift VC)
///   _1: u32  (arg: shift — the current shift amount)
///   _2: u32  (arg: byte — raw byte from input)
///   _3: u32  (byte & 0x7f — masked value)
///   _4: u64  (u64::from(_3) — widened to u64)
///   _5: u64  (_4 << _1 — the shifted value)
///   _6: u64  (copy of the shifted value)
///   _7: bool (shift-amount-in-range condition)
///
/// bb0: _3 = _2 & 0x7f; _4 = cast(_3 as u64); _7 = Lt(_1, 64);
///      assert(_7, expected: true, Overflow(Shl)) -> bb1
/// bb1: _5 = Shl(_4, _1); _6 = _5; _0 = _6; return
///
/// VCs: ShiftOverflow { op: Shl, operand_ty: u64, shift_ty: u32 }
fn build_leb128_shift_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "leb128_read_u64_shift".to_string(),
        def_path: "ay::leb128::read_u64::loop_body_shift".to_string(),
        span: SourceSpan {
            file: "ay/crates/ay-proof-common/src/leb128.rs".to_string(),
            line_start: 19,
            col_start: 9,
            line_end: 19,
            col_end: 52,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("shift".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("byte".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None }, // byte & 0x7f
                LocalDecl { index: 4, ty: Ty::u64(), name: None }, // cast to u64
                LocalDecl { index: 5, ty: Ty::u64(), name: None }, // shifted value
                LocalDecl { index: 6, ty: Ty::u64(), name: None }, // copy of shifted value
                LocalDecl { index: 7, ty: Ty::Bool, name: Some("shift_ok".into()) },
            ],
            blocks: vec![
                // bb0: _3 = _2 & 0x7f; _4 = cast(_3 as u64); _7 = Lt(_1, 64);
                //      assert(_7, true, Overflow(Shl)) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::BitAnd,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(0x7f, 32)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-proof-common/src/leb128.rs".to_string(),
                                line_start: 19,
                                col_start: 22,
                                line_end: 19,
                                col_end: 35,
                            },
                        },
                        // Cast u32 -> u64 (u64::from)
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(3)), Ty::u64()),
                            span: SourceSpan::default(),
                        },
                        // Shift-amount range condition (against the u64 width)
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(64, 32)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-proof-common/src/leb128.rs".to_string(),
                                line_start: 19,
                                col_start: 9,
                                line_end: 19,
                                col_end: 52,
                            },
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(7)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _5 = Shl(_4, _1); _6 = _5; _0 = _6; return
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(4)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-proof-common/src/leb128.rs".to_string(),
                                line_start: 19,
                                col_start: 9,
                                line_end: 19,
                                col_end: 52,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(6))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Model 3: ay VSIDS Score Rescaling — bump_score + rescale guard
//
// Source: ~/ay/crates/ay-sat/src/vsids/heap.rs:34-58, mod.rs:589-605
//   activities[idx] += self.increment;
//   if activities[idx] > 1e100 { self.rescale(); }
//   // rescale: for act in &mut activities { *act *= 1e-100; }
//   //          self.increment *= 1e-100;
//
// The model captures the bump operation as a plain Add on f64 values, and
// the rescale guard. Without the rescale, activities can overflow to Inf.
// With the rescale, multiplication by 1e-100 brings values back in range —
// but only if the activity was finite before rescale.
//
// We model this as: activity += increment (float overflow VC), then
// activity *= 1e-100 (the rescale). The multiply can also overflow if
// activity is already extremely large.
//
// Since this is floating-point, the VCs use FloatOverflowToInfinity.
// ---------------------------------------------------------------------------

/// Build model of VSIDS bump_score: activity += increment, with rescale guard.
///
/// MIR layout:
///   _0: Unit  (return)
///   _1: f64  (arg: activity — current VSIDS score)
///   _2: f64  (arg: increment — current bump increment)
///   _3: f64  (result of _1 + _2)
///   _4: f64  (new_activity = _3)
///   _5: bool  (_4 > 1e100 — rescale guard)
///   _6: f64  (rescaled = _4 * 1e-100)
///
/// bb0: _3 = _1 + _2; goto bb1
/// bb1: _4 = _3; _5 = _4 > 1e100; switchInt(_5): true -> bb2, false -> bb3
/// bb2: _6 = _4 * 1e-100; return  (rescale path)
/// bb3: return  (no rescale path)
///
/// VCs: FloatOverflowToInfinity{Add} for the activity bump
fn build_vsids_bump_score_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "vsids_bump_score".to_string(),
        def_path: "ay::vsids::VSIDS::bump_score".to_string(),
        span: SourceSpan {
            file: "ay/crates/ay-sat/src/vsids/heap.rs".to_string(),
            line_start: 34,
            col_start: 5,
            line_end: 59,
            col_end: 6,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("activity".into()) },
                LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("increment".into()) },
                LocalDecl { index: 3, ty: Ty::f64_ty(), name: None }, // activity + increment
                LocalDecl { index: 4, ty: Ty::f64_ty(), name: None }, // new_activity
                LocalDecl { index: 5, ty: Ty::Bool, name: None },     // rescale guard
                LocalDecl { index: 6, ty: Ty::f64_ty(), name: None }, // rescaled value
            ],
            blocks: vec![
                // bb0: _3 = _1 + _2; goto bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan {
                            file: "ay/crates/ay-sat/src/vsids/heap.rs".to_string(),
                            line_start: 42,
                            col_start: 9,
                            line_end: 42,
                            col_end: 45,
                        },
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1: _4 = _3; _5 = _4 > 1e100; switchInt(_5) -> [true: bb2, false: bb3]
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Float(1e100)),
                            ),
                            span: SourceSpan {
                                file: "ay/crates/ay-sat/src/vsids/heap.rs".to_string(),
                                line_start: 43,
                                col_start: 12,
                                line_end: 43,
                                col_end: 39,
                            },
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _6 = _4 * 1e-100; return (rescale path)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(ConstValue::Float(1e-100)),
                        ),
                        span: SourceSpan {
                            file: "ay/crates/ay-sat/src/vsids/mod.rs".to_string(),
                            line_start: 591,
                            col_start: 13,
                            line_end: 591,
                            col_end: 29,
                        },
                    }],
                    terminator: Terminator::Return,
                },
                // bb3: return (no rescale needed)
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ===========================================================================
// Tests: VC generation (no ay required)
// ===========================================================================

#[test]
fn test_literal_positive_vc_generation() {
    let func = build_literal_positive_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // var.0 << 1 generates ShiftOverflow{Shl}
    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(
        !shift_vcs.is_empty(),
        "literal_positive model must produce ShiftOverflow(Shl) VC, got {} VCs total: {:?}",
        vcs.len(),
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );

    assert_eq!(vcs[0].function, "literal_positive");

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
    }
}

#[test]
fn test_literal_negative_vc_generation() {
    let func = build_literal_negative_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // (var.0 << 1) | 1 — the shift generates ShiftOverflow{Shl}
    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(
        !shift_vcs.is_empty(),
        "literal_negative model must produce ShiftOverflow(Shl) VC, got {} VCs total: {:?}",
        vcs.len(),
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );

    assert_eq!(vcs[0].function, "literal_negative");
}

#[test]
fn test_leb128_shift_vc_generation() {
    let func = build_leb128_shift_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(
        !shift_vcs.is_empty(),
        "leb128_shift model must produce ShiftOverflow(Shl) VC, got {} VCs total: {:?}",
        vcs.len(),
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );

    assert_eq!(vcs[0].function, "leb128_read_u64_shift");
}

#[test]
fn test_vsids_bump_score_vc_generation() {
    let func = build_vsids_bump_score_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Float addition generates FloatOverflowToInfinity{Add}, not ArithmeticOverflow
    let float_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. }))
        .collect();
    assert!(
        !float_vcs.is_empty(),
        "vsids_bump_score model must produce FloatOverflowToInfinity(Add) VC, got {} VCs total: {:?}",
        vcs.len(),
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );

    // The rescale path (Mul by 1e-100) also generates FloatOverflowToInfinity{Mul}
    let mul_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Mul, .. }))
        .collect();
    assert!(
        !mul_vcs.is_empty(),
        "vsids_bump_score rescale path must produce FloatOverflowToInfinity(Mul) VC"
    );

    assert_eq!(vcs[0].function, "vsids_bump_score");
}

// ===========================================================================
// Tests: Optional real ay solver model checks
// ===========================================================================

/// AY proves the Literal::positive shift check safe: the shift amount is
/// the constant 1, which is in range for u32.
#[test]
fn test_real_ay_literal_positive_shift_safe() {
    let ay = require_ay();
    let func = build_literal_positive_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(!shift_vcs.is_empty(), "must have ShiftOverflow VC");

    for vc in &shift_vcs {
        if !ay.can_handle(vc) {
            eprintln!("ay cannot handle {:?}, skipping", vc.kind);
            continue;
        }
        let result = ay.verify(vc);
        eprintln!("ay result for literal_positive {:?}: {:?}", vc.kind, result);

        assert!(
            result.is_proved(),
            "ay must prove constant-one literal_positive shift safe. Got: {result:?}"
        );

        if let VerificationResult::Proved { time_ms, .. } = &result {
            assert!(*time_ms < 30_000, "should complete in under 30s");
        }
    }
}

/// AY proves the Literal::negative shift check safe for the same reason as
/// positive; `(var.0 << 1) | 1` uses an in-range constant shift amount.
#[test]
fn test_real_ay_literal_negative_shift_safe() {
    let ay = require_ay();
    let func = build_literal_negative_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(!shift_vcs.is_empty(), "must have ShiftOverflow VC");

    for vc in &shift_vcs {
        if !ay.can_handle(vc) {
            continue;
        }
        let result = ay.verify(vc);
        eprintln!("ay result for literal_negative {:?}: {:?}", vc.kind, result);

        assert!(
            result.is_proved(),
            "ay must prove constant-one literal_negative shift safe. Got: {result:?}"
        );
    }
}

/// AY checks the LEB128 shift model. Under the loop invariant `shift < 64`,
/// the shift `<< shift` on a u64 value cannot overflow.
///
/// Without constraints on shift, the shift CAN overflow (shift >= 64).
/// The full invariant (shift < 64 AND shift % 7 == 0) makes the shift VC UNSAT,
/// but even the weaker constraint (shift < 64) suffices for shift safety.
///
/// We test without preconditions: the operation's REFUTABLE shift VC must be
/// SAT (ay finds shift=64 or similar as a counterexample). This demonstrates
/// that ay correctly identifies the need for the loop guard.
///
/// DUAL ROWS (2026-08-21 campaign): trust-vcgen now dual-emits at the shift —
/// the safety-walk STATEMENT row (the unconditioned `shift >= 64` question ay
/// must refute) plus the cond-bound ASSERT-lane row, whose exact `shift_ok =
/// Lt(shift, 64)` binding contradicts the violation on the guarded path, so it
/// legitimately PROVES. The pinned strength is unchanged: exactly one row is
/// refuted, and it carries the shift >= 64 counterexample.
#[test]
fn test_real_ay_leb128_shift_without_guard() {
    let ay = require_ay();
    let func = build_leb128_shift_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(!shift_vcs.is_empty(), "must have ShiftOverflow VC");

    let mut failed = 0usize;
    for vc in &shift_vcs {
        if !ay.can_handle(vc) {
            continue;
        }
        let result = ay.verify(vc);
        eprintln!("ay result for leb128 shift (no guard) {:?}: {:?}", vc.kind, result);

        match &result {
            // The statement row: without the guard, shift can be >= 64.
            VerificationResult::Failed { counterexample, .. } => {
                failed += 1;
                if let Some(cex) = counterexample {
                    eprintln!("  Counterexample (shift >= 64 causes overflow): {cex}");
                }
            }
            // The cond-bound assert-lane row self-discharges (guarded path).
            r if r.is_proved() => {}
            other => panic!(
                "each leb128 shift row must either refute (statement row) or prove \
                 (cond-bound assert-lane row). Got: {other:?}"
            ),
        }
    }
    assert_eq!(
        failed, 1,
        "exactly one shift row (the unconditioned statement row) must be refuted \
         when shift is unconstrained"
    );
}

/// AY checks the VSIDS bump_score model: activity addition can overflow f64
/// when both activity and increment are large positive values.
#[test]
#[ignore = "measurement instrument: logs ay's verdict on each float-add overflow VC and passes \
            on any of them; run with --ignored --nocapture"]
fn test_real_ay_vsids_bump_score_overflow() {
    let ay = require_ay();
    let func = build_vsids_bump_score_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. }))
        .collect();

    for vc in &add_vcs {
        if !ay.can_handle(vc) {
            eprintln!("ay cannot handle VSIDS {:?}, skipping", vc.kind);
            continue;
        }
        let result = ay.verify(vc);
        eprintln!("ay result for vsids_bump_score {:?}: {:?}", vc.kind, result);

        // Float addition overflow depends on the ay float encoding.
        // Log the result regardless — this is the stretch goal target.
        match &result {
            VerificationResult::Proved { solver, time_ms, .. } => {
                eprintln!(
                    "  UNSAT/safe in model by {solver} in {time_ms}ms (float abstraction may be conservative)"
                );
            }
            VerificationResult::Failed { counterexample, solver, time_ms } => {
                eprintln!("  FAILED: {solver} found violation in {time_ms}ms");
                if let Some(cex) = counterexample {
                    eprintln!("  Counterexample: {cex}");
                }
            }
            other => {
                eprintln!("  Result: {other:?}");
            }
        }
    }
}

// ===========================================================================
// Full suite: selected ay function models with summary report
// ===========================================================================

#[test]
fn test_ay_phase2_full_suite() {
    let models: Vec<(&str, VerifiableFunction)> = vec![
        ("ay::literal::Literal::positive", build_literal_positive_model()),
        ("ay::literal::Literal::negative", build_literal_negative_model()),
        ("ay::leb128::read_u64", build_leb128_shift_model()),
        ("ay::vsids::VSIDS::bump_score", build_vsids_bump_score_model()),
    ];

    let router = trust_router::Router::new();
    let mut total_vcs = 0;

    println!();
    println!("=== Trust Phase 2 Model-Check Showcase: ay Function Models ===");
    println!("Models of real ay source functions dispatched through Trust pipeline.");
    println!();

    for (source_path, model) in &models {
        let vcs = trust_vcgen::generate_vcs(model);
        let results = router.verify_all(&vcs);
        total_vcs += results.len();

        println!("  {} ({})", model.name, source_path);
        for vc in &vcs {
            println!("    VC: {:?} — level {:?}", vc.kind, vc.kind.proof_level());
        }
        println!("    {} VCs generated, {} routed", vcs.len(), results.len());
    }

    println!();
    println!("  Phase 2 summary:");
    println!("    {} ay functions modeled", models.len());
    println!("    {} total VCs generated and routed", total_vcs);
    println!("    Source files modeled:");
    println!("      - ay/crates/ay-sat/src/literal.rs (positive, negative)");
    println!("      - ay/crates/ay-proof-common/src/leb128.rs (read_u64 shift)");
    println!("      - ay/crates/ay-sat/src/vsids/heap.rs (bump_score + rescale)");
    println!();

    assert!(
        total_vcs >= 4,
        "Phase 2 should generate at least 4 VCs (1 per model + extras), got {}",
        total_vcs
    );
}

/// Generate a showcase report from Phase 2 models.
#[test]
fn test_ay_phase2_report_generation() {
    let models: Vec<VerifiableFunction> = vec![
        build_literal_positive_model(),
        build_literal_negative_model(),
        build_leb128_shift_model(),
        build_vsids_bump_score_model(),
    ];

    let router = trust_router::Router::new();
    let mut all_results = Vec::new();

    for model in &models {
        let vcs = trust_vcgen::generate_vcs(model);
        let results = router.verify_all(&vcs);
        all_results.extend(results);
    }

    let report = trust_report::build_json_report("ay-phase2-model-check-showcase", &all_results);

    assert_eq!(report.crate_name, "ay-phase2-model-check-showcase");
    assert!(
        report.summary.functions_analyzed >= 3,
        "report should cover at least 3 ay functions, got {}",
        report.summary.functions_analyzed
    );

    let func_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(func_names.contains(&"literal_positive"), "must contain literal_positive");
    assert!(func_names.contains(&"literal_negative"), "must contain literal_negative");
    assert!(func_names.contains(&"leb128_read_u64_shift"), "must contain leb128_read_u64_shift");
    assert!(func_names.contains(&"vsids_bump_score"), "must contain vsids_bump_score");

    let text = trust_report::format_json_summary(&report);
    println!();
    println!("=== Trust Phase 2: ay Function Model-Check Report ===");
    println!("{}", text);
}
