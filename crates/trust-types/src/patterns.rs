// trust-types/patterns.rs: MIR pattern matching for common vulnerability detection
//
// Scans VerifiableBody instances for patterns that indicate potential
// vulnerabilities: unchecked arithmetic, unchecked indexing, division
// without zero check, use-after-move, and uninitialized reads.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
#![allow(dead_code)]

use crate::VcKind;
use crate::fx::FxHashSet;
use crate::model::{
    BinOp, BlockId, Operand, Place, Projection, Rvalue, Statement, Terminator, VerifiableBody,
};

/// Severity level for a detected vulnerability pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Severity {
    High,
    Medium,
    Low,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Severity::High => f.write_str("High"),
            Severity::Medium => f.write_str("Medium"),
            Severity::Low => f.write_str("Low"),
        }
    }
}

/// A vulnerability pattern match found in a MIR body.
#[derive(Debug, Clone)]
pub(crate) struct PatternMatch {
    /// Name of the pattern that matched (e.g. "unchecked_arithmetic").
    pub pattern_name: String,
    /// Block where the pattern was detected.
    pub block_id: BlockId,
    /// Statement index within the block (None if in terminator).
    pub stmt_index: Option<usize>,
    /// Severity of the potential vulnerability.
    pub severity: Severity,
    /// Human-readable description of the finding.
    pub description: String,
    /// Suggested verification condition kind to generate.
    pub suggested_vc_kind: VcKind,
}

/// Scan a MIR body for all known vulnerability patterns.
///
/// Runs every detector and collects results. The returned matches are
/// ordered by block id then statement index.
#[must_use]
pub(crate) fn scan_body(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut matches = Vec::new();
    matches.extend(detect_unchecked_arithmetic(body));
    matches.extend(detect_unchecked_indexing(body));
    matches.extend(detect_unchecked_division(body));
    matches.extend(detect_use_after_move(body));
    matches.extend(detect_uninitialized_read(body));
    matches.sort_by_key(|m| (m.block_id.0, m.stmt_index.unwrap_or(usize::MAX)));
    matches
}

/// Detect Add/Sub/Mul BinOps that are not wrapped in CheckedBinaryOp
/// and lack a preceding overflow Assert in the same block.
#[must_use]
pub(crate) fn detect_unchecked_arithmetic(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut results = Vec::new();

    for block in &body.blocks {
        // Collect locals assigned by CheckedBinaryOp in this block --
        // these have compiler-inserted overflow checks.
        let checked_locals: FxHashSet<usize> = block
            .stmts
            .iter()
            .filter_map(|stmt| match stmt {
                Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(..), .. } => {
                    Some(place.local)
                }
                _ => None,
            })
            .collect();

        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = stmt
                && op.can_overflow()
                && !is_operand_from_checked(&checked_locals, lhs, rhs)
            {
                let op_name = format!("{op:?}");
                let lhs_ty = operand_ty_hint(body, lhs);
                let rhs_ty = operand_ty_hint(body, rhs);
                results.push(PatternMatch {
                    pattern_name: "unchecked_arithmetic".to_string(),
                    block_id: block.id,
                    stmt_index: Some(idx),
                    severity: Severity::High,
                    description: format!("Unchecked {op_name} operation without overflow guard"),
                    suggested_vc_kind: VcKind::ArithmeticOverflow {
                        op: *op,
                        operand_tys: (lhs_ty, rhs_ty),
                    },
                });
            }
        }
    }

    results
}

/// Detect Index projections without a preceding bounds check Assert
/// in the same block or a dominating block.
#[must_use]
pub(crate) fn detect_unchecked_indexing(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut results = Vec::new();

    // Collect blocks that have a BoundsCheck assert terminator -- these
    // guard the target block.
    let bounds_checked_targets: FxHashSet<usize> = body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert {
                msg: crate::model::AssertMessage::BoundsCheck, target, ..
            } => Some(target.0),
            _ => None,
        })
        .collect();

    for block in &body.blocks {
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue, .. } = stmt
                && rvalue_has_index_projection(rvalue)
                && !bounds_checked_targets.contains(&block.id.0)
            {
                results.push(PatternMatch {
                    pattern_name: "unchecked_indexing".to_string(),
                    block_id: block.id,
                    stmt_index: Some(idx),
                    severity: Severity::High,
                    description: "Index operation without preceding bounds check".to_string(),
                    suggested_vc_kind: VcKind::IndexOutOfBounds,
                });
            }
        }
    }

    results
}

/// Detect Div/Rem BinOps without a preceding DivisionByZero or
/// RemainderByZero assert.
#[must_use]
pub(crate) fn detect_unchecked_division(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut results = Vec::new();

    // Collect blocks guarded by a division-by-zero assert.
    let div_checked_targets: FxHashSet<usize> = body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert {
                msg:
                    crate::model::AssertMessage::DivisionByZero
                    | crate::model::AssertMessage::RemainderByZero,
                target,
                ..
            } => Some(target.0),
            _ => None,
        })
        .collect();

    for block in &body.blocks {
        if div_checked_targets.contains(&block.id.0) {
            continue;
        }

        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), .. } = stmt
                && op.is_division()
            {
                let vc_kind = match op {
                    BinOp::Div => VcKind::DivisionByZero,
                    BinOp::Rem => VcKind::RemainderByZero,
                    _ => {
                        unreachable!("BinOp::is_division() only returns true for Div and Rem")
                    }
                };
                results.push(PatternMatch {
                    pattern_name: "unchecked_division".to_string(),
                    block_id: block.id,
                    stmt_index: Some(idx),
                    severity: Severity::High,
                    description: format!("Unchecked {op:?} operation without zero-divisor guard"),
                    suggested_vc_kind: vc_kind,
                });
            }
        }
    }

    results
}

/// Detect variable use after StorageDead (approximated by Drop terminator
/// on the same local, then a subsequent read in a later block).
///
/// This is a conservative linear scan: we track locals that have been
/// dropped and flag any later read of those locals.
#[must_use]
pub(crate) fn detect_use_after_move(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut results = Vec::new();
    let mut dropped_locals: FxHashSet<usize> = FxHashSet::default();

    for block in &body.blocks {
        // Check statements for reads of dropped locals.
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue, .. } = stmt {
                for local in rvalue_read_locals(rvalue) {
                    if dropped_locals.contains(&local) {
                        let name =
                            body.locals.get(local).and_then(|l| l.name.as_deref()).unwrap_or("_");
                        results.push(PatternMatch {
                            pattern_name: "use_after_move".to_string(),
                            block_id: block.id,
                            stmt_index: Some(idx),
                            severity: Severity::High,
                            description: format!("Read of local _{local} ({name}) after drop/move"),
                            suggested_vc_kind: VcKind::Unreachable,
                        });
                    }
                }
            }
        }

        // Track drops from terminators.
        if let Terminator::Drop { place, .. } = &block.terminator {
            dropped_locals.insert(place.local);
        }
    }

    results
}

/// Detect reads of locals that have never been assigned.
///
/// Skips argument locals (indices 1..=arg_count) and the return local
/// (index 0) since arguments are always initialized by the caller and
/// the return slot is write-only until return.
#[must_use]
pub(crate) fn detect_uninitialized_read(body: &VerifiableBody) -> Vec<PatternMatch> {
    let mut results = Vec::new();
    let mut assigned_locals: FxHashSet<usize> = FxHashSet::default();

    // Arguments are always initialized (locals 1..=arg_count).
    for i in 0..=body.arg_count {
        assigned_locals.insert(i);
    }

    for block in &body.blocks {
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                // Check reads first (before recording the assignment).
                for local in rvalue_read_locals(rvalue) {
                    if !assigned_locals.contains(&local) {
                        let name =
                            body.locals.get(local).and_then(|l| l.name.as_deref()).unwrap_or("_");
                        results.push(PatternMatch {
                            pattern_name: "uninitialized_read".to_string(),
                            block_id: block.id,
                            stmt_index: Some(idx),
                            severity: Severity::Medium,
                            description: format!(
                                "Read of local _{local} ({name}) before any assignment"
                            ),
                            suggested_vc_kind: VcKind::Unreachable,
                        });
                    }
                }
                // Record the assignment.
                assigned_locals.insert(place.local);
            }
        }
    }

    results
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Check whether either operand is reading from a local produced by
/// CheckedBinaryOp (i.e., extracting the `.0` field of a checked result).
fn is_operand_from_checked(
    checked_locals: &FxHashSet<usize>,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    operand_is_checked_field(checked_locals, lhs) || operand_is_checked_field(checked_locals, rhs)
}

fn operand_is_checked_field(checked_locals: &FxHashSet<usize>, op: &Operand) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => checked_locals.contains(&place.local),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
    }
}

/// Check whether an rvalue contains an Index projection.
fn rvalue_has_index_projection(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => operand_has_index(op),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_has_index(lhs) || operand_has_index(rhs)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_has_index(place),
        Rvalue::Aggregate(_, ops) => ops.iter().any(operand_has_index),
        Rvalue::Repeat(op, _) => operand_has_index(op),
        // Trust: W2 inc-0 — pointer arithmetic reads both operands.
        Rvalue::PtrOffset { ptr, count } => operand_has_index(ptr) || operand_has_index(count),
        Rvalue::Unsupported { operands, .. } => operands.iter().any(operand_has_index),
    }
}

fn operand_has_index(op: &Operand) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place_has_index(place),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
    }
}

fn place_has_index(place: &Place) -> bool {
    place.projections.iter().any(|p| matches!(p, Projection::Index(_)))
}

/// Collect all locals that are read by an rvalue.
fn rvalue_read_locals(rvalue: &Rvalue) -> Vec<usize> {
    let mut locals = Vec::new();
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
            extend_operand_locals(&mut locals, op);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            extend_operand_locals(&mut locals, lhs);
            extend_operand_locals(&mut locals, rhs);
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => {
            locals.push(place.local);
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                extend_operand_locals(&mut locals, op);
            }
        }
        Rvalue::Repeat(op, _) => {
            extend_operand_locals(&mut locals, op);
        }
        // Trust: W2 inc-0 — pointer arithmetic reads both operands.
        Rvalue::PtrOffset { ptr, count } => {
            extend_operand_locals(&mut locals, ptr);
            extend_operand_locals(&mut locals, count);
        }
        Rvalue::Unsupported { operands, .. } => {
            for op in operands {
                extend_operand_locals(&mut locals, op);
            }
        }
    }
    locals
}

fn extend_operand_locals(locals: &mut Vec<usize>, op: &Operand) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            locals.push(place.local);
        }
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => {}
    }
}

/// Best-effort type hint for an operand by looking up locals.
fn operand_ty_hint(body: &VerifiableBody, op: &Operand) -> crate::model::Ty {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            body.locals.get(place.local).map(|l| l.ty.clone()).unwrap_or(crate::model::Ty::Unit)
        }
        Operand::Constant(crate::model::ConstValue::Int(_)) => crate::model::Ty::i64(),
        Operand::Constant(crate::model::ConstValue::Uint(_, w)) => {
            crate::model::Ty::Int { width: *w, signed: false }
        }
        Operand::Constant(crate::model::ConstValue::Float(_)) => crate::model::Ty::f64_ty(),
        Operand::Constant(crate::model::ConstValue::FloatBits { width, .. }) => {
            crate::model::Ty::Float { width: *width }
        }
        Operand::Constant(crate::model::ConstValue::Bool(_)) => crate::model::Ty::Bool,
        Operand::Constant(
            crate::model::ConstValue::Unit
            | crate::model::ConstValue::CallableItem { .. },
        ) => crate::model::Ty::Unit,
        // a `&str` literal has no numeric type and never feeds an
        // arithmetic/bounds VC; the neutral `Unit` hint keeps it out of sort
        // selection. Its SMT identity comes from `ConstValue::str_smt_var_name`.
        Operand::Constant(crate::model::ConstValue::Str { .. }) => crate::model::Ty::Unit,
        // An opaque `&[…]` table constant: no numeric type, never feeds an
        // arithmetic/bounds VC; neutral `Unit` hint (modeled as an opaque slice).
        Operand::Constant(crate::model::ConstValue::OpaqueConst) => crate::model::Ty::Unit,
        // A `UnitVariantRef` reference constant: same neutral `Unit` hint as
        // `OpaqueConst` above (modeled as an opaque fresh-symbolic ref).
        Operand::Constant(crate::model::ConstValue::UnitVariantRef { .. }) => {
            crate::model::Ty::Unit
        }
        // A typed opaque integer constant (const-generic `N`, associated const,
        // `size_of::<T>()` in a generic body): carries its declared integer type so
        // sort selection stays correct for the arithmetic/bounds VCs it DOES feed.
        // Its value is a fresh unconstrained symbol minted by the lowering bridge.
        Operand::Constant(crate::model::ConstValue::OpaqueScalar { width, signed }) => {
            crate::model::Ty::Int { width: *width, signed: *signed }
        }
        // Trust: piece #7a — a const-generic PARAM value carries its declared
        // integer type, exactly like `OpaqueScalar`, so sort selection stays
        // correct for the bounds/arith VCs it feeds. Its SMT identity (the
        // per-param symbol) is minted at the operand-lowering site in trust-vcgen.
        Operand::Constant(crate::model::ConstValue::ConstParam { width, signed, .. }) => {
            crate::model::Ty::Int { width: *width, signed: *signed }
        }
        // Trust: #564 — Symbolic formulas from lifted code; infer type from Sort if possible.
        Operand::Symbolic(formula) => match formula {
            crate::Formula::BitVec { width, .. } => {
                crate::model::Ty::Int { width: *width, signed: false }
            }
            crate::Formula::Bool(_)
            | crate::Formula::Not(_)
            | crate::Formula::And(_)
            | crate::Formula::Or(_)
            | crate::Formula::Eq(..)
            | crate::Formula::Lt(..)
            | crate::Formula::Le(..)
            | crate::Formula::Gt(..)
            | crate::Formula::Ge(..) => crate::model::Ty::Bool,
            crate::Formula::Var(_, sort) | crate::Formula::SymVar(_, sort) => match sort {
                crate::Sort::Bool => crate::model::Ty::Bool,
                crate::Sort::BitVec(w) => crate::model::Ty::Int { width: *w, signed: false },
                _ => crate::model::Ty::Unit,
            },
            _ => crate::model::Ty::Unit,
        },
        Operand::Unsupported { .. } => crate::model::Ty::Unit,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::*;

    // -----------------------------------------------------------------------
    // Helper: build a minimal VerifiableBody for tests
    // -----------------------------------------------------------------------

    fn make_body(
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
    ) -> VerifiableBody {
        VerifiableBody { locals, blocks, arg_count, return_ty: Ty::Unit }
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(String::from) }
    }

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    // =======================================================================
    // detect_unchecked_arithmetic
    // =======================================================================

    #[test]
    fn test_unchecked_arithmetic_detects_bare_add() {
        // _2 = Add(_0, _1) -- no CheckedBinaryOp, no overflow assert
        let body = make_body(
            vec![
                local(0, Ty::i32(), Some("a")),
                local(1, Ty::i32(), Some("b")),
                local(2, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_arithmetic(&body);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern_name, "unchecked_arithmetic");
        assert_eq!(matches[0].block_id, BlockId(0));
        assert_eq!(matches[0].stmt_index, Some(0));
        assert_eq!(matches[0].severity, Severity::High);
        assert!(matches[0].description.contains("Add"));
    }

    #[test]
    fn test_unchecked_arithmetic_ignores_checked_op() {
        // _3 = CheckedAdd(_1, _2) -> no flag since this IS the checked form
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), Some("b")),
                local(3, Ty::Tuple(vec![Ty::i32(), Ty::Bool]), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_arithmetic(&body);
        assert!(matches.is_empty(), "CheckedBinaryOp should not be flagged");
    }

    #[test]
    fn test_unchecked_arithmetic_ignores_use_of_checked_result() {
        // _3 = CheckedAdd(_1, _2); _4 = Add(_3, const 0)
        // The second Add reads from _3 (a checked-result local), so it
        // should NOT be flagged.
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), Some("b")),
                local(3, Ty::Tuple(vec![Ty::i32(), Ty::Bool]), None),
                local(4, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_arithmetic(&body);
        assert!(matches.is_empty(), "Op using checked local should not be flagged");
    }

    #[test]
    fn test_unchecked_arithmetic_ignores_non_overflow_ops() {
        // _2 = Eq(_0, _1) -- comparison cannot overflow
        let body = make_body(
            vec![local(0, Ty::i32(), None), local(1, Ty::i32(), None), local(2, Ty::Bool, None)],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_arithmetic(&body);
        assert!(matches.is_empty(), "Eq cannot overflow");
    }

    #[test]
    fn test_unchecked_arithmetic_detects_mul_and_sub() {
        let body = make_body(
            vec![
                local(0, Ty::i32(), Some("x")),
                local(1, Ty::i32(), Some("y")),
                local(2, Ty::i32(), None),
                local(3, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(0)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(0)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_arithmetic(&body);
        assert_eq!(matches.len(), 2);
        assert!(matches[0].description.contains("Mul"));
        assert!(matches[1].description.contains("Sub"));
    }

    // =======================================================================
    // detect_unchecked_indexing
    // =======================================================================

    #[test]
    fn test_unchecked_indexing_detects_bare_index() {
        // _2 = _0[_1] without a BoundsCheck assert
        let body = make_body(
            vec![
                local(0, Ty::Slice { elem: Box::new(Ty::i32()) }, Some("arr")),
                local(1, Ty::usize(), Some("idx")),
                local(2, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 0,
                        projections: vec![Projection::Index(1)],
                    })),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_indexing(&body);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern_name, "unchecked_indexing");
        assert_eq!(matches[0].severity, Severity::High);
    }

    #[test]
    fn test_unchecked_indexing_skips_bounds_checked_block() {
        // bb0: assert(BoundsCheck) -> bb1
        // bb1: _2 = _0[_1]
        let body = make_body(
            vec![
                local(0, Ty::Slice { elem: Box::new(Ty::i32()) }, Some("arr")),
                local(1, Ty::usize(), Some("idx")),
                local(2, Ty::i32(), None),
                local(3, Ty::Bool, None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(3)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 0,
                            projections: vec![Projection::Index(1)],
                        })),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            2,
        );

        let matches = detect_unchecked_indexing(&body);
        assert!(matches.is_empty(), "BoundsCheck-guarded block should not be flagged");
    }

    // =======================================================================
    // detect_unchecked_division
    // =======================================================================

    #[test]
    fn test_unchecked_division_detects_bare_div() {
        // _2 = Div(_0, _1) without a DivisionByZero assert
        let body = make_body(
            vec![
                local(0, Ty::i32(), Some("a")),
                local(1, Ty::i32(), Some("b")),
                local(2, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_division(&body);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern_name, "unchecked_division");
        assert!(matches!(matches[0].suggested_vc_kind, VcKind::DivisionByZero));
    }

    #[test]
    fn test_unchecked_division_detects_bare_rem() {
        let body = make_body(
            vec![
                local(0, Ty::i32(), Some("a")),
                local(1, Ty::i32(), Some("b")),
                local(2, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = detect_unchecked_division(&body);
        assert_eq!(matches.len(), 1);
        assert!(matches!(matches[0].suggested_vc_kind, VcKind::RemainderByZero));
    }

    #[test]
    fn test_unchecked_division_skips_zero_checked_block() {
        // bb0: assert(DivisionByZero) -> bb1
        // bb1: _2 = Div(_0, _1)
        let body = make_body(
            vec![
                local(0, Ty::i32(), Some("a")),
                local(1, Ty::i32(), Some("b")),
                local(2, Ty::i32(), None),
                local(3, Ty::Bool, None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(3)),
                        expected: true,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(0)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            2,
        );

        let matches = detect_unchecked_division(&body);
        assert!(matches.is_empty(), "DivisionByZero-guarded block should not be flagged");
    }

    #[test]
    fn test_unchecked_division_div_by_constant_still_flagged() {
        // _1 = Div(_0, const 2) -- constant divisor is still flagged
        // (the VC generator can optimize away the proof obligation, but
        // the pattern scanner is conservative)
        let body = make_body(
            vec![local(0, Ty::i32(), Some("a")), local(1, Ty::i32(), None)],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(0)),
                        Operand::Constant(ConstValue::Int(2)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let matches = detect_unchecked_division(&body);
        assert_eq!(matches.len(), 1);
    }

    // =======================================================================
    // detect_use_after_move
    // =======================================================================

    #[test]
    fn test_use_after_move_detects_read_after_drop() {
        // bb0: drop(_1) -> bb1
        // bb1: _2 = Use(_1) -- use after move
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("x")),
                local(2, Ty::i32(), None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            1,
        );

        let matches = detect_use_after_move(&body);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern_name, "use_after_move");
        assert!(matches[0].description.contains("_1"));
        assert!(matches[0].description.contains("x"));
    }

    #[test]
    fn test_use_after_move_no_false_positive_before_drop() {
        // bb0: _2 = Use(_1); drop(_1) -> bb1
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("x")),
                local(2, Ty::i32(), None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span(),
                    }],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            1,
        );

        let matches = detect_use_after_move(&body);
        assert!(matches.is_empty(), "Use before drop should not be flagged");
    }

    // =======================================================================
    // detect_uninitialized_read
    // =======================================================================

    #[test]
    fn test_uninitialized_read_detects_read_before_assign() {
        // _3 = Use(_2) where _2 is never assigned and not an argument
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),         // return
                local(1, Ty::i32(), Some("a")),   // arg
                local(2, Ty::i32(), Some("tmp")), // uninitialized
                local(3, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let matches = detect_uninitialized_read(&body);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern_name, "uninitialized_read");
        assert!(matches[0].description.contains("_2"));
        assert!(matches[0].description.contains("tmp"));
        assert_eq!(matches[0].severity, Severity::Medium);
    }

    #[test]
    fn test_uninitialized_read_skips_arguments() {
        // _2 = Use(_1) where _1 is an argument -- should NOT flag
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let matches = detect_uninitialized_read(&body);
        assert!(matches.is_empty(), "Arguments should be considered initialized");
    }

    #[test]
    fn test_uninitialized_read_skips_after_assignment() {
        // _2 = const 0; _3 = Use(_2)
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), Some("x")),
                local(3, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            1,
        );

        let matches = detect_uninitialized_read(&body);
        assert!(matches.is_empty(), "Read after assignment should not be flagged");
    }

    // =======================================================================
    // scan_body integration
    // =======================================================================

    #[test]
    fn test_scan_body_finds_multiple_patterns() {
        // A body with unchecked add AND unchecked div
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), Some("b")),
                local(3, Ty::i32(), None),
                local(4, Ty::i32(), None),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            2,
        );

        let matches = scan_body(&body);
        assert!(matches.len() >= 2, "Expected at least 2 findings, got {}", matches.len());

        let names: Vec<&str> = matches.iter().map(|m| m.pattern_name.as_str()).collect();
        assert!(names.contains(&"unchecked_arithmetic"), "Missing unchecked_arithmetic");
        assert!(names.contains(&"unchecked_division"), "Missing unchecked_division");
    }

    #[test]
    fn test_scan_body_returns_sorted_by_location() {
        // Two blocks, each with one finding -- should be sorted by block id
        let body = make_body(
            vec![
                local(0, Ty::Unit, None),
                local(1, Ty::i32(), Some("a")),
                local(2, Ty::i32(), Some("b")),
                local(3, Ty::i32(), None),
                local(4, Ty::i32(), None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            2,
        );

        let matches = scan_body(&body);
        for window in matches.windows(2) {
            let a_key = (window[0].block_id.0, window[0].stmt_index.unwrap_or(usize::MAX));
            let b_key = (window[1].block_id.0, window[1].stmt_index.unwrap_or(usize::MAX));
            assert!(a_key <= b_key, "Results should be sorted by location");
        }
    }

    #[test]
    fn test_scan_body_empty_body_returns_empty() {
        let body = make_body(vec![], vec![], 0);
        let matches = scan_body(&body);
        assert!(matches.is_empty());
    }

    #[test]
    fn test_scan_body_clean_function_returns_empty() {
        // A fully checked midpoint function: CheckedAdd + assert, Div by const
        // The Div by constant is still flagged by our conservative scanner,
        // but the checked add is not.
        let body = make_body(
            vec![
                local(0, Ty::usize(), None),      // return
                local(1, Ty::usize(), Some("a")), // arg
                local(2, Ty::usize(), Some("b")), // arg
                local(3, Ty::Tuple(vec![Ty::usize(), Ty::Bool]), None),
                local(4, Ty::usize(), None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            2,
        );

        let matches = scan_body(&body);
        // No unchecked arithmetic (CheckedBinaryOp is fine)
        // No unchecked indexing
        // No unchecked division (no Div op in this cleaned-up version)
        // No use-after-move
        // No uninitialized read
        assert!(
            matches.is_empty(),
            "Fully checked function should have no findings, got: {matches:?}"
        );
    }
}
