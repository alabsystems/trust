// trust-transval: Core VC generation for translation validation
//
// Generates refinement verification conditions between source (pre-optimization)
// and target (post-optimization) MIR functions. This is the authoritative
// implementation — trust_vcgen/translation_validation.rs delegates here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{
    BasicBlock,
    BlockId,
    // Translation validation types from trust-types.
    CheckKind,
    Formula,
    Operand,
    Place,
    RefinementVc,
    RefinementVcToVc,
    Rvalue,
    SimulationRelation,
    Sort,
    SortFromTy,
    Statement,
    Terminator,
    TranslationCheck,
    TranslationValidationError,
    Ty,
    UnOp,
    VerifiableFunction,
};

fn definite_refinement_violation() -> Formula {
    // VC convention is SAT = violation, UNSAT = proved. Structural mismatches
    // are known violations unless a later precise proof discharges them.
    Formula::Bool(true)
}

/// Generate refinement verification conditions between a source and target function.
///
/// The source is the original (pre-optimization) MIR, and the target is the
/// optimized or compiled version. The simulation relation maps source program
/// points to target program points.
///
/// Returns VCs that, when all UNSAT, prove the target refines the source.
pub fn generate_refinement_vcs(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    // Validate inputs.
    if source.body.blocks.is_empty() {
        return Err(TranslationValidationError::EmptyBody(source.name.clone()));
    }
    if target.body.blocks.is_empty() {
        return Err(TranslationValidationError::EmptyBody(target.name.clone()));
    }
    if source.body.arg_count != target.body.arg_count {
        return Err(TranslationValidationError::SignatureMismatch {
            source_args: source.body.arg_count,
            target_args: target.body.arg_count,
        });
    }

    relation.validate(source, target)?;

    let mut vcs = Vec::new();

    // 1. Control flow preservation.
    vcs.extend(check_control_flow_preservation(source, target, relation)?);

    // 2. Data flow preservation.
    vcs.extend(check_data_flow_preservation(source, target, relation)?);

    // 3. Return value preservation.
    vcs.extend(check_return_value_preservation(source, target, relation)?);

    // 4. Termination preservation.
    vcs.extend(check_termination_preservation(source, target, relation)?);

    Ok(vcs)
}

/// Check that the target preserves the control flow structure of the source.
///
/// For each source block that has a conditional terminator, verify that the
/// target's corresponding block branches to the corresponding target of each
/// source successor.
pub(crate) fn check_control_flow_preservation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        let source_succs = trust_types::block_successors_list(&source_block.terminator);
        if source_succs.is_empty() {
            continue;
        }

        let target_block_id = relation
            .block_map
            .get(&source_block.id)
            .ok_or(TranslationValidationError::UnmappedBlock(source_block.id))?;

        let target_block = target_blocks.get(target_block_id).ok_or(
            TranslationValidationError::InvalidRelation(format!(
                "target block {:?} not found",
                target_block_id
            )),
        )?;

        let target_succs = trust_types::block_successors_list(&target_block.terminator);

        // For each source successor, the corresponding target successor must
        // be reachable from the mapped target block.
        for source_succ in &source_succs {
            if let Some(expected_target_succ) = relation.block_map.get(source_succ) {
                // Build a VC: target block reaches expected_target_succ.
                // Formula: NOT(target_succs contains expected_target_succ)
                // If UNSAT, the successor is preserved. If SAT, it's missing.
                let succ_preserved = target_succs.contains(expected_target_succ);

                if !succ_preserved {
                    // Generate a VC that the target's semantics still reach the
                    // expected successor (the optimization may have restructured
                    // the CFG but preserved reachability).
                    let formula = definite_refinement_violation();

                    vcs.push(RefinementVc {
                        check: TranslationCheck {
                            source_point: source_block.id,
                            target_point: *target_block_id,
                            kind: CheckKind::ControlFlow,
                            formula,
                            description: format!(
                                "source block {:?} -> {:?} must be preserved in target {:?}",
                                source_block.id, source_succ, target_block_id
                            ),
                        },
                        source_function: source.name.clone(),
                        target_function: target.name.clone(),
                    });
                }
            }
        }
    }

    Ok(vcs)
}

/// Check that assignments in the target preserve the data flow of the source.
///
/// For each assignment in a source block, verify that the corresponding target
/// block computes an equivalent value for the mapped variable.
pub(crate) fn check_data_flow_preservation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        let target_block_id = relation
            .block_map
            .get(&source_block.id)
            .ok_or(TranslationValidationError::UnmappedBlock(source_block.id))?;

        let target_block = target_blocks.get(target_block_id).ok_or(
            TranslationValidationError::InvalidRelation(format!(
                "target block {:?} not found",
                target_block_id
            )),
        )?;

        for source_stmt in &source_block.stmts {
            if let Statement::Assign { place: source_place, rvalue: source_rvalue, .. } =
                source_stmt
            {
                // Build source-side expression.
                let source_expr = rvalue_to_formula(source, source_rvalue)?;

                // Prefer explicit expression maps, then inspect target assignments before
                // falling back to whole-local identity mappings. This keeps malformed
                // target MIR from being hidden by a weak/default relation.
                let target_expr = if let Some(mapped) =
                    relation.expression_map.get(&source_place.local)
                {
                    mapped.clone()
                } else if let Some((target_place, rvalue)) =
                    find_assignment_to(target_block, source_place.local, relation)
                {
                    if !target_place.projections.is_empty() {
                        return Err(unsupported_mir(
                            "place projection",
                            format!(
                                "assignment destination local {} has unsupported projections {:?}",
                                target_place.local, target_place.projections
                            ),
                        ));
                    }
                    rvalue_to_formula(target, rvalue)?
                } else if let Some(mapped) = relation.resolve_variable(source_place.local, target) {
                    mapped
                } else {
                    continue; // Dead code elimination removed this assignment.
                };

                // Refinement VC: source_expr != target_expr => violation.
                // We check SAT of: NOT(source_expr == target_expr).
                // UNSAT means they are always equal (refined).
                let formula = Formula::Not(Box::new(Formula::Eq(
                    Box::new(source_expr),
                    Box::new(target_expr),
                )));

                vcs.push(RefinementVc {
                    check: TranslationCheck {
                        source_point: source_block.id,
                        target_point: *target_block_id,
                        kind: CheckKind::DataFlow,
                        formula,
                        description: format!(
                            "assignment to local {} in source {:?} must be preserved in target {:?}",
                            source_place.local, source_block.id, target_block_id
                        ),
                    },
                    source_function: source.name.clone(),
                    target_function: target.name.clone(),
                });
            }
        }
    }

    Ok(vcs)
}

/// Check that the target's return value matches the source's return value.
///
/// For each Return terminator in the source, verify that the target's
/// corresponding block also returns and that _0 (the return local) holds
/// an equivalent value.
pub(crate) fn check_return_value_preservation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        if !matches!(source_block.terminator, Terminator::Return) {
            continue;
        }

        let target_block_id = relation
            .block_map
            .get(&source_block.id)
            .ok_or(TranslationValidationError::UnmappedBlock(source_block.id))?;

        let target_block = target_blocks.get(target_block_id).ok_or(
            TranslationValidationError::InvalidRelation(format!(
                "target block {:?} not found",
                target_block_id
            )),
        )?;

        // Both should return.
        if !matches!(target_block.terminator, Terminator::Return) {
            let formula = definite_refinement_violation();
            vcs.push(RefinementVc {
                check: TranslationCheck {
                    source_point: source_block.id,
                    target_point: *target_block_id,
                    kind: CheckKind::ReturnValue,
                    formula,
                    description: format!(
                        "source {:?} returns but target {:?} does not",
                        source_block.id, target_block_id
                    ),
                },
                source_function: source.name.clone(),
                target_function: target.name.clone(),
            });
            continue;
        }

        // Return local is always _0. It must be explicitly mapped by the
        // simulation relation; otherwise a malformed relation can silently
        // compare the source return to a synthetic target `_0` fallback.
        let source_ret = local_to_formula(source, 0);
        let target_ret = relation.resolve_variable(0, target).ok_or_else(|| {
            TranslationValidationError::InvalidRelation(
                "source return local _0 is not mapped in the simulation relation".to_string(),
            )
        })?;

        // VC: NOT(source_ret == target_ret). UNSAT => return values always match.
        let formula =
            Formula::Not(Box::new(Formula::Eq(Box::new(source_ret), Box::new(target_ret))));

        vcs.push(RefinementVc {
            check: TranslationCheck {
                source_point: source_block.id,
                target_point: *target_block_id,
                kind: CheckKind::ReturnValue,
                formula,
                description: format!(
                    "return value at source {:?} must equal return value at target {:?}",
                    source_block.id, target_block_id
                ),
            },
            source_function: source.name.clone(),
            target_function: target.name.clone(),
        });
    }

    Ok(vcs)
}

/// Check that the target preserves termination behavior.
///
/// If the source has a loop (detected via back-edges), the target's
/// corresponding blocks must also form a loop or have been validly
/// unrolled/eliminated.
pub(crate) fn check_termination_preservation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();

    // Detect loops in source via back-edges.
    let source_loops = trust_types::detect_back_edges(&source.body);
    let target_loops = trust_types::detect_back_edges(&target.body);

    for (header, latch) in &source_loops {
        let target_header = relation.block_map.get(header);
        let target_latch = relation.block_map.get(latch);

        match (target_header, target_latch) {
            (Some(th), Some(tl)) => {
                // Check that the target also has a back-edge from tl to th,
                // or that the loop was validly eliminated.
                let has_target_loop = target_loops.iter().any(|(h, l)| h == th && l == tl);

                if !has_target_loop {
                    // The loop was eliminated in the target. Generate a VC that
                    // the elimination is valid (the loop body's effect is preserved).
                    let formula = definite_refinement_violation();

                    vcs.push(RefinementVc {
                        check: TranslationCheck {
                            source_point: *header,
                            target_point: *th,
                            kind: CheckKind::Termination,
                            formula,
                            description: format!(
                                "source loop {:?}->{:?} eliminated in target; must preserve semantics",
                                header, latch
                            ),
                        },
                        source_function: source.name.clone(),
                        target_function: target.name.clone(),
                    });
                }
            }
            _ => {
                // Loop header or latch not mapped. This means the optimization
                // removed these blocks entirely. Generate a VC.
                let th = target_header.copied().unwrap_or(BlockId(0));
                let formula = definite_refinement_violation();

                vcs.push(RefinementVc {
                    check: TranslationCheck {
                        source_point: *header,
                        target_point: th,
                        kind: CheckKind::Termination,
                        formula,
                        description: format!(
                            "source loop {:?}->{:?} has unmapped blocks in target",
                            header, latch
                        ),
                    },
                    source_function: source.name.clone(),
                    target_function: target.name.clone(),
                });
            }
        }
    }

    Ok(vcs)
}

// --- Internal helpers ---

/// Convert an Rvalue to a Formula for comparison.
///
/// Uses trust_vcgen helpers (`operand_to_formula`, `try_binop_to_formula`) for
/// consistent encoding with the rest of the verification pipeline.
fn rvalue_to_formula(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
) -> Result<Formula, TranslationValidationError> {
    match rvalue {
        Rvalue::Use(op) => operand_to_formula(func, op),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            // Delegate to the shared CHC binop lowering, which handles
            // bitwise ops correctly via bitvector formulas.
            let l = operand_to_formula(func, lhs)?;
            let r = operand_to_formula(func, rhs)?;
            // Pass signedness for correct right-shift selection.
            let ty = trust_vcgen::operand_ty(func, lhs);
            // Trust: BitAnd/BitOr/BitXor on BOOL operands are LOGICAL connectives,
            // not bitvector ops. Lowering them via the integer path
            // (chc::try_binop_to_formula → BvAnd/BvOr) makes a downstream refinement
            // `Eq` compare a Bool against a BitVec — a sort mismatch the in-process
            // ay backend DECLINES (Unknown), silently dropping a real port-vs-
            // reference divergence (e.g. a predicate that differs only by an extra
            // `&&`, as in ATERM-FINDINGS class 4). Emit the Bool connective so the
            // obligation actually reaches the solver. Mirrors the Bool path already
            // taken in trust-vcgen guards.rs (`BitAnd => Formula::And`).
            if matches!(ty.as_ref(), Some(trust_types::Ty::Bool)) {
                use trust_types::BinOp;
                match op {
                    BinOp::BitAnd => return Ok(Formula::And(vec![l, r])),
                    BinOp::BitOr => return Ok(Formula::Or(vec![l, r])),
                    // bool xor: a ^ b ≡ ¬(a = b)
                    BinOp::BitXor => {
                        return Ok(Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r)))));
                    }
                    _ => {}
                }
            }
            let width = ty.as_ref().and_then(|t| t.int_width());
            let signed = ty.as_ref().is_some_and(|t| t.is_signed());
            // Trust (TCB hardening): fail-closed on an unsupported BinOp — the
            // verifier core must never crash on unexpected MIR. An unsupported op
            // becomes an unsupported-MIR obligation (Unknown), not a compiler abort.
            trust_vcgen::chc::try_binop_to_formula(*op, l, r, width, signed).map_err(|e| {
                unsupported_mir("Rvalue::BinaryOp", &format!("unsupported BinOp lowering: {e}"))
            })
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => Ok(Formula::Neg(Box::new(operand_to_formula(func, op)?))),
        Rvalue::UnaryOp(UnOp::Not, op) => Ok(Formula::Not(Box::new(operand_to_formula(func, op)?))),
        Rvalue::UnaryOp(UnOp::PtrMetadata, _) => Err(unsupported_mir(
            "Rvalue::UnaryOp(PtrMetadata)",
            "pointer metadata extraction is not modeled by translation validation",
        )),
        Rvalue::Cast(_, ty) => Err(unsupported_mir(
            "Rvalue::Cast",
            format!("cast semantics to {ty:?} are not modeled by translation validation"),
        )),
        Rvalue::Unsupported { kind, detail, .. } => {
            Err(unsupported_mir(kind.clone(), detail.clone()))
        }
        Rvalue::Ref { .. }
        | Rvalue::Aggregate(..)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::Repeat(..)
        | Rvalue::AddressOf(..)
        | Rvalue::CopyForDeref(_) => Err(unsupported_mir(
            rvalue_kind(rvalue),
            format!("{rvalue:?} is not modeled by translation validation"),
        )),
        _ => Err(unsupported_mir(
            "Rvalue::<unknown>",
            "non-exhaustive rvalue variant is not modeled by translation validation",
        )),
    }
}

fn operand_to_formula(
    func: &VerifiableFunction,
    operand: &Operand,
) -> Result<Formula, TranslationValidationError> {
    match operand {
        Operand::Unsupported { kind, detail } => Err(unsupported_mir(kind.clone(), detail.clone())),
        Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_) | Operand::Symbolic(_) => {
            Ok(trust_vcgen::operand_to_formula(func, operand))
        }
        _ => Err(unsupported_mir(
            "Operand::<unknown>",
            "non-exhaustive operand variant is not modeled by translation validation",
        )),
    }
}

fn unsupported_mir(
    kind: impl Into<String>,
    detail: impl Into<String>,
) -> TranslationValidationError {
    TranslationValidationError::InvalidRelation(format!(
        "unsupported MIR in translation validation: {}: {}",
        kind.into(),
        detail.into()
    ))
}

fn rvalue_kind(rvalue: &Rvalue) -> &'static str {
    match rvalue {
        Rvalue::Ref { .. } => "Rvalue::Ref",
        Rvalue::Aggregate(..) => "Rvalue::Aggregate",
        Rvalue::Discriminant(_) => "Rvalue::Discriminant",
        Rvalue::Len(_) => "Rvalue::Len",
        Rvalue::Repeat(..) => "Rvalue::Repeat",
        Rvalue::AddressOf(..) => "Rvalue::AddressOf",
        Rvalue::CopyForDeref(_) => "Rvalue::CopyForDeref",
        _ => "Rvalue::<unknown>",
    }
}

/// Convert a local variable to a formula.
fn local_to_formula(func: &VerifiableFunction, local_idx: usize) -> Formula {
    let name = func
        .body
        .locals
        .get(local_idx)
        .and_then(|d| d.name.as_deref())
        .unwrap_or(&format!("_{}", local_idx))
        .to_string();

    let sort = func
        .body
        .locals
        .get(local_idx)
        .map(|d| match &d.ty {
            Ty::Bool => Sort::Bool,
            Ty::Int { .. } => Sort::Int,
            other => Sort::from_ty(other),
        })
        .unwrap_or(Sort::Int);

    Formula::Var(name, sort)
}

/// Find an assignment to a target local in a target block, using the variable map.
fn find_assignment_to<'a>(
    block: &'a BasicBlock,
    source_local: usize,
    relation: &SimulationRelation,
) -> Option<(&'a Place, &'a Rvalue)> {
    let target_local = relation.variable_map.get(&source_local)?;
    block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { place, rvalue, .. } if place.local == *target_local => {
            Some((place, rvalue))
        }
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Build a simple "add two i32s" function for testing.
    fn simple_add_function(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{}", name),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
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

    fn unsupported_rvalue_function(name: &str, rvalue: Rvalue) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{}", name),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Array { elem: Box::new(Ty::i32()), len: 4 },
                        name: Some("arr".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::i32(), name: Some("tmp".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue,
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn assert_unsupported_rvalue_fails_closed(rvalue: Rvalue, expected_kind: &str) {
        let source = unsupported_rvalue_function("source", rvalue.clone());
        let target = unsupported_rvalue_function("target", rvalue);
        let rel = infer_identity_relation(&source, &target).unwrap();

        let err = generate_refinement_vcs(&source, &target, &rel)
            .expect_err("unsupported MIR must not generate proof VCs");
        let msg = err.to_string();
        assert!(
            msg.contains("unsupported MIR in translation validation"),
            "error must be explicit: {msg}"
        );
        assert!(msg.contains(expected_kind), "error should identify {expected_kind}: {msg}");
    }

    #[test]
    fn test_generate_refinement_vcs_identical_functions() {
        let source = simple_add_function("source");
        let target = simple_add_function("target");
        let rel = infer_identity_relation(&source, &target).unwrap();

        let vcs = generate_refinement_vcs(&source, &target, &rel).unwrap();
        assert!(!vcs.is_empty(), "identical functions should still produce VCs");

        let cf_vcs: Vec<_> =
            vcs.iter().filter(|vc| vc.check.kind == CheckKind::ControlFlow).collect();
        assert!(cf_vcs.is_empty(), "identical CFGs should have no control flow violations");
    }

    #[test]
    fn test_generate_refinement_vcs_signature_mismatch() {
        let source = simple_add_function("source");
        let mut target = simple_add_function("target");
        target.body.arg_count = 3;

        let rel = SimulationRelation::identity(&source);
        let err = generate_refinement_vcs(&source, &target, &rel).unwrap_err();
        assert!(matches!(
            err,
            TranslationValidationError::SignatureMismatch { source_args: 2, target_args: 3 }
        ));
    }

    #[test]
    fn test_generate_refinement_vcs_empty_source() {
        let mut source = simple_add_function("source");
        source.body.blocks.clear();
        let target = simple_add_function("target");
        let rel = SimulationRelation::new();

        let err = generate_refinement_vcs(&source, &target, &rel).unwrap_err();
        assert!(matches!(err, TranslationValidationError::EmptyBody(_)));
    }

    #[test]
    fn structural_return_mismatch_is_sat_violation() {
        let source = simple_add_function("source");
        let mut target = simple_add_function("target");
        target.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
        target.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        let mut rel = SimulationRelation::new();
        rel.block_map.insert(BlockId(0), BlockId(0));
        for local in &source.body.locals {
            rel.variable_map.insert(local.index, local.index);
        }

        let vcs = generate_refinement_vcs(&source, &target, &rel).unwrap();
        let return_vc = vcs
            .iter()
            .find(|vc| {
                vc.check.kind == CheckKind::ReturnValue && vc.check.formula == Formula::Bool(true)
            })
            .expect("return mismatch must be a satisfiable violation");
        assert!(return_vc.check.description.contains("does not"));
    }

    #[test]
    fn return_value_requires_explicit_return_local_mapping() {
        let source = simple_add_function("source");
        let target = simple_add_function("target");
        let mut rel = SimulationRelation::new();
        rel.block_map.insert(BlockId(0), BlockId(0));
        rel.variable_map.insert(1, 1);
        rel.variable_map.insert(2, 2);
        rel.variable_map.insert(3, 3);

        let err = generate_refinement_vcs(&source, &target, &rel)
            .expect_err("missing return-local mapping must fail closed");
        let msg = err.to_string();
        assert!(msg.contains("invalid simulation relation"), "{msg}");
        assert!(msg.contains("return local _0"), "{msg}");
    }

    #[test]
    fn structural_missing_successor_is_sat_violation() {
        let mut source = simple_add_function("source");
        source.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
        source.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        let mut target = simple_add_function("target");
        target.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        let rel = infer_identity_relation(&source, &target).unwrap();

        let vcs = generate_refinement_vcs(&source, &target, &rel).unwrap();
        assert!(
            vcs.iter().any(|vc| {
                vc.check.kind == CheckKind::ControlFlow && vc.check.formula == Formula::Bool(true)
            }),
            "missing CFG successor must be a satisfiable violation"
        );
    }

    #[test]
    fn structural_loop_elimination_is_sat_violation() {
        let mut source = simple_add_function("source");
        source.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(0)) },
        ];

        let mut target = simple_add_function("target");
        target.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];
        let rel = infer_identity_relation(&source, &target).unwrap();

        let vcs = generate_refinement_vcs(&source, &target, &rel).unwrap();
        assert!(
            vcs.iter().any(|vc| {
                vc.check.kind == CheckKind::Termination && vc.check.formula == Formula::Bool(true)
            }),
            "removed source loop must be a satisfiable violation until precisely proved"
        );
    }

    #[test]
    fn test_refinement_vc_to_vc() {
        let rvc = RefinementVc {
            check: TranslationCheck {
                source_point: BlockId(0),
                target_point: BlockId(0),
                kind: CheckKind::DataFlow,
                formula: Formula::Bool(true),
                description: "test check".into(),
            },
            source_function: "source_fn".into(),
            target_function: "target_fn".into(),
        };

        let vc = rvc.to_vc();
        assert_eq!(vc.function, "target_fn");
        assert!(matches!(vc.kind, VcKind::RefinementViolation { .. }));
    }

    #[test]
    fn unsupported_len_does_not_prove_equivalence() {
        assert_unsupported_rvalue_fails_closed(Rvalue::Len(Place::local(2)), "Rvalue::Len");
    }

    #[test]
    fn unsupported_aggregate_does_not_prove_equivalence() {
        assert_unsupported_rvalue_fails_closed(
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(3))],
            ),
            "Rvalue::Aggregate",
        );
    }

    #[test]
    fn unsupported_cast_like_rvalues_do_not_prove_equivalence() {
        assert_unsupported_rvalue_fails_closed(
            Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i64()),
            "Rvalue::Cast",
        );
        assert_unsupported_rvalue_fails_closed(
            Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
            "Rvalue::UnaryOp(PtrMetadata)",
        );
    }

    #[test]
    fn unsupported_operand_does_not_prove_equivalence() {
        assert_unsupported_rvalue_fails_closed(
            Rvalue::Use(Operand::Unsupported {
                kind: "Operand::Opaque".into(),
                detail: "opaque test operand".into(),
            }),
            "Operand::Opaque",
        );
    }

    #[test]
    fn target_unsupported_rvalue_not_hidden_by_variable_map() {
        let source = simple_add_function("source");
        let mut target = simple_add_function("target");
        target.body.blocks[0].stmts[0] = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Aggregate(AggregateKind::Tuple, vec![]),
            span: SourceSpan::default(),
        };
        let rel = infer_identity_relation(&source, &target).unwrap();

        let err = generate_refinement_vcs(&source, &target, &rel)
            .expect_err("unsupported target MIR must not be hidden by variable_map");
        let msg = err.to_string();
        assert!(
            msg.contains("unsupported MIR in translation validation"),
            "error must be explicit: {msg}"
        );
        assert!(msg.contains("Rvalue::Aggregate"), "error should identify aggregate: {msg}");
    }

    #[test]
    fn target_projected_assignment_not_treated_as_whole_local_assignment() {
        let source = simple_add_function("source");
        let mut target = simple_add_function("target");
        target.body.blocks[0].stmts[0] = Statement::Assign {
            place: Place::field(3, 0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        let rel = infer_identity_relation(&source, &target).unwrap();

        let err = generate_refinement_vcs(&source, &target, &rel)
            .expect_err("projected target assignment must fail closed");
        let msg = err.to_string();
        assert!(
            msg.contains("unsupported MIR in translation validation"),
            "error must be explicit: {msg}"
        );
        assert!(msg.contains("place projection"), "error should identify projection: {msg}");
    }
}
