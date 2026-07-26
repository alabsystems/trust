use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Sort, SourceSpan, Terminator, Ty,
    VcKind, VerifiableBody, VerifiableFunction,
};

use super::{
    generate_callsite_precondition_vcs, generate_callsite_precondition_vcs_attributed,
    generate_vcs_with_discharge, generate_vcs_with_discharge_and_summaries,
};
use crate::modular::{FunctionSummary, SummaryDatabase};

fn caller_to_reciprocal() -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "example::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("_2".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "example::reciprocal".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn caller_to_reciprocal_with_body_vc() -> VerifiableFunction {
    let mut func = caller_to_reciprocal();
    // A false postcondition yields a concrete violation VC. It makes the
    // regression non-vacuous even though the function body only contains a
    // call and return.
    func.postconditions.push(Formula::Bool(false));
    func
}

fn caller_to_slice_sink() -> VerifiableFunction {
    let slice_ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    VerifiableFunction {
        name: "slice_caller".to_string(),
        def_path: "example::slice_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: slice_ty, name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("_2".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "example::slice_sink".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn summaries_emit_unproved_callsite_preconditions_with_actual_args() {
    let func = caller_to_reciprocal();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new("example::reciprocal")
            .with_param_names(vec!["n".to_string()])
            .with_precondition(Formula::Gt(
                Box::new(Formula::var("n", Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
    );

    let (solver_vcs, discharged) = generate_vcs_with_discharge_and_summaries(&func, &summaries);

    assert!(discharged.is_empty());
    let pre_vcs: Vec<_> =
        solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).collect();
    assert_eq!(pre_vcs.len(), 1);
    assert!(
        matches!(&pre_vcs[0].kind, VcKind::Precondition { callee } if callee == "example::reciprocal")
    );
    assert_eq!(
        pre_vcs[0].formula,
        Formula::Not(Box::new(Formula::Gt(
            Box::new(Formula::var("x", Sort::Int)),
            Box::new(Formula::Int(0)),
        )))
    );
}

#[test]
fn direct_summary_slice_length_rebinds_to_actual_argument() {
    let func = caller_to_slice_sink();
    let slice_ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new("example::slice_sink")
            .with_param_names(vec!["xs".to_string()])
            .with_param_types(vec![slice_ty])
            .with_precondition(Formula::Gt(
                Box::new(Formula::var("xs__slice_len", Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
    );

    let vcs = generate_callsite_precondition_vcs(&func, &summaries);
    let pre = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .expect("the caller must receive one explicit precondition obligation");
    let free = pre.formula.free_variables();
    assert!(free.contains("s__slice_len"), "actual slice length missing: {pre:#?}");
    assert!(
        !free.contains("xs__slice_len"),
        "formal slice length must not remain free after exact typed substitution: {pre:#?}",
    );
}

#[test]
fn arithmetic_summary_requires_fail_closed_in_all_callsite_producers() {
    let func = caller_to_reciprocal();
    let arithmetic = Formula::Gt(
        Box::new(Formula::Add(
            Box::new(Formula::var("n", Sort::Int)),
            Box::new(Formula::Int(1)),
        )),
        Box::new(Formula::var("n", Sort::Int)),
    );
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new("example::reciprocal")
            .with_param_names(vec!["n".to_string()])
            .with_precondition(arithmetic),
    );

    let ordinary = generate_callsite_precondition_vcs(&func, &summaries);
    let attributed = generate_callsite_precondition_vcs_attributed(&func, &summaries);
    let modular = crate::modular::generate_modular_vcs(&func, &summaries);
    for (lane, vcs) in [
        ("ordinary", ordinary),
        ("attributed", attributed.into_iter().map(|(vc, _, _)| vc).collect()),
        ("modular", modular),
    ] {
        assert_eq!(vcs.len(), 1, "{lane} must retain one explicit row: {vcs:#?}");
        assert!(
            matches!(&vcs[0].kind, VcKind::UnsupportedMir { detail, .. }
                if detail.contains("example::reciprocal")),
            "{lane} must identify the exact rejected callee: {vcs:#?}",
        );
        assert_eq!(vcs[0].formula, Formula::Bool(true), "{lane} must be non-provable");
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })),
            "{lane} must not emit a solver-capable arithmetic precondition",
        );
    }
}

#[test]
fn arithmetic_summary_postcondition_is_never_injected() {
    let func = caller_to_reciprocal();
    let summary = FunctionSummary::new("example::reciprocal")
        .with_param_names(vec!["n".to_string()])
        .with_postcondition(Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::var("_0", Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::var("_0", Sort::Int)),
        ));
    assert!(
        super::rebind_callee_postconditions(
            &func,
            &[Operand::Copy(Place::local(1))],
            &Place::local(2),
            &summary,
        )
        .is_empty(),
        "an arithmetic Ensures must never become a caller assumption",
    );
}

// Trust (cross-crate precondition discharge — fail-closed regression):
//
// A contracted callee summary built for a NON-LOCAL `#[requires]` reaches the
// SAME callsite-discharge path as a local one (the summary is keyed by
// `safe_def_path_str`, exactly as the MIR call terminator's `func` name is).
// This guards the fail-closed fallback: if the actual-arg -> formal mapping
// cannot be built (here: `param_names` empty, which is what an empty
// cross-crate `fn_arg_idents` degrades to) while the call passes arguments,
// the discharge path MUST emit a fail-closed obligation — a `Bool(true)`
// `UnsupportedMir` VC, preclassified to `Unknown` — never silently zero
// obligations, which would be the original cross-crate FAIL-OPEN.
#[test]
fn summary_with_precondition_but_unbuildable_arg_mapping_fails_closed() {
    use trust_types::VerificationResult;

    let func = caller_to_reciprocal(); // calls reciprocal(x) with ONE arg
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        // No param names (empty `fn_arg_idents` cross-crate) but a real
        // precondition — the arg mapping cannot be built.
        FunctionSummary::new("example::reciprocal").with_precondition(Formula::Gt(
            Box::new(Formula::var("n", Sort::Int)),
            Box::new(Formula::Int(0)),
        )),
    );

    let (solver_vcs, discharged) = generate_vcs_with_discharge_and_summaries(&func, &summaries);

    // The fail-closed obligation is preclassified to `Unknown` and lands in
    // `discharged` (not `solver_vcs`): an `UnsupportedMir{SummaryArityMismatch}`
    // VC with a `Bool(true)` violation formula.
    let fail_closed: Vec<_> = discharged
        .iter()
        .filter(|(vc, _)| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "SummaryArityMismatch"))
        .collect();
    assert_eq!(
        fail_closed.len(),
        1,
        "an unbuildable arg mapping must emit a fail-closed obligation, not zero VCs"
    );
    let (vc, result) = fail_closed[0];
    assert_eq!(vc.formula, Formula::Bool(true));
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "fail-closed obligation must classify as Unknown, never Proved: {result:?}"
    );

    // It must NOT silently emit a (vacuously dischargeable) Precondition VC.
    assert!(
        !solver_vcs.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })),
        "must not emit a precondition VC from an unbuildable substitution"
    );
}

// Trust (R1 guarded-caller discharge): `sigma_actual_stable_copy_root` must fold
// an argument temp `_3 = copy x; f(move _3)` to the STABLE, source-named root `x`,
// so σ names the argument the same way the caller's dominating guard does. A
// reseated temp, an `&mut`-mutated (unstable) root, or a nameless root must NOT
// fold — σ then keeps the opaque temp name and the caller obligation fails closed.
fn caller_passing_copy_of_param(mutate_source: bool) -> VerifiableFunction {
    use trust_types::{BinOp, Rvalue, Statement};
    // locals: _0 ret, _1 = x (param, u32), _2 = call dest, _3 = temp copy of x.
    let mut stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }];
    if mutate_source {
        // Reassign the SOURCE `x` in place (`x = x + 0`) — makes `_1` unstable
        // (two whole-local assigns), so the fold must decline (fail-closed).
        stmts.push(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(trust_types::ConstValue::Uint(0, 32)),
            ),
            span: SourceSpan::default(),
        });
    }
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "example::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("_2".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("_3".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "example::reciprocal".to_string(),
                        args: vec![Operand::Move(Place::local(3))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn sigma_folds_stable_copy_chain_to_source_name() {
    // `_3 = copy x; reciprocal(move _3)` with a stable `x` → σ names the arg `x`,
    // so a caller guard over `x` can discharge the callee precondition.
    let func = caller_passing_copy_of_param(false);
    let root = super::sigma_actual_stable_copy_root(&func, &Operand::Move(Place::local(3)));
    assert_eq!(root, Some(Place::local(1)), "stable copy-of-param must fold to source local");
    // And the resulting σ formula names it `x` (matching the guard's read).
    let sigma = super::sigma_actual_formula(&func, "n", &Operand::Move(Place::local(3)));
    assert_eq!(sigma, Formula::var("x", Sort::Int));
}

#[test]
fn sigma_does_not_fold_when_source_is_reassigned() {
    // The source `x` is reassigned before the call → NOT stable → NO fold, so σ
    // keeps the opaque temp name `_3` and the caller obligation fails closed.
    let func = caller_passing_copy_of_param(true);
    let root = super::sigma_actual_stable_copy_root(&func, &Operand::Move(Place::local(3)));
    assert_eq!(root, None, "an unstable (reassigned) source must NOT fold — fail-closed");
    let sigma = super::sigma_actual_formula(&func, "n", &Operand::Move(Place::local(3)));
    assert_eq!(sigma, Formula::var("_3", Sort::Int));
}

// ---------------------------------------------------------------------
// R1 guarded-caller discharge: value-preserving-cast σ roots + the
// caller's own stable preconditions as flat guard conjuncts.
// ---------------------------------------------------------------------

/// `lo <= hi` over the caller's formals (entry names) — the shared shape of
/// the caller `#[requires]` AND (post-σ-rooting) the callee's substituted P.
fn lo_le_hi() -> Formula {
    Formula::Le(
        Box::new(Formula::var("lo", Sort::Int)),
        Box::new(Formula::var("hi", Sort::Int)),
    )
}

/// The `range_usize` shape:
///   #[requires(lo <= hi)]
///   fn range_usize(lo: usize, hi: usize) {
///       let lo_i = lo as i128;          // _3 = Cast(copy _1, i128)  (widening)
///       let hi_i = hi as i128;          // _4 = Cast(copy _2, i128)
///       range_i128(lo_i, hi_i)          // _5 = copy _3; _6 = copy _4; call
///   }
/// With `reassign_lo`, appends `lo = lo + 0` — the formal is REASSIGNED, so
/// both the σ cast-root fold and the own-precondition conjoin must decline.
fn caller_with_widening_casts(reassign_lo: bool) -> VerifiableFunction {
    use trust_types::{BinOp, Rvalue, Statement};
    let cast = |dst: usize, src: usize| Statement::Assign {
        place: Place::local(dst),
        rvalue: Rvalue::Cast(Operand::Copy(Place::local(src)), Ty::i128()),
        span: SourceSpan::default(),
    };
    let copy = |dst: usize, src: usize| Statement::Assign {
        place: Place::local(dst),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(src))),
        span: SourceSpan::default(),
    };
    let mut stmts = vec![cast(3, 1), cast(4, 2), copy(5, 3), copy(6, 4)];
    if reassign_lo {
        stmts.push(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(trust_types::ConstValue::Uint(0, 64)),
            ),
            span: SourceSpan::default(),
        });
    }
    VerifiableFunction {
        name: "range_usize".to_string(),
        def_path: "example::range_usize".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) },
                LocalDecl { index: 3, ty: Ty::i128(), name: Some("lo_i".into()) },
                LocalDecl { index: 4, ty: Ty::i128(), name: Some("hi_i".into()) },
                LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                LocalDecl { index: 6, ty: Ty::i128(), name: Some("_6".into()) },
                LocalDecl { index: 7, ty: Ty::i128(), name: Some("_7".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "example::range_i128".to_string(),
                        args: vec![
                            Operand::Move(Place::local(5)),
                            Operand::Move(Place::local(6)),
                        ],
                        dest: Place::local(7),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![lo_le_hi()],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Callee `#[requires(lo <= hi)]` over ITS formals `lo`, `hi` (the cast
/// temps at the call site) — `example::range_i128`'s summary.
fn range_i128_summary_db() -> SummaryDatabase {
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new("example::range_i128")
            .with_param_names(vec!["lo".to_string(), "hi".to_string()])
            .with_precondition(lo_le_hi()),
    );
    summaries
}

#[test]
fn widening_cast_sigma_roots_and_caller_precondition_make_obligation_unsat_shaped() {
    let func = caller_with_widening_casts(false);

    // σ follows `_5 = copy lo_i; lo_i = lo as i128` (usize → i128 is a
    // provably value-preserving zero-extension) to the stable root `lo`.
    let root = super::sigma_actual_stable_copy_root(&func, &Operand::Move(Place::local(5)));
    assert_eq!(root, Some(Place::local(1)), "widening cast chain must fold to `lo`");

    let vcs = super::generate_callsite_precondition_vcs(&func, &range_i128_summary_db());
    let pre_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).collect();
    assert_eq!(pre_vcs.len(), 1);
    let Formula::And(conjuncts) = &pre_vcs[0].formula else {
        panic!("expected a flat And obligation, got {:?}", pre_vcs[0].formula);
    };
    // ¬P[σ] renders the callee formals as the ROOT source names (`lo`,
    // `hi`), NOT the temp names (`_5`, `_6` / `lo_i`, `hi_i`) …
    let not_p = Formula::Not(Box::new(lo_le_hi()));
    assert!(
        conjuncts.contains(&not_p),
        "¬P[σ] must be a direct conjunct over the root names: {conjuncts:?}"
    );
    // … and the caller's own `#[requires(lo <= hi)]` sits beside it as a
    // flat conjunct, so the obligation is UNSAT-shaped (P ∧ ¬P).
    assert!(
        conjuncts.contains(&lo_le_hi()),
        "the caller's stable precondition must be a direct conjunct: {conjuncts:?}"
    );
}

/// A NARROWING (or otherwise value-changing) cast must NOT be followed: σ
/// keeps the opaque temp name and the obligation fails closed.
fn caller_casting_param(from_ty: Ty, to_ty: Ty) -> VerifiableFunction {
    use trust_types::{Rvalue, Statement};
    // _2 (named `x_n`) = Cast(copy x, to_ty); _3 = copy _2; f(move _3).
    VerifiableFunction {
        name: "caster".to_string(),
        def_path: "example::caster".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: from_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: to_ty.clone(), name: Some("x_n".into()) },
                LocalDecl { index: 3, ty: to_ty.clone(), name: Some("_3".into()) },
                LocalDecl { index: 4, ty: to_ty.clone(), name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to_ty),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "example::sink".to_string(),
                        args: vec![Operand::Move(Place::local(3))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn sigma_declines_root_reassigned_via_call_destination() {
    // A WIDENING cast (usize→i128, followable in isolation) whose root
    // parameter `x` is reassigned by a CALL DESTINATION (`x = g()`) before
    // the cast. `local_is_never_written` scans only statement assigns and
    // `place_source_is_stable` admits ONE whole-local call-dest store (a
    // parameter's entry binding is not an explicit store), so without the
    // `local_has_call_dest_write` gate the fold would equate the temp with
    // a root whose value changed since entry — one SMT name for two values,
    // a false-discharge channel.
    let mut func = caller_casting_param(Ty::usize(), Ty::i128());
    func.body.blocks.insert(
        0,
        BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "example::reseat".to_string(),
                args: vec![],
                dest: Place::local(1), // reassigns the parameter `x`
                target: Some(BlockId(0)),
                span: SourceSpan::default(),
                atomic: None,
            },
        },
    );
    assert!(super::local_has_call_dest_write(&func, 1));
    assert_eq!(
        super::sigma_actual_stable_copy_root(&func, &Operand::Move(Place::local(3))),
        None,
        "a call-dest-reassigned root must NOT be folded — fail-closed"
    );
}

#[test]
fn sigma_does_not_follow_narrowing_or_sign_changing_casts() {
    // i128 → usize: NARROWING (truncation mod 2^64 can change the value).
    let narrowing = caller_casting_param(Ty::i128(), Ty::usize());
    assert_eq!(
        super::sigma_actual_stable_copy_root(&narrowing, &Operand::Move(Place::local(3))),
        None,
        "a narrowing cast must NOT be followed — fail-closed"
    );
    assert_eq!(
        super::sigma_actual_formula(&narrowing, "n", &Operand::Move(Place::local(3))),
        Formula::var("_3", Sort::Int),
        "σ must keep the opaque temp name across a narrowing cast"
    );

    // i32 → u64: signed → unsigned widening (a negative source wraps).
    let sign_changing = caller_casting_param(Ty::i32(), Ty::u64());
    assert_eq!(
        super::sigma_actual_stable_copy_root(&sign_changing, &Operand::Move(Place::local(3))),
        None,
        "a signed→unsigned cast must NOT be followed — fail-closed"
    );
}

#[test]
fn reassigned_formal_precondition_is_not_conjoined() {
    let func = caller_with_widening_casts(true); // `lo = lo + 0` reassigns the formal
    // The gate itself must drop the precondition (fail-closed) …
    assert_eq!(
        super::stable_caller_preconditions(&func),
        Vec::<Formula>::new(),
        "a precondition over a reassigned formal must be dropped"
    );
    // … and no emitted obligation may carry it as a conjunct.
    let vcs = super::generate_callsite_precondition_vcs(&func, &range_i128_summary_db());
    let pre_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).collect();
    assert_eq!(pre_vcs.len(), 1);
    let conjuncts: Vec<Formula> = match &pre_vcs[0].formula {
        Formula::And(cs) => cs.clone(),
        other => vec![other.clone()],
    };
    assert!(
        !conjuncts.contains(&lo_le_hi()),
        "a reassigned formal's precondition must NOT reach the obligation: {conjuncts:?}"
    );
    // The reassigned root also declines the σ fold (kept fail-closed).
    assert_eq!(
        super::sigma_actual_stable_copy_root(&func, &Operand::Move(Place::local(5))),
        None
    );
}

#[test]
fn attributed_callsite_vc_carries_obligation_identity_and_gate_admits() {
    use trust_router::strengthen_whole_program::is_admissible_caller_discharge;

    let func = caller_with_widening_casts(false);
    let summaries = range_i128_summary_db();

    let attributed = super::generate_callsite_precondition_vcs_attributed(&func, &summaries);
    let entries: Vec<_> = attributed
        .iter()
        .filter(|(vc, _, _)| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert_eq!(entries.len(), 1);
    let (vc, substituted, guards) = entries[0];

    // This attributed row is the authoritative handoff to trust_verify's
    // R1 harvest. It must preserve the exact caller/callee/call-site
    // identity used to construct the obligation, not just its formula.
    assert_eq!(vc.function, "example::range_usize");
    assert_eq!(vc.location, SourceSpan::default());
    assert!(
        matches!(
            &vc.kind,
            VcKind::Precondition { callee } if callee == "example::range_i128"
        ),
        "attributed row must retain its exact callee identity: {:?}",
        vc.kind
    );

    // The independent pre-image P[σ] renders the ROOT source names.
    assert_eq!(*substituted, lo_le_hi());
    // The conjoined caller precondition surfaces as an allowed guard.
    assert!(
        guards.contains(&lo_le_hi()),
        "guards must carry the conjoined caller precondition: {guards:?}"
    );
    // And the R1 discharge gate admits the exact emitted obligation.
    assert!(
        is_admissible_caller_discharge(&vc.formula, substituted, guards),
        "the assembled obligation must pass the flat-And discharge gate: {:?}",
        vc.formula
    );

    // The two emitters MUST assemble identical formulas.
    let plain = super::generate_callsite_precondition_vcs(&func, &summaries);
    let plain_pre: Vec<_> =
        plain.iter().filter(|v| matches!(v.kind, VcKind::Precondition { .. })).collect();
    assert_eq!(plain_pre.len(), 1);
    assert_eq!(plain_pre[0].formula, vc.formula);
}

#[test]
fn proved_summary_postconditions_do_not_rewrite_body_vcs_globally() {
    let func = caller_to_reciprocal_with_body_vc();
    let (plain_solver, plain_discharged) = generate_vcs_with_discharge(&func);

    let postcondition =
        Formula::Ge(Box::new(Formula::var("result", Sort::Int)), Box::new(Formula::Int(0)));
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new("example::reciprocal").with_postcondition(postcondition).proved(),
    );

    let (summary_solver, summary_discharged) =
        generate_vcs_with_discharge_and_summaries(&func, &summaries);

    assert_eq!(plain_discharged.len(), summary_discharged.len());
    assert_eq!(plain_solver.len(), summary_solver.len());
    assert!(!summary_solver.is_empty(), "test must exercise a real solver VC");
    for (plain, summarized) in plain_solver.iter().zip(summary_solver.iter()) {
        assert_eq!(plain.formula, summarized.formula);
        assert!(
            !matches!(summarized.formula, Formula::Implies(..)),
            "callee postconditions must not be injected as global solver premises"
        );
    }
}
