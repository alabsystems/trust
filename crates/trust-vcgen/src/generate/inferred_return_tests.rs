// Unit tests for `inferred_return` (D5-B): one decline per fragment gate, the
// shapes the synthesizer must produce, and the builder's refusal to mix an
// inferred clause into an authored summary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BasicBlock, LocalDecl, SourceSpan, VerifiableBody};

use super::*;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn uconst(value: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(value, 32))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn func(
    locals: Vec<(Ty, Option<&str>)>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "h".into(),
        def_path: "fx::h".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(str::to_string) })
                .collect(),
            blocks,
            arg_count,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn guard(bit: u32) -> bool { bit < 64 }`
fn guard() -> VerifiableFunction {
    func(
        vec![(Ty::Bool, None), (u32_ty(), Some("bit"))],
        1,
        vec![block(
            0,
            vec![assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(1), uconst(64)))],
            Terminator::Return,
        )],
    )
}

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.into(), sort)
}

#[test]
fn guard_infers_the_comparison() {
    let inferred = infer_return_candidate(&guard()).expect("guard is in the fragment");
    assert_eq!(inferred.param_names(), ["bit".to_string()]);
    assert_eq!(
        inferred.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(var("bit", Sort::Int)), Box::new(Formula::Int(64)))),
        )
    );
    assert!(!inferred.check_vcs().is_empty());
    assert!(inferred.check_vcs().iter().all(|vc| matches!(vc.kind, VcKind::Postcondition)));
}

fn scalar_guard_identity() -> trust_types::CalleeIdentity {
    trust_types::CalleeIdentity { stable_crate_id: 17, def_index: 3, substs_digest: [5, 9] }
}

fn scalar_guard_caller() -> VerifiableFunction {
    let mut caller = func(
        vec![(Ty::Bool, None), (u32_ty(), Some("input"))],
        1,
        vec![
            block(
                0,
                vec![],
                Terminator::Call {
                    func: "fx::h".into(),
                    args: vec![copy(1)],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: trust_types::UnwindEdge::Unreachable,
                    callee_identity: Some(scalar_guard_identity()),
                    callee_key: crate::sep_engine::tests::fixture_key("fx::h"),
                },
            ),
            block(1, vec![], Terminator::Return),
        ],
    );
    caller.name = "caller".into();
    caller.def_path = "fx::caller".into();
    caller
}

#[test]
fn scalar_guard_call_uses_shared_checked_input_and_keeps_original_rows() {
    let callee = infer_return_candidate(&guard()).unwrap();
    assert!(callee.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    let input = InferredReturnCall::new(scalar_guard_identity(), &callee)
        .expect("an exact scalar Boolean return candidate must be usable as a checked call input");
    let caller = scalar_guard_caller();
    let mut rows = trust_types::vc_context::VcContext::default();
    let candidate = infer_return_candidate_with_calls_rows(&caller, &[input], &mut rows).unwrap();
    assert_eq!(
        candidate.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(var("input", Sort::Int)), Box::new(Formula::Int(64)))),
        )
    );
    assert!(!candidate.check_vcs().is_empty());
    assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
}

#[test]
fn scalar_guard_call_uses_the_argument_value_at_the_call() {
    let callee = infer_return_candidate(&guard()).unwrap();
    let input = InferredReturnCall::new(scalar_guard_identity(), &callee).unwrap();
    let mut caller = scalar_guard_caller();
    caller.body.locals.push(LocalDecl { index: 2, ty: u32_ty(), name: None });
    caller.body.blocks[0].stmts =
        vec![assign(2, Rvalue::Use(copy(1))), assign(2, Rvalue::Use(uconst(9)))];
    let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!()
    };
    *args = vec![copy(2)];
    let candidate = infer_return_candidate_with_calls_rows(
        &caller,
        &[input],
        &mut trust_types::vc_context::VcContext::default(),
    )
    .unwrap();
    assert_eq!(
        candidate.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(Formula::Int(9)), Box::new(Formula::Int(64)))),
        )
    );
    assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
}

#[test]
fn scalar_guard_call_refuses_unbound_or_incompatible_calls() {
    let callee = infer_return_candidate(&guard()).unwrap();
    let input = InferredReturnCall::new(scalar_guard_identity(), &callee).unwrap();
    for mutation in 0..6 {
        let mut caller = scalar_guard_caller();
        let Terminator::Call { callee_identity, is_foreign, is_unsafe_sig, args, dest, .. } =
            &mut caller.body.blocks[0].terminator
        else {
            unreachable!()
        };
        match mutation {
            0 => *callee_identity = None,
            1 => callee_identity.as_mut().unwrap().def_index += 1,
            2 => *is_foreign = true,
            3 => *is_unsafe_sig = true,
            4 => *args = vec![Operand::Constant(ConstValue::Uint(1u128 << 40, 32))],
            5 => *dest = Place::local(1),
            _ => unreachable!(),
        }
        assert!(
            infer_return_candidate_with_calls_rows(
                &caller,
                std::slice::from_ref(&input),
                &mut trust_types::vc_context::VcContext::default(),
            )
            .is_err(),
            "accepted scalar call mutation {mutation}"
        );
    }
    assert!(
        infer_return_candidate_with_calls_rows(
            &scalar_guard_caller(),
            &[],
            &mut trust_types::vc_context::VcContext::default(),
        )
        .is_err()
    );
}

#[test]
fn scalar_guard_call_accepts_only_typed_in_range_literal_actuals() {
    let callee = infer_return_candidate(&guard()).unwrap();
    let input = InferredReturnCall::new(scalar_guard_identity(), &callee).unwrap();
    let mut caller = scalar_guard_caller();
    let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!()
    };
    *args = vec![uconst(9)];
    let candidate = infer_return_candidate_with_calls_rows(
        &caller,
        std::slice::from_ref(&input),
        &mut trust_types::vc_context::VcContext::default(),
    )
    .unwrap();
    assert_eq!(
        candidate.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(Formula::Int(9)), Box::new(Formula::Int(64)))),
        )
    );
    assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    for actual in [
        Operand::Constant(ConstValue::Uint(9, 64)),
        Operand::Constant(ConstValue::Int(9)),
        Operand::Constant(ConstValue::Bool(true)),
        Operand::Symbolic(Formula::Int(9)),
    ] {
        let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
            unreachable!()
        };
        *args = vec![actual];
        assert!(
            infer_return_candidate_with_calls_rows(
                &caller,
                std::slice::from_ref(&input),
                &mut trust_types::vc_context::VcContext::default(),
            )
            .is_err()
        );
    }
}

#[test]
fn scalar_numeric_return_is_bound_by_its_declared_type() {
    let mut identity = guard();
    identity.body.return_ty = u32_ty();
    identity.body.locals[0].ty = u32_ty();
    identity.body.blocks[0].stmts = vec![assign(0, Rvalue::Use(copy(1)))];
    let callee = infer_return_candidate(&identity).unwrap();
    assert!(callee.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    let input = InferredReturnCall::new(scalar_guard_identity(), &callee).unwrap();
    let mut caller = scalar_guard_caller();
    caller.body.locals.push(LocalDecl { index: 2, ty: u32_ty(), name: None });
    let Terminator::Call { dest, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!()
    };
    *dest = Place::local(2);
    caller.body.blocks[1].stmts = vec![assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(2), uconst(64)))];
    let candidate = infer_return_candidate_with_calls_rows(
        &caller,
        std::slice::from_ref(&input),
        &mut trust_types::vc_context::VcContext::default(),
    )
    .unwrap();
    assert_eq!(
        candidate.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Bool)),
            Box::new(Formula::Lt(Box::new(var("input", Sort::Int)), Box::new(Formula::Int(64)))),
        )
    );
    assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    caller.body.locals[2].ty = Ty::Int { width: 64, signed: false };
    assert!(
        infer_return_candidate_with_calls_rows(
            &caller,
            &[input],
            &mut trust_types::vc_context::VcContext::default(),
        )
        .is_err()
    );
}

#[test]
fn numeric_return_dependencies_compose_without_a_boolean_caller() {
    let mut callee = guard();
    callee.body.return_ty = u32_ty();
    callee.body.locals[0].ty = u32_ty();
    callee.body.blocks[0].stmts = vec![assign(0, Rvalue::Use(copy(1)))];
    let inferred = infer_return_candidate(&callee).unwrap();
    assert!(inferred.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    let input = InferredReturnCall::new(scalar_guard_identity(), &inferred).unwrap();
    let mut caller = scalar_guard_caller();
    caller.body.return_ty = u32_ty();
    caller.body.locals[0].ty = u32_ty();
    caller.body.blocks[1].stmts.clear();
    assert!(return_dependency_body_within_budget(&caller));
    assert!(infer_return_candidate(&caller).is_err(), "a missing callee remains opaque");
    let composed = infer_return_candidate_with_calls_rows(
        &caller,
        &[input],
        &mut trust_types::vc_context::VcContext::default(),
    )
    .unwrap();
    assert_eq!(
        composed.postcondition(),
        &Formula::Eq(Box::new(var("_0", Sort::Int)), Box::new(var("input", Sort::Int))),
    );
    assert!(composed.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
}

#[test]
fn dependency_walk_budget_never_grants_semantic_admission() {
    let mut function = guard();
    function.postconditions.push(Formula::Bool(true));
    assert!(return_dependency_body_within_budget(&function));
    assert!(infer_return_candidate(&function).is_err(), "authored callers mint no inferred fact");
    function.postconditions.clear();
    function.body.return_ty = Ty::Int { width: 128, signed: false };
    function.body.locals[0].ty = function.body.return_ty.clone();
    assert!(return_dependency_body_within_budget(&function));
    assert!(infer_return_candidate(&function).is_err(), "cost admission invents no scalar model");
}

#[test]
fn dependency_walk_keeps_the_original_whole_body_cost_limits() {
    let original = guard();
    let mut function = original.clone();
    function.body.blocks[0].stmts = vec![Statement::Nop; 256];
    assert!(return_dependency_body_within_budget(&function));
    function.body.blocks[0].stmts.push(Statement::Nop);
    assert!(!return_dependency_body_within_budget(&function));
    function = original.clone();
    function.body.locals.resize(128, function.body.locals[0].clone());
    assert!(return_dependency_body_within_budget(&function));
    function.body.locals.push(function.body.locals[0].clone());
    assert!(!return_dependency_body_within_budget(&function));
    function = original.clone();
    function.body.blocks.resize(32, function.body.blocks[0].clone());
    assert!(return_dependency_body_within_budget(&function));
    function.body.blocks.push(function.body.blocks[0].clone());
    assert!(!return_dependency_body_within_budget(&function));
    function = original;
    function.body.arg_count = 8;
    assert!(return_dependency_body_within_budget(&function));
    function.body.arg_count = 9;
    assert!(!return_dependency_body_within_budget(&function));
}

#[test]
fn scalar_call_arguments_are_rebound_simultaneously() {
    let callee = func(
        vec![(Ty::Bool, None), (u32_ty(), Some("x")), (u32_ty(), Some("y"))],
        2,
        vec![block(
            0,
            vec![assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(1), copy(2)))],
            Terminator::Return,
        )],
    );
    let inferred = infer_return_candidate(&callee).unwrap();
    assert!(inferred.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    let input = InferredReturnCall::new(scalar_guard_identity(), &inferred).unwrap();
    for (actuals, left, right) in
        [(vec![copy(2), copy(1)], "y", "x"), (vec![copy(1), copy(1)], "x", "x")]
    {
        let mut caller = scalar_guard_caller();
        caller.body.arg_count = 2;
        caller.body.locals = callee.body.locals.clone();
        let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
            unreachable!()
        };
        *args = actuals;
        let candidate = infer_return_candidate_with_calls_rows(
            &caller,
            std::slice::from_ref(&input),
            &mut trust_types::vc_context::VcContext::default(),
        )
        .unwrap();
        assert_eq!(
            candidate.postcondition(),
            &Formula::Eq(
                Box::new(var("_0", Sort::Bool)),
                Box::new(Formula::Lt(
                    Box::new(var(left, Sort::Int)),
                    Box::new(var(right, Sort::Int))
                )),
            )
        );
        assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    }
}

#[test]
fn scalar_signed_literal_calls_keep_the_formal_width() {
    let mut callee = guard();
    let signed = Ty::Int { width: 8, signed: true };
    callee.body.locals[1].ty = signed.clone();
    callee.body.blocks[0].stmts = vec![assign(
        0,
        Rvalue::BinaryOp(BinOp::Lt, copy(1), Operand::Constant(ConstValue::Int(0))),
    )];
    let inferred = infer_return_candidate(&callee).unwrap();
    assert!(inferred.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    let input = InferredReturnCall::new(scalar_guard_identity(), &inferred).unwrap();
    for value in [-129, -128, 127, 128] {
        let mut caller = scalar_guard_caller();
        caller.body.locals[1].ty = signed.clone();
        let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
            unreachable!()
        };
        *args = vec![Operand::Constant(ConstValue::Int(value))];
        let candidate = infer_return_candidate_with_calls_rows(
            &caller,
            std::slice::from_ref(&input),
            &mut trust_types::vc_context::VcContext::default(),
        );
        if !(-128..=127).contains(&value) {
            assert!(candidate.is_err(), "out-of-range i8 actual {value} was accepted");
            continue;
        }
        let candidate = candidate.unwrap();
        assert_eq!(
            candidate.postcondition(),
            &Formula::Eq(
                Box::new(var("_0", Sort::Bool)),
                Box::new(Formula::Lt(Box::new(Formula::Int(value)), Box::new(Formula::Int(0)))),
            )
        );
        assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    }
}

#[test]
fn scalar_summary_admission_and_emission_check_the_result_type() {
    let inferred = infer_return_candidate(&guard()).unwrap();
    let summary = crate::modular::FunctionSummary::new(inferred.def_path())
        .with_body_inferred_return(&inferred);
    let mut caller = scalar_guard_caller();
    let args = [copy(1)];
    let dest = Place::local(0);
    assert!(crate::generate::callee_postcondition_is_injectable(&caller, &dest, &summary, &args));
    assert!(
        !crate::generate::rebind_callee_postconditions(&caller, &args, &dest, &summary).is_empty()
    );
    caller.body.locals[0].ty = u32_ty();
    caller.body.return_ty = u32_ty();
    assert!(!crate::generate::callee_postcondition_is_injectable(&caller, &dest, &summary, &args));
    assert!(
        crate::generate::rebind_callee_postconditions(&caller, &args, &dest, &summary).is_empty()
    );
}

/// `fn nz(d: u32) -> u32 { if d == 0 { 1 } else { d } }` — the real rustc
/// lowering (`_3 = d == 0; switchInt(move _3) -> [0: bb2, otherwise: bb1]`,
/// both arms writing the temp `_2`, `bb3: _0 = _2; return`) becomes an `Ite`.
#[test]
fn diamond_becomes_ite() {
    let f = {
        let mut f = func(
            vec![(u32_ty(), None), (u32_ty(), Some("d")), (u32_ty(), None), (Ty::Bool, None)],
            1,
            vec![
                block(
                    0,
                    vec![assign(3, Rvalue::BinaryOp(BinOp::Eq, copy(1), uconst(0)))],
                    Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                ),
                block(1, vec![assign(2, Rvalue::Use(uconst(1)))], Terminator::Goto(BlockId(3))),
                block(2, vec![assign(2, Rvalue::Use(copy(1)))], Terminator::Goto(BlockId(3))),
                block(3, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return),
            ],
        );
        f.body.return_ty = u32_ty();
        f
    };
    let inferred = infer_return_candidate(&f).expect("nz is in the fragment");
    let d_eq_0 = Formula::Eq(Box::new(var("d", Sort::Int)), Box::new(Formula::Int(0)));
    assert_eq!(
        inferred.postcondition(),
        &Formula::Eq(
            Box::new(var("_0", Sort::Int)),
            Box::new(Formula::Ite(
                Box::new(Formula::Not(Box::new(d_eq_0))),
                Box::new(var("d", Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        )
    );
}

fn declines(f: &VerifiableFunction) -> &'static str {
    match infer_return_candidate(f) {
        Ok(inferred) => panic!("expected a decline, got {:?}", inferred.postcondition()),
        Err(reason) => reason,
    }
}

#[test]
fn authored_contract_declines() {
    let mut f = guard();
    f.postconditions.push(Formula::Bool(true));
    assert_eq!(declines(&f), "authored contract present");
}

#[test]
fn arithmetic_declines() {
    let mut f = guard();
    f.body.locals[0].ty = u32_ty();
    f.body.return_ty = u32_ty();
    f.body.blocks[0].stmts = vec![assign(0, Rvalue::BinaryOp(BinOp::Add, copy(1), uconst(1)))];
    assert_eq!(declines(&f), "binary op producing a non-bool (arithmetic)");
}

#[test]
fn cast_declines() {
    let mut f = guard();
    let u64_ty = Ty::Int { width: 64, signed: false };
    f.body.locals[0].ty = u64_ty.clone();
    f.body.return_ty = u64_ty.clone();
    f.body.blocks[0].stmts = vec![assign(0, Rvalue::Cast(copy(1), u64_ty))];
    assert_eq!(declines(&f), "rvalue outside the fragment");
}

/// `fn by_ref(r: &u32) -> bool { *r < 64 }` — a reference parameter is a
/// non-scalar local, whatever the body does with it.
#[test]
fn reference_parameter_declines() {
    let f = func(
        vec![
            (Ty::Bool, None),
            (Ty::Ref { mutable: false, inner: Box::new(u32_ty()) }, Some("r")),
            (u32_ty(), None),
        ],
        1,
        vec![block(
            0,
            vec![
                assign(
                    2,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![trust_types::Projection::Deref],
                    })),
                ),
                assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(2), uconst(64))),
            ],
            Terminator::Return,
        )],
    );
    assert_eq!(declines(&f), "local of a non-scalar type");
}

#[test]
fn wide_integer_declines() {
    let mut f = guard();
    f.body.locals[1].ty = Ty::Int { width: 128, signed: false };
    f.body.blocks[0].stmts = vec![assign(
        0,
        Rvalue::BinaryOp(BinOp::Lt, copy(1), Operand::Constant(ConstValue::Uint(64, 128))),
    )];
    assert_eq!(declines(&f), "local of a non-scalar type");
}

fn marker_parameter() -> Ty {
    let mut marker = Ty::adt("fx::Marker", vec![]);
    if let Ty::Adt { adt_kind, .. } = &mut marker {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    marker
}

/// `fn take(_marker: Marker, x: u32) -> u32 { x }` retains both formal
/// positions, even though the scalar equality does not depend on the marker.
fn marker_identity() -> VerifiableFunction {
    let mut f = func(
        vec![(u32_ty(), None), (marker_parameter(), Some("_marker")), (u32_ty(), Some("x"))],
        2,
        vec![block(0, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return)],
    );
    f.body.return_ty = u32_ty();
    f
}

#[test]
fn unused_marker_preserves_formal_positions_and_kernel_check() {
    let f = marker_identity();
    let inferred = infer_return_candidate(&f).expect("unused marker parameter");
    assert_eq!(inferred.param_names(), ["_marker", "x"]);
    assert_eq!(
        inferred.postcondition(),
        &Formula::Eq(Box::new(var("_0", Sort::Int)), Box::new(var("x", Sort::Int))),
    );
    let wrong = Formula::Eq(Box::new(var("_0", Sort::Int)), Box::new(Formula::Int(0)));
    let wrong_rows = inferred_return_check_vcs(&f, &wrong).expect("wrong candidate check rows");
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            assert!(
                inferred.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()),
                "the candidate has no authority until every original-body row kernel-checks",
            );
            assert!(wrong_rows.iter().any(|vc| trust_certify::certify_vc(vc).is_none()));
        })
        .expect("kernel check thread")
        .join()
        .expect("kernel check completed");
}

#[test]
fn unused_nonempty_enum_or_unknown_kind_parameter_declines() {
    let mut nonempty = marker_parameter();
    if let Ty::Adt { fields, .. } = &mut nonempty {
        fields.make_mut().push(("0".into(), u32_ty()));
    }
    let mut enumeration = marker_parameter();
    if let Ty::Adt { adt_kind, .. } = &mut enumeration {
        *adt_kind = Some(trust_types::AdtKind::Enum);
    }
    for ty in [nonempty, enumeration, Ty::adt("fx::Unknown", vec![])] {
        let mut f = marker_identity();
        f.body.locals[1].ty = ty;
        assert_eq!(declines(&f), "local of a non-scalar type");
    }
}

#[test]
fn marker_return_or_temporary_declines() {
    let mut result = marker_identity();
    result.body.locals[0].ty = marker_parameter();
    result.body.return_ty = marker_parameter();
    assert_eq!(declines(&result), "local of a non-scalar type");
    let mut temporary = marker_identity();
    temporary.body.locals.push(LocalDecl { index: 3, ty: marker_parameter(), name: None });
    assert_eq!(declines(&temporary), "local of a non-scalar type");
}

#[test]
fn marker_uses_in_unreachable_blocks_decline() {
    let mut reassigned = marker_identity();
    reassigned.body.blocks.push(block(
        1,
        vec![assign(1, Rvalue::Use(copy(1)))],
        Terminator::Goto(BlockId(0)),
    ));
    assert_eq!(declines(&reassigned), "dataless parameter is used");
    let mut borrowed = marker_identity();
    borrowed.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Ref { mutable: false, inner: Box::new(marker_parameter()) },
        name: None,
    });
    borrowed.body.blocks.push(block(
        1,
        vec![assign(3, Rvalue::Ref { mutable: false, place: Place::local(1) })],
        Terminator::Goto(BlockId(0)),
    ));
    assert_eq!(declines(&borrowed), "dataless parameter is used");
    let mut dropped = marker_identity();
    dropped.body.blocks.push(block(
        1,
        vec![],
        Terminator::Drop {
            place: Place::local(1),
            target: BlockId(0),
            span: SourceSpan::default(),
            unwind: trust_types::UnwindEdge::Unreachable,
        },
    ));
    assert_eq!(declines(&dropped), "dataless parameter is used");
}

#[test]
fn parameter_write_declines() {
    let mut f = guard();
    f.body.blocks[0].stmts.insert(0, assign(1, Rvalue::Use(uconst(3))));
    assert_eq!(declines(&f), "parameter reassigned");
}

#[test]
fn call_terminator_declines() {
    let mut f = guard();
    f.body.blocks.push(block(1, vec![], Terminator::Return));
    f.body.blocks[0].terminator = Terminator::Call {
        func: "fx::other".into(),
        args: vec![copy(1)],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: trust_types::UnwindEdge::Unreachable,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("fx::other"),
    };
    assert_eq!(declines(&f), "terminator outside the fragment");
}

#[test]
fn unreachable_block_declines() {
    let mut f = guard();
    f.body.blocks.push(block(1, vec![], Terminator::Unreachable));
    assert_eq!(declines(&f), "terminator outside the fragment");
}

#[test]
fn loop_declines() {
    let mut f = guard();
    f.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
    f.body.blocks.push(block(
        1,
        vec![],
        Terminator::SwitchInt {
            discr: copy(0),
            targets: vec![(0, BlockId(1))],
            otherwise: BlockId(2),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    ));
    f.body.blocks.push(block(2, vec![], Terminator::Return));
    assert_eq!(declines(&f), "cyclic control flow");
}

#[test]
fn two_returns_decline() {
    let mut f = guard();
    f.body.blocks.push(block(1, vec![], Terminator::Return));
    assert_eq!(declines(&f), "not exactly one Return block");
}

#[test]
fn read_before_write_declines() {
    let mut f = guard();
    f.body.locals.push(LocalDecl { index: 2, ty: Ty::Bool, name: None });
    f.body.blocks[0].stmts = vec![assign(0, Rvalue::Use(copy(2)))];
    assert_eq!(declines(&f), "read before write");
}

#[test]
fn integer_bitwise_declines() {
    let mut f = guard();
    f.body.locals.push(LocalDecl { index: 2, ty: u32_ty(), name: None });
    f.body.blocks[0].stmts = vec![
        assign(2, Rvalue::BinaryOp(BinOp::BitAnd, copy(1), uconst(7))),
        assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(2), uconst(4))),
    ];
    assert_eq!(declines(&f), "binary op producing a non-bool (arithmetic)");
}

#[test]
fn builder_never_mixes_with_an_authored_summary() {
    let inferred = infer_return_candidate(&guard()).expect("guard");
    let authored = crate::modular::FunctionSummary::new("fx::guard")
        .with_postcondition(Formula::Bool(true))
        .with_body_inferred_return(&inferred);
    assert_eq!(authored.postconditions, vec![Formula::Bool(true)]);
    assert!(!authored.has_reusable_postcondition_evidence());
    let required = crate::modular::FunctionSummary::new("fx::guard")
        .with_precondition(Formula::Bool(true))
        .with_body_inferred_return(&inferred);
    assert!(required.postconditions.is_empty());
    assert!(!required.has_reusable_postcondition_evidence());
    let fresh = crate::modular::FunctionSummary::new(inferred.def_path())
        .with_body_inferred_return(&inferred);
    assert!(fresh.has_reusable_postcondition_evidence());
    assert!(crate::generate::summary_may_inject_postcondition(&fresh));
    assert_eq!(fresh.param_names, vec!["bit".to_string()]);
    let mut renamed = fresh.clone();
    renamed.name = "fx::different_body".to_owned();
    assert!(!crate::generate::summary_may_inject_postcondition(&renamed));
    // A later plain clause strips the reuse bit (mixed provenance fails closed).
    let mixed = fresh.with_postcondition(Formula::Bool(true));
    assert!(!mixed.has_reusable_postcondition_evidence());
}

// ── W5 Stage 1: the one admitted call form ──────────────────────────────────

const WADD32: &str = "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_add";
const WMUL32: &str = "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_mul";

fn wrapping_call_body(callee: &str, dest_ty: Ty, operand_ty: Ty) -> VerifiableFunction {
    let mut f = func(
        vec![(dest_ty.clone(), None), (operand_ty.clone(), Some("a")), (operand_ty, Some("b"))],
        2,
        vec![
            block(
                0,
                vec![],
                Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![copy(1), copy(2)],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(callee),
                    is_foreign: false,
                },
            ),
            block(1, vec![], Terminator::Return),
        ],
    );
    // The `func` helper hardcodes `return_ty: Ty::Bool` for the bool-guard fixtures.
    f.body.return_ty = dest_ty;
    f
}

/// POSITIVE. The admitted form yields a clause, and it is the SHARED modular-`Ite`
/// spelling. That equality is the real assertion: a second spelling would pass a
/// looser test here and then be refused downstream, because
/// `machine_faithful_clause_admissible` is constructor-verified against exactly this
/// builder at the resolved domain.
#[test]
fn wrapping_add_call_is_in_the_fragment_at_the_shared_spelling() {
    let f = wrapping_call_body(WADD32, u32_ty(), u32_ty());
    let inferred = infer_return_candidate(&f).expect("the wrapping-add form is admitted");
    let expected = crate::generate::assert_refutation::wrapping_binop_modular_ite(
        BinOp::Add,
        &var("a", Sort::Int),
        &var("b", Sort::Int),
        32,
        false,
    )
    .expect("the shared constructor models u32");
    assert_eq!(
        inferred.postcondition(),
        &Formula::Eq(Box::new(var("_0", Sort::Int)), Box::new(expected))
    );
    assert!(inferred.check_vcs().iter().all(|vc| matches!(vc.kind, VcKind::Postcondition)));
}

/// NEGATIVE CONTROL, and the one this increment exists for: a 32-bit wrapping call
/// storing into a `u64` destination. Folding at either width mints a clause false of
/// the other — the false proof the adversary pass constructed and COMPILED against the
/// rejected ambient-width design (it claimed `_0 == 0` for a body returning 2^32).
#[test]
fn a_wrapping_call_whose_width_disagrees_with_its_destination_is_refused() {
    // Pins the END BEHAVIOUR — a width-skewed wrapping call never becomes an inferred
    // clause — and NOT any single guard. Measured, because two drafts of this comment
    // were wrong about which guard fires:
    //
    //   * with the dest-width cross-check neutered, this still refuses;
    //   * with the operand-agreement guard neutered too, it STILL refuses.
    //
    // The last line of defence is downstream: the clause would be built at width 32 over
    // u64 locals, so `machine_faithful_clause_admissible` refuses it at the resolved
    // domain, `inferred_return_check_vcs` sees a non-`Postcondition` row, and admission
    // fails. The two explicit cross-checks in `eval` are therefore BELT AND BRACES —
    // they refuse earlier and with a clearer message, which is worth having, but deleting
    // them does not open a hole and this test would not tell you if you did.
    //
    // Recorded so nobody reads this as a born-red pin on the cross-check. If you want one,
    // it has to assert on the returned `Err` string, not on `is_err()`.
    let u64_ty = Ty::Int { width: 64, signed: false };
    let f = wrapping_call_body(WADD32, u64_ty.clone(), u64_ty);
    assert!(
        infer_return_candidate(&f).is_err(),
        "a 32-bit wrapping call storing into a u64 destination must leave the fragment"
    );
}

/// The sibling shape: callee width and destination agree, but an operand is declared at a
/// different width. Same caveat as above — this pins the end behaviour, and the downstream
/// `machine_faithful_clause_admissible` check is what ultimately guarantees it.
#[test]
fn a_wrapping_call_whose_operand_width_disagrees_is_refused() {
    let f = wrapping_call_body(WADD32, u32_ty(), Ty::Int { width: 64, signed: false });
    assert!(
        infer_return_candidate(&f).is_err(),
        "an operand at a width other than the result's must leave the fragment"
    );
}

/// NEGATIVE CONTROL. `WrappingMul` is outside the admitted set.
#[test]
fn wrapping_mul_stays_outside_the_fragment() {
    let f = wrapping_call_body(WMUL32, u32_ty(), u32_ty());
    assert!(infer_return_candidate(&f).is_err(), "WrappingMul is not admitted");
}

/// NEGATIVE CONTROL. The widening admits ONE authenticated primitive, not calls in
/// general — an ordinary user callee is still outside the fragment.
#[test]
fn a_user_call_stays_outside_the_fragment() {
    let f = wrapping_call_body("mycrate::helper", u32_ty(), u32_ty());
    assert!(infer_return_candidate(&f).is_err(), "a user callee is not admitted");
}

/// T3 C07p: a candidate's check rows go through the row oracle into the caller's context,
/// and the candidate is the one the tree-only synthesizer returns; a declined body
/// interns nothing.
#[test]
fn candidate_check_rows_go_through_the_row_oracle() {
    use trust_types::vc_context::{Oracle, ParityCount, VcContext, same_row};

    let mut rows = VcContext::new();
    let inferred =
        infer_return_candidate_rows(&guard(), &mut rows).expect("guard is in the fragment");
    let tree = infer_return_candidate(&guard()).expect("guard is in the fragment");
    assert_eq!(inferred.postcondition(), tree.postcondition());
    assert_eq!(inferred.check_vcs().len(), tree.check_vcs().len());
    assert!(inferred.check_vcs().iter().zip(tree.check_vcs()).all(|(a, b)| same_row(a, b)));
    let checked = inferred.check_vcs().len() as u64;
    assert!(checked > 0);
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: checked, mismatches: 0 });

    let mut declined = VcContext::new();
    let mut authored = guard();
    authored.postconditions.push(Formula::Bool(true));
    assert!(infer_return_candidate_rows(&authored, &mut declined).is_err());
    assert!(declined.is_empty());
}
