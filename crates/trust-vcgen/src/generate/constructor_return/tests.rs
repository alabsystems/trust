// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
use trust_types::{
    AdtKind, BasicBlock, CalleeIdentity, LocalDecl, SourceSpan, UnwindEdge, VerifiableBody,
};

use super::*;

fn uint() -> Ty {
    Ty::Int { width: 32, signed: false }
}
fn structure(name: &str) -> Ty {
    let mut ty = Ty::adt(name, vec![("0".into(), uint())]);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Struct);
    }
    ty
}
fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(str::to_owned) }
}
fn copy(index: usize) -> Operand {
    Operand::Copy(Place::local(index))
}
fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}
fn function(ty: Ty, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "new".into(),
        def_path: "fx::A::new".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}
fn constructor() -> VerifiableFunction {
    function(
        structure("fx::A"),
        vec![
            local(0, structure("fx::A"), None),
            local(1, uint(), Some("x")),
            local(2, uint(), None),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), Rvalue::Use(copy(1))),
                assign(
                    Place::local(0),
                    Rvalue::Aggregate(
                        trust_types::AggregateKind::Adt {
                            name: "fx::A".into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![copy(2)],
                    ),
                ),
            ],
            terminator: Terminator::Return,
        }],
    )
}
fn identity() -> CalleeIdentity {
    CalleeIdentity { stable_crate_id: 13, def_index: 17, substs_digest: [19, 23] }
}
fn caller() -> VerifiableFunction {
    let mut f = function(
        uint(),
        vec![
            local(0, uint(), None),
            local(1, uint(), Some("x")),
            local(2, structure("fx::A"), Some("a")),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "fx::A::new".into(),
                    args: vec![copy(1)],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Unreachable,
                    callee_identity: Some(identity()),
                    callee_key: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::field(2, 0))),
                )],
                terminator: Terminator::Return,
            },
        ],
    );
    f.def_path = "fx::caller".into();
    f.name = "caller".into();
    f
}
fn summaries() -> crate::CalleeSummaryContext {
    let candidate =
        infer_constructor_return_candidate(&constructor()).expect("constructor candidate");
    crate::CalleeSummaryContext::default().with_constructor_returns(
        [("fx::A::new".to_owned(), candidate.bind_checked_identity(identity()))]
            .into_iter()
            .collect(),
    )
}
fn facts(f: &VerifiableFunction) -> Vec<Formula> {
    let _scope = crate::enter_test_callee_summaries(summaries());
    constructor_return_callsite_facts(&StmtVersionCtx::build(f), f, &f.body.blocks[0])
}

#[test]
fn original_aggregate_body_is_kernel_checked_and_wrong_field_candidate_refused() {
    let mut f = constructor();
    // Even an impossible entry assumption must not make a wrong candidate
    // certify. Real extraction's scalar range preconditions are cleared too.
    f.preconditions.push(Formula::Bool(false));
    let candidate = infer_constructor_return_candidate(&f).expect("preoptimization constructor");
    assert_eq!(candidate.result_ty(), &structure("fx::A"));
    let wrong = Formula::Eq(Box::new(Formula::var("_0.0", Sort::Int)), Box::new(Formula::Int(0)));
    let wrong = inferred_return_check_vcs(&f, &wrong).expect("wrong original-body check");
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            assert!(!candidate.check_vcs().is_empty());
            assert!(candidate.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
            assert!(wrong.iter().any(|vc| trust_certify::certify_vc(vc).is_none()));
        })
        .expect("kernel thread")
        .join()
        .expect("kernel checks");
}

#[test]
fn live_drop_total_metadata_keeps_original_body_kernel_and_wrong_value_checks() {
    let mut source = constructor();
    let stamp = Some(trust_types::AdtAuth::TotalDrop(None));
    for ty in [&mut source.body.return_ty, &mut source.body.locals[0].ty] {
        let Ty::Adt { arbitrary_precision, .. } = ty else { panic!("one-field struct") };
        *arbitrary_precision = stamp;
    }
    source.preconditions.push(Formula::Bool(false));
    let encoded = serde_json::to_string(&source).unwrap();
    let decoded: VerifiableFunction = serde_json::from_str(&encoded).unwrap();
    assert!(
        matches!(decoded.body.return_ty, Ty::Adt { arbitrary_precision: None, .. }),
        "the old JSON fixture cannot retain this live-extractor premise"
    );
    let candidate =
        infer_constructor_return_candidate(&source).expect("live metadata is structural");
    assert!(matches!(
        candidate.result_ty(),
        Ty::Adt { arbitrary_precision: Some(trust_types::AdtAuth::TotalDrop(None)), .. }
    ));
    let wrong = Formula::Eq(Box::new(Formula::var("_0.0", Sort::Int)), Box::new(Formula::Int(0)));
    let wrong = inferred_return_check_vcs(&source, &wrong).unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            assert!(!candidate.check_vcs().is_empty());
            assert!(
                candidate.check_vcs().iter().all(|row| trust_certify::certify_vc(row).is_some())
            );
            assert!(
                wrong.iter().any(|row| trust_certify::certify_vc(row).is_none()),
                "drop metadata cannot make an incorrect field relation true"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn unrelated_abstract_carrier_markers_cannot_authorize_constructor_inference() {
    for stamp in [
        trust_types::AdtAuth::ArbPrec(trust_types::ArbPrecKind::Signed),
        trust_types::AdtAuth::ArbPrec(trust_types::ArbPrecKind::RatioSigned),
        trust_types::AdtAuth::TotalStdMap(trust_types::TotalMapKind::HashDefault),
        trust_types::AdtAuth::TotalDrop(Some(trust_types::TotalMapKind::OrdGlobal)),
        trust_types::AdtAuth::SerdeJson(trust_types::SerdeJsonKind::Value),
    ] {
        let mut source = constructor();
        for ty in [&mut source.body.return_ty, &mut source.body.locals[0].ty] {
            let Ty::Adt { arbitrary_precision, .. } = ty else { panic!("one-field struct") };
            *arbitrary_precision = Some(stamp);
        }
        assert!(infer_constructor_return_candidate(&source).is_err());
    }
}

#[test]
fn post_call_field_is_separate_from_pre_call_scalar_input() {
    let f = caller();
    let facts = facts(&f);
    assert_eq!(facts.len(), 1);
    let free = facts[0].free_variables();
    assert!(free.iter().any(|name| name.as_str() == "a.0#s0_t"), "{facts:?}");
    assert!(free.iter().any(|name| name.as_str() == "x"), "{facts:?}");
    assert!(!free.iter().any(|name| name.as_str() == "a" || name.as_str() == "_0.0"));
    // These facts never enter generic postcondition pinning.
    assert!(!super::super::callsite::postcondition_determines_result(&facts[0]));
}

#[test]
fn cross_type_width_identity_and_instantiation_mismatches_refuse() {
    for mutate in 0..6 {
        let mut f = caller();
        match mutate {
            0 => f.body.locals[2].ty = structure("different::A"),
            1 => f.body.locals[1].ty = Ty::Int { width: 64, signed: false },
            2 => {
                if let Terminator::Call { callee_identity: Some(id), .. } =
                    &mut f.body.blocks[0].terminator
                {
                    id.def_index += 1;
                }
            }
            3 => {
                if let Terminator::Call { callee_identity: Some(id), .. } =
                    &mut f.body.blocks[0].terminator
                {
                    id.substs_digest[0] += 1;
                }
            }
            4 => {
                if let Terminator::Call { callee_identity, .. } = &mut f.body.blocks[0].terminator {
                    *callee_identity = None;
                }
            }
            _ => {
                if let Terminator::Call { is_foreign, .. } = &mut f.body.blocks[0].terminator {
                    *is_foreign = true;
                }
            }
        }
        assert!(facts(&f).is_empty(), "mutation {mutate} borrowed a field fact");
    }
}

#[test]
fn constructor_type_kind_and_unread_sibling_never_hide_in_the_fragment() {
    for mutate in 0..7 {
        let mut f = constructor();
        if let Ty::Adt { name, fields, adt_kind, .. } = &mut f.body.return_ty {
            match mutate {
                0 => *adt_kind = Some(AdtKind::Enum),
                1 => *adt_kind = Some(AdtKind::Union),
                2 => *adt_kind = None,
                3 => fields.make_mut().push(("1".into(), uint())),
                4 => fields.make_mut()[0].1 = Ty::Ref { mutable: false, inner: Box::new(uint()) },
                5 => *name = "different::A".into(),
                _ => fields.make_mut().clear(),
            }
        }
        f.body.locals[0].ty = f.body.return_ty.clone();
        assert!(infer_constructor_return_candidate(&f).is_err(), "mutation {mutate}");
    }
}

#[test]
fn constructor_fragment_does_not_inherit_unused_marker_parameter_admission() {
    let mut f = constructor();
    let mut marker = Ty::adt("fx::Marker", vec![]);
    if let Ty::Adt { adt_kind, .. } = &mut marker {
        *adt_kind = Some(AdtKind::Struct);
    }
    f.body.locals = vec![
        local(0, structure("fx::A"), None),
        local(1, marker, Some("marker")),
        local(2, uint(), Some("x")),
        local(3, uint(), None),
    ];
    f.body.arg_count = 2;
    f.body.blocks[0].stmts[0] = assign(Place::local(3), Rvalue::Use(copy(2)));
    if let Statement::Assign { rvalue: Rvalue::Aggregate(_, fields), .. } =
        &mut f.body.blocks[0].stmts[1]
    {
        *fields = vec![copy(3)];
    } else {
        panic!("actual constructor fixture");
    }
    assert_eq!(
        infer_constructor_return_candidate(&f).unwrap_err().to_string(),
        "non-scalar constructor input/temporary"
    );
}

#[test]
fn drop_call_contracts_and_projected_return_writes_refuse() {
    for mutate in 0..4 {
        let mut f = constructor();
        match mutate {
            0 => {
                f.body.blocks[0].terminator = Terminator::Drop {
                    place: Place::local(0),
                    target: BlockId(0),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                }
            }
            1 => f.spec.requires.push("true".into()),
            2 => f.body.blocks[0].stmts.push(assign(Place::field(0, 0), Rvalue::Use(copy(1)))),
            _ => f.body.blocks[0].terminator = caller().body.blocks.remove(0).terminator,
        }
        assert!(infer_constructor_return_candidate(&f).is_err());
    }
}

#[test]
fn aliased_redefined_and_joined_destinations_do_not_gain_stale_facts() {
    for mutate in 0..3 {
        let mut f = caller();
        match mutate {
            0 => {
                f.body.locals.push(local(
                    3,
                    Ty::Ref { mutable: true, inner: Box::new(structure("fx::A")) },
                    None,
                ));
                f.body.blocks[1].stmts.push(assign(
                    Place::local(3),
                    Rvalue::Ref { mutable: true, place: Place::local(2) },
                ));
            }
            1 => f.body.blocks[1].stmts.push(assign(Place::field(2, 0), Rvalue::Use(copy(1)))),
            _ => f.body.blocks.push(BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            }),
        }
        assert!(facts(&f).is_empty(), "mutation {mutate} gained a stale fact");
    }
}

#[test]
fn projected_pre_call_actual_keeps_its_entry_value() {
    let mut f = caller();
    f.body.locals[1].ty = structure("fx::A");
    f.body.locals[1].name = Some("a".into());
    f.body.locals.remove(2);
    if let Terminator::Call { args, dest, .. } = &mut f.body.blocks[0].terminator {
        *args = vec![Operand::Copy(Place::field(1, 0))];
        *dest = Place::local(1);
    }
    f.body.blocks[1].stmts =
        vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::field(1, 0))))];
    let facts = facts(&f);
    assert_eq!(facts.len(), 1, "typed input/output binding should recover this case");
    let free = facts[0].free_variables();
    assert!(free.iter().any(|name| name.as_str() == "a.0"), "{facts:?}");
    assert!(free.iter().any(|name| name.as_str() == "a.0#s0_t"), "{facts:?}");
}

#[test]
fn two_calls_reusing_one_destination_are_not_pinned_to_either_token() {
    let mut f = caller();
    f.body.blocks[1].stmts.clear();
    f.body.blocks[1].terminator = f.body.blocks[0].terminator.clone();
    if let Terminator::Call { target, .. } = &mut f.body.blocks[1].terminator {
        *target = Some(BlockId(2));
    }
    f.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    assert!(facts(&f).is_empty());
}

#[test]
fn a_later_source_write_cannot_retime_the_established_field_fact() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            for overwrite in [false, true] {
                let mut f = caller();
                f.body.locals.push(local(3, Ty::Bool, Some("equal")));
                f.body.blocks[1].stmts.clear();
                if overwrite {
                    f.body.blocks[1].stmts.push(assign(
                        Place::local(1),
                        Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                    ));
                }
                f.body.blocks[1].stmts.push(assign(
                    Place::local(3),
                    Rvalue::BinaryOp(BinOp::Eq, Operand::Copy(Place::field(2, 0)), copy(1)),
                ));
                f.body.blocks[1].terminator = Terminator::Assert {
                    cond: copy(3),
                    expected: true,
                    msg: trust_types::AssertMessage::Custom(
                        "constructor field equals source".into(),
                    ),
                    target: BlockId(2),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                };
                f.body.blocks.push(BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::field(2, 0))),
                    )],
                    terminator: Terminator::Return,
                });
                let context = crate::VcgenContext::for_function(&f.def_path)
                    .with_callee_summaries(summaries());
                let vcs = crate::generate_vcs_with_context(&f, &context);
                let assertions: Vec<_> =
                    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).collect();
                assert_eq!(
                    assertions.len(),
                    1,
                    "must exercise the actual assertion consumer: {vcs:?}"
                );
                assert_eq!(
                    trust_certify::certify_vc(assertions[0]).is_some(),
                    !overwrite,
                    "overwrite={overwrite}: {:?}",
                    assertions[0].formula
                );
            }
        })
        .expect("kernel consumption thread")
        .join()
        .expect("source timing checks");
}

#[test]
fn default_and_nested_contexts_cannot_inherit_constructor_facts() {
    let f = caller();
    let candidate = infer_constructor_return_candidate(&constructor()).expect("candidate");
    assert!(!summaries().is_empty());
    assert!(crate::CalleeSummaryContext::default().is_empty());
    let _scope = crate::enter_test_callee_summaries(summaries());
    assert!(crate::constructor_return_summary("fx::A::new").is_some());
    {
        let _nested = crate::enter_test_callee_summaries(crate::CalleeSummaryContext::default());
        assert!(crate::constructor_return_summary("fx::A::new").is_none());
        assert!(
            constructor_return_callsite_facts(&StmtVersionCtx::build(&f), &f, &f.body.blocks[0])
                .is_empty()
        );
    }
    assert_eq!(
        crate::constructor_return_summary("fx::A::new"),
        Some(candidate.bind_checked_identity(identity()))
    );
}

#[test]
fn same_short_names_compose_only_their_own_checked_field_values() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            for wrong_value in [false, true] {
                let mut other = constructor();
                other.def_path = "other::A::new".into();
                other.body.return_ty = structure("other::A");
                other.body.locals[0].ty = other.body.return_ty.clone();
                if let Statement::Assign {
                    rvalue: Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, fields),
                    ..
                } = &mut other.body.blocks[0].stmts[1]
                {
                    *name = "other::A".into();
                    if wrong_value {
                        *fields = vec![Operand::Constant(ConstValue::Uint(0, 32))];
                    }
                } else {
                    panic!("fixture must contain its actual constructor");
                }
                let other = infer_constructor_return_candidate(&other).expect("other constructor");
                assert!(other.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
                let mut other_identity = identity();
                other_identity.def_index += 1;
                let own =
                    infer_constructor_return_candidate(&constructor()).expect("own constructor");
                assert!(own.check_vcs().iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
                let models = crate::CalleeSummaryContext::default().with_constructor_returns(
                    [
                        ("fx::A::new".into(), own.bind_checked_identity(identity())),
                        ("other::A::new".into(), other.bind_checked_identity(other_identity)),
                    ]
                    .into_iter()
                    .collect(),
                );
                let mut f = caller();
                f.body.locals.push(local(3, structure("other::A"), Some("b")));
                f.body.locals.push(local(4, Ty::Bool, Some("equal")));
                f.body.blocks[1] = BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "other::A::new".into(),
                        args: vec![copy(1)],
                        dest: Place::local(3),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Unreachable,
                        callee_identity: Some(other_identity),
                        callee_key: None,
                    },
                };
                f.body.blocks.push(BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::field(2, 0)),
                            Operand::Copy(Place::field(3, 0)),
                        ),
                    )],
                    terminator: Terminator::Assert {
                        cond: copy(4),
                        expected: true,
                        msg: trust_types::AssertMessage::Custom("two constructor results".into()),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                });
                f.body.blocks.push(BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::field(2, 0))),
                    )],
                    terminator: Terminator::Return,
                });
                let context =
                    crate::VcgenContext::for_function(&f.def_path).with_callee_summaries(models);
                let vcs = crate::generate_vcs_with_context(&f, &context);
                let assertions: Vec<_> =
                    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).collect();
                assert_eq!(assertions.len(), 1);
                assert_eq!(
                    trust_certify::certify_vc(assertions[0]).is_some(),
                    !wrong_value,
                    "same short names, wrong_value={wrong_value}: {:?}",
                    assertions[0].formula
                );
            }
        })
        .expect("kernel composition thread")
        .join()
        .expect("same-name body checks");
}

#[test]
fn actual_original_member_fixture_outlined_panic_needs_its_own_checked_field_models() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let input: Vec<VerifiableFunction> = serde_json::from_str(include_str!(
                "../../../tests/fixtures/native_constructor_return_actual.json"
            ))
            .expect("unchanged actual C6 function dumps");
            assert_eq!(input.len(), 3);
            let caller = input.iter().find(|f| f.name == "make").expect("actual caller");
            let identity_a = caller
                .body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator {
                    Terminator::Call { func, callee_identity, .. }
                        if func.ends_with("::A::new") =>
                    {
                        *callee_identity
                    }
                    _ => None,
                })
                .expect("actual first constructor identity");
            // 0: no model; 1: both checked original bodies; 2: identity donation;
            // 3: a genuine differing constructor value, independently checked.
            for control in 0..4 {
                let mut models = FxHashMap::default();
                if control != 0 {
                    for block in &caller.body.blocks {
                        let Terminator::Call { func, callee_identity: Some(identity), .. } =
                            &block.terminator
                        else {
                            continue;
                        };
                        let Some(original) = input.iter().find(|body| &body.def_path == func)
                        else {
                            continue;
                        };
                        let mut body = original.clone();
                        let second = body.def_path.ends_with("::B::new");
                        if control == 3 && second {
                            let Statement::Assign { rvalue: Rvalue::Aggregate(_, fields), .. } =
                                &mut body.body.blocks[0].stmts[0]
                            else {
                                panic!("actual constructor shape");
                            };
                            *fields = vec![Operand::Constant(ConstValue::Uint(0, 32))];
                        }
                        let candidate = infer_constructor_return_candidate(&body)
                            .expect("actual constructor candidate");
                        assert!(
                            candidate
                                .check_vcs()
                                .iter()
                                .all(|vc| trust_certify::certify_vc(vc).is_some())
                        );
                        let owner = if control == 2 && second { identity_a } else { *identity };
                        assert!(
                            models
                                .insert(func.clone(), candidate.bind_checked_identity(owner))
                                .is_none()
                        );
                    }
                    assert_eq!(models.len(), 2);
                }
                let context = crate::VcgenContext::for_function(&caller.def_path)
                    .with_callee_summaries(
                        crate::CalleeSummaryContext::default().with_constructor_returns(models),
                    );
                // Constructor fields contribute proof-facing equalities only;
                // they do not ground aggregates for the refutation-only lane.
                assert!(
                    crate::generate_full_assert_refutation_vcs_with_context(caller, &context)
                        .is_empty()
                );
                let ordinary = crate::generate_vcs_with_context(caller, &context);
                let vcs: Vec<_> = ordinary
                    .iter()
                    .filter(|vc| matches!(vc.kind, VcKind::Assertion { .. }))
                    .collect();
                assert_eq!(
                    vcs.len(),
                    1,
                    "must keep the original outlined-panic site, control={control}: {ordinary:?}"
                );
                assert_eq!(
                    trust_certify::certify_vc(&vcs[0]).is_some(),
                    control == 1,
                    "actual original source, control={control}: {:?}",
                    vcs[0].formula
                );
            }
        })
        .expect("actual MIR proof thread")
        .join()
        .expect("actual outlined-panic controls");
}
