use trust_types::{
    BasicBlock, BlockId, LocalDecl, ObligationRecord, Sort, SourceSpan, Ty, VerifiableBody,
    VerificationResult,
};

use super::*;

#[test]
fn held_generic_refutation_retains_every_prior_stop_without_verdict_credit() {
    use trust_types::determinism::StopCause;
    let held_reason = format!("{GENERIC_REFUTATION_HELD_PREFIX} unmodeled call result");
    for cause in StopCause::ALL {
        let previous = cause.unknown_result("native-lane", 17, "native search ended here");
        let held = hold_generic_refutation_result(&previous, &held_reason).unwrap();
        assert_eq!(StopCause::of_result(&held), cause, "{cause}");
        assert!(matches!(&held, VerificationResult::Unknown { solver, time_ms:17, reason }
            if solver.as_str()=="native-lane" && reason.starts_with(&held_reason)
                && reason.contains("native search ended here")));
    }
    let previous = VerificationResult::Unknown {
        solver: "native-lane".into(),
        time_ms: 19,
        reason: "no retained native cause".into(),
    };
    let held = hold_generic_refutation_result(&previous, &held_reason).unwrap();
    assert_eq!(StopCause::of_result(&held), StopCause::Unclassified);
    let timeout = VerificationResult::Timeout { solver: "native-clock".into(), timeout_ms: 230 };
    let held = hold_generic_refutation_result(&timeout, &held_reason).unwrap();
    assert_eq!(StopCause::of_result(&held), StopCause::WallBackstop);
    assert!(matches!(&held, VerificationResult::Unknown { solver,time_ms:0,reason }
        if solver.as_str()=="native-clock" && reason.starts_with(&held_reason)
            && reason.contains("230ms")));
    let nested = VerificationResult::Unknown {
        solver: "native-lane".into(),
        time_ms: 0,
        reason: "clock [stop:wall-backstop]; wrapper [stop:unsupported]".into(),
    };
    let held = hold_generic_refutation_result(&nested, &held_reason).unwrap();
    let VerificationResult::Unknown { reason: prior_reason, .. } = &nested else { unreachable!() };
    let VerificationResult::Unknown { reason, .. } = &held else { unreachable!() };
    assert!(
        reason.contains(prior_reason),
        "retain the complete original diagnostic, including nested tokens"
    );
    assert_eq!(StopCause::of_result(&held), StopCause::WallBackstop);
}

#[test]
fn held_generic_refutation_never_rewrites_a_verdict_or_unrecognized_marker() {
    let reason = format!("{GENERIC_REFUTATION_HELD_PREFIX} unmodeled call result");
    let failed =
        VerificationResult::Failed { solver: "native".into(), time_ms: 1, counterexample: None };
    let proved = VerificationResult::Proved {
        solver: "native".into(),
        time_ms: 1,
        strength: trust_types::ProofStrength::deductive(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    assert!(hold_generic_refutation_result(&failed, &reason).is_none());
    assert!(hold_generic_refutation_result(&proved, &reason).is_none());
    let unknown =
        trust_types::determinism::StopCause::Unclassified.unknown_result("native", 0, "gap");
    for invalid in [
        "plain diagnostic".to_string(),
        format!(" {reason}"),
        "legacy exact-string assertion hold".to_string(),
    ] {
        assert!(hold_generic_refutation_result(&unknown, &invalid).is_none());
    }
}

#[test]
fn held_generic_refutation_keeps_its_prefix_when_ay_counts_and_resources_fold() {
    use trust_types::determinism::{StopCause, fold_lane_stop};
    let prefix = format!("{GENERIC_REFUTATION_HELD_PREFIX} model is not an execution");
    for native_cause in StopCause::ALL {
        let previous = native_cause.unknown_result("native", 9, "prior native search");
        let held = hold_generic_refutation_result(&previous, &prefix).unwrap();
        let VerificationResult::Unknown { reason, .. } = &held else { unreachable!() };
        for ay_cause in [StopCause::Effort, StopCause::RssBackstop, StopCause::SolverFault] {
            let ay = ay_cause.unknown_result("ay", 3, "exact query's ay stop");
            let folded = fold_lane_stop(reason, "the ay producer", &ay).unwrap();
            assert!(folded.starts_with(&prefix));
            assert!(folded.contains("prior native search"));
            assert!(folded.contains("exact query's ay stop"));
            assert_eq!(
                StopCause::from_reason(&folded),
                Some(StopCause::combine(native_cause, ay_cause))
            );
        }
    }
}

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}
fn assign(local: usize, source: usize) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(source))),
        span: SourceSpan::default(),
    }
}
fn function() -> VerifiableFunction {
    VerifiableFunction {
        name: "loop_subject".into(),
        def_path: "test::loop_subject".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("len".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("run".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("hi".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("index".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(3, 1)],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(3, 3)],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(4, 3)],
                    terminator: Terminator::Return,
                },
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
fn gap(func: &VerifiableFunction) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "UserLoopContractUnsupported".into(),
            detail: "e4.machine.mixed-domain".into(),
        },
        function: Symbol::intern(&func.name),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}
fn query(func: &VerifiableFunction, raw: Formula, facts: Vec<Formula>) -> VerificationCondition {
    let wrappers =
        if facts.is_empty() { vec![] } else { vec![ObligationWrapper::ConjoinFactsLast { facts }] };
    VerificationCondition {
        kind: VcKind::SliceBoundsCheck,
        function: Symbol::intern(&func.name),
        location: SourceSpan::default(),
        formula: reconstruct(&raw, &wrappers).unwrap(),
        contract_metadata: None,
        obligation: Some(ObligationRecord { body: raw, wrappers, subject: None, width: None }),
    }
}
fn scope(func: &VerifiableFunction) -> GenericRefutationScope {
    GenericRefutationScope::for_function(func, &[gap(func)], &[])
}
fn sat(vc: &VerificationCondition) {
    let result = crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
    assert!(matches!(&result[0].1, VerificationResult::Failed { .. }), "{result:?}");
}

#[test]
fn satisfiable_free_loop_state_is_not_an_execution_counterexample() {
    let func = function();
    let vc = query(
        &func,
        Formula::Ge(Box::new(var("index")), Box::new(var("len"))),
        vec![
            Formula::Eq(Box::new(var("index")), Box::new(var("hi#s0_0_s2_0"))),
            Formula::Eq(Box::new(var("hi#s0_0_s2_0")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("len")), Box::new(Formula::Int(0))),
        ],
    );
    sat(&vc);
    let before = serde_json::to_value(&vc).unwrap();
    assert!(scope(&func).rejection_reason(&vc).unwrap().contains("loop-written"));
    assert_eq!(
        serde_json::to_value(&vc).unwrap(),
        before,
        "no obligation/formula is dropped or rewritten"
    );
}

#[test]
fn every_path_guard_and_transitive_definition_participates() {
    let func = function();
    let vc = query(
        &func,
        Formula::Ge(Box::new(var("len")), Box::new(Formula::Int(0))),
        vec![Formula::Gt(Box::new(var("hi#s0_0_s2_0")), Box::new(Formula::Int(0)))],
    );
    assert!(
        scope(&func).rejection_reason(&vc).is_some(),
        "a raw-only free-variable scan misses the guard"
    );
    let vc = query(&func, Formula::Ge(Box::new(var("index")), Box::new(var("len"))), vec![]);
    assert!(
        scope(&func).rejection_reason(&vc).is_some(),
        "the body copies the loop value after exit"
    );
}

#[test]
fn preclassified_unsupported_gap_preserves_the_dependency_restriction() {
    let func = function();
    let dependent = query(&func, Formula::Ge(Box::new(var("index")), Box::new(var("len"))), vec![]);
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    let (solver_vcs, preclassified) = crate::discharge_captured_raw_body_with_context(
        &func,
        vec![gap(&func), dependent],
        &context,
    );
    assert_eq!(solver_vcs.len(), 1);
    assert_eq!(preclassified.len(), 1);
    assert!(matches!(preclassified[0].1, VerificationResult::Unknown { .. }));
    assert!(matches!(&preclassified[0].0.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported"));
    let original = serde_json::to_value((&solver_vcs, &preclassified)).unwrap();
    assert!(
        GenericRefutationScope::for_function(&func, &solver_vcs, &preclassified)
            .rejection_reason(&solver_vcs[0])
            .is_some(),
        "preclassification must not hide an unsupported-loop dependency from the scope"
    );
    let independent = query(&func, Formula::Ge(Box::new(var("len")), Box::new(var("len"))), vec![]);
    assert!(
        GenericRefutationScope::for_function(&func, &solver_vcs, &preclassified)
            .rejection_reason(&independent)
            .is_none(),
        "a classified gap must not suppress an independent failure"
    );
    let mut foreign = preclassified.clone();
    foreign[0].0.function = Symbol::intern("another_function");
    assert!(
        GenericRefutationScope::for_function(&func, &solver_vcs, &foreign)
            .rejection_reason(&solver_vcs[0])
            .is_none(),
        "another function's gap cannot activate this scope"
    );
    let mut other_kind = preclassified.clone();
    other_kind[0].0.kind = VcKind::UnsupportedMir {
        kind: "OtherUnsupportedShape".into(),
        detail: "not a loop clause".into(),
    };
    assert!(
        GenericRefutationScope::for_function(&func, &solver_vcs, &other_kind)
            .rejection_reason(&solver_vcs[0])
            .is_none(),
        "unrelated classified rows are not loop gaps"
    );
    assert_eq!(serde_json::to_value((&solver_vcs, &preclassified)).unwrap(), original);
}

#[test]
fn loop_independent_real_failure_and_supported_loop_scope_are_unchanged() {
    let func = function();
    let vc = query(&func, Formula::Ge(Box::new(var("len")), Box::new(var("len"))), vec![]);
    sat(&vc);
    assert!(scope(&func).rejection_reason(&vc).is_none());
    let dependent = query(&func, Formula::Ge(Box::new(var("hi")), Box::new(var("len"))), vec![]);
    let supported_inventory = vec![dependent.clone()];
    assert!(
        GenericRefutationScope::for_function(&func, &supported_inventory, &[])
            .rejection_reason(&dependent)
            .is_none(),
        "this restriction does not revoke a supported invariant's counterexamples"
    );
    let mut acyclic = func.clone();
    acyclic.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
    assert!(
        GenericRefutationScope::for_function(&acyclic, &[], &[])
            .rejection_reason(&dependent)
            .is_none()
    );
}

#[test]
fn supported_transition_havoc_is_not_an_execution_without_an_unsupported_gap() {
    let func = function();
    for name in ["hi#e45_call_bb2", "hi#e45_nested_bb2_1", "hi#e45_call_bb2#s3_0"] {
        for value in [var(name), Formula::SymVar(Symbol::intern(name), Sort::Int)] {
            let mut vc = query(
                &func,
                Formula::Not(Box::new(Formula::Eq(Box::new(value), Box::new(Formula::Int(0))))),
                vec![],
            );
            // The scalar formula is genuinely satisfiable in the L0
            // query lane. E4 itself is currently excluded by AY routing;
            // do not misreport a future-admission guard as a live E4 SAT.
            sat(&vc);
            vc.kind =
                VcKind::LoopInvariantConsecution { invariant: "hi == 0".into(), header_block: 1 };
            let result =
                crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(&vc));
            assert!(matches!(&result[0].1, VerificationResult::Unknown { .. }), "{result:?}");
            let original = serde_json::to_value(&vc).unwrap();
            assert!(
                GenericRefutationScope::for_function(&func, &[vc.clone()], &[])
                    .rejection_reason(&vc)
                    .expect("a modeled transition may still over-approximate its return value")
                    .contains("loop-transition havoc"),
                "{name}"
            );
            assert_eq!(serde_json::to_value(&vc).unwrap(), original);
        }
    }
}

#[test]
fn supported_transition_havoc_in_facts_and_path_guards_is_withheld() {
    let func = function();
    let dependency = Formula::Gt(Box::new(var("hi#e45_call_bb2")), Box::new(Formula::Int(0)));
    let mut vc = query(&func, Formula::Bool(true), vec![dependency.clone()]);
    sat(&vc);
    vc.kind = VcKind::NonTermination { context: "loop".into(), measure: "hi".into() };
    let result =
        crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(&vc));
    assert!(matches!(&result[0].1, VerificationResult::Unknown { .. }), "{result:?}");
    let (generated, preclassified) = crate::discharge_captured_raw_body_with_context(
        &func,
        vec![vc.clone()],
        &crate::VcgenContext::for_function(func.def_path.clone()),
    );
    assert_eq!(generated.len(), 1);
    assert!(preclassified.is_empty());
    let scope = GenericRefutationScope::for_function(&func, &generated, &preclassified);
    assert!(scope.rejection_reason(&generated[0]).is_some());
    let record = vc.obligation.as_mut().unwrap();
    record.wrappers = vec![ObligationWrapper::PathGuardOr {
        paths: vec![PathGuardTerm::Guarded { guards: vec![dependency] }],
    }];
    vc.formula = reconstruct(&record.body, &record.wrappers).unwrap();
    assert!(scope.rejection_reason(&vc).is_some());
    // The complete solver query is still screened if an upstream producer
    // omitted or corrupted its raw-violation record.
    vc.obligation = None;
    assert!(scope.rejection_reason(&vc).is_some());
}

#[test]
fn supported_transition_havoc_does_not_suppress_independent_sat_or_change_unsat() {
    let func = function();
    let scope = GenericRefutationScope::for_function(&func, &[], &[]);
    for name in ["len", "hi#s2_0", "e45_call_bb2", "hi#other_e45_call_bb2"] {
        let vc = query(&func, Formula::Eq(Box::new(var(name)), Box::new(var(name))), vec![]);
        sat(&vc);
        assert!(scope.rejection_reason(&vc).is_none(), "ordinary value {name}");
    }
    let value = var("hi#e45_call_bb2");
    let vc = query(
        &func,
        Formula::Not(Box::new(Formula::Eq(Box::new(value.clone()), Box::new(value)))),
        vec![],
    );
    let original = serde_json::to_value(&vc).unwrap();
    let result =
        crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(&vc));
    assert!(matches!(&result[0].1, VerificationResult::Proved { .. }), "{result:?}");
    // This API is a restriction on SAT, never an instruction to discard
    // a proof. The compiler invokes it only for Failed results.
    assert!(scope.rejection_reason(&vc).is_some());
    assert_eq!(serde_json::to_value(&vc).unwrap(), original);
}

#[test]
fn supported_transition_dependency_scan_is_bounded() {
    let func = function();
    let mut vc = query(&func, Formula::Bool(true), vec![]);
    vc.formula = Formula::And(vec![Formula::Bool(true); MAX_FORMULA_NODES + 1]);
    assert!(
        GenericRefutationScope::for_function(&func, &[], &[])
            .rejection_reason(&vc)
            .expect("a truncated scan cannot establish absence of symbolic dependencies")
            .contains("bound")
    );
}

#[test]
#[ignore = "requires TRUST_INTEGER_CAST_A10_INPUT naming a retained actual compiler extraction"]
fn retained_a10_dependent_invariant_withholds_call_havoc_after_cast_admission() {
    let path = std::env::var("TRUST_INTEGER_CAST_A10_INPUT").unwrap();
    assert!(std::fs::metadata(&path).unwrap().len() <= 4 * 1024 * 1024);
    let bytes = std::fs::read(&path).unwrap();
    let mut func: VerifiableFunction = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(func.def_path, "a10_saturating_fold::saturating_fold");
    let unchanged = crate::generate_vcs(&func);
    let unchanged_scope = GenericRefutationScope::for_function(&func, &unchanged, &[]);
    let independent: Vec<_> = unchanged
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .collect();
    assert_eq!(independent.len(), 1);
    assert!(
        unchanged_scope.rejection_reason(independent[0]).is_none(),
        "the actual source's scalar-count invariant is independent of the call return"
    );
    // This is a deliberate dependency mutation of retained compiler MIR,
    // not a claim about the source program's actual authored invariant.
    func.contracts[0].body = "bb1: __trust_lowered_compiler_contract__:acc == 0".into();
    let raw = crate::generate_vcs(&func);
    let (generated, preclassified) = configured_production_discharge(&func);
    assert!(
        !raw.iter()
            .chain(generated.iter())
            .chain(preclassified.iter().map(|(vc, _)| vc))
            .any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == "UserLoopContractUnsupported"))
    );
    let original = serde_json::to_value((&raw, &generated, &preclassified)).unwrap();
    for (label, inventory, classified) in [
        ("raw", raw.as_slice(), &[][..]),
        ("discharged", generated.as_slice(), preclassified.as_slice()),
    ] {
        let scope = GenericRefutationScope::for_function(&func, inventory, classified);
        let mut held = 0;
        for vc in
            inventory.iter().filter(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        {
            assert!(serde_json::to_string(&vc.formula).unwrap().contains("_7#e45_call_bb3"));
            assert!(
                scope
                    .rejection_reason(vc)
                    .expect("dependent E4 candidate must be held")
                    .contains("loop-transition havoc")
            );
            held += 1;
        }
        assert_eq!(held, 1, "{label} must retain the actual consecution obligation");
    }
    assert_eq!(serde_json::to_value((&raw, &generated, &preclassified)).unwrap(), original);
    assert_eq!(std::fs::read(path).unwrap(), bytes);
}

#[test]
fn missing_mismatched_ambiguous_and_foreign_provenance_is_conservative() {
    let func = function();
    let mut vc = query(&func, Formula::Ge(Box::new(var("len")), Box::new(Formula::Int(0))), vec![]);
    vc.obligation = None;
    assert!(scope(&func).rejection_reason(&vc).unwrap().contains("missing"));
    vc.obligation = Some(ObligationRecord {
        body: Formula::Bool(false),
        wrappers: vec![],
        subject: None,
        width: None,
    });
    assert!(scope(&func).rejection_reason(&vc).unwrap().contains("reconstruct"));
    let unknown =
        query(&func, Formula::Ge(Box::new(var("opaque_alias")), Box::new(var("len"))), vec![]);
    assert!(scope(&func).rejection_reason(&unknown).unwrap().contains("provenance"));
    let mut foreign = query(&func, Formula::Bool(true), vec![]);
    foreign.function = Symbol::intern("other");
    assert!(scope(&func).rejection_reason(&foreign).unwrap().contains("identity"));
}

#[test]
fn opaque_applications_do_not_hide_dependencies_in_uninterpreted_symbols() {
    let func = function();
    for args in [vec![], vec![var("len")]] {
        for raw in [
            Formula::Pred(Symbol::intern("opaque_loop_state"), args.clone()),
            Formula::FnApp { func: "opaque_loop_state".into(), args, sort: Sort::Bool },
        ] {
            let vc = query(&func, raw, vec![]);
            assert!(scope(&func).rejection_reason(&vc).unwrap().contains("opaque predicate"));
            assert!(
                GenericRefutationScope::for_function(&func, &[], &[])
                    .rejection_reason(&vc)
                    .is_none(),
                "inactive scope grants no new authority"
            );
        }
    }
}

#[test]
fn projected_writes_and_unmodeled_aliases_cannot_claim_independence() {
    let mut func = function();
    let vc = query(&func, Formula::Ge(Box::new(var("len")), Box::new(Formula::Int(0))), vec![]);
    func.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::field(3, 0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }];
    assert!(scope(&func).rejection_reason(&vc).is_some());
    let mut func = function();
    func.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
        span: SourceSpan::default(),
    }];
    assert!(scope(&func).rejection_reason(&vc).is_some());
}

#[test]
fn field_index_and_slice_length_dependencies_are_not_hidden_by_names() {
    let func = function();
    for name in ["hi.0", "hi[0]", "hi*", "hi__slice_len", "hi#s17_2"] {
        let vc = query(&func, Formula::Ge(Box::new(var(name)), Box::new(var("len"))), vec![]);
        assert!(scope(&func).rejection_reason(&vc).is_some(), "{name}");
    }
}

#[test]
fn nested_and_renumbered_loops_do_not_depend_on_numeric_layout() {
    let mut func = function();
    // Inner self-cycle inside the outer loop; both writes contribute.
    func.body.blocks[2].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(2)),
        targets: vec![(0, BlockId(1))],
        otherwise: BlockId(2),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let vc = query(&func, Formula::Ge(Box::new(var("index")), Box::new(var("len"))), vec![]);
    assert!(scope(&func).rejection_reason(&vc).is_some());
    // Swap header/latch indices: the backedge now points UP numerically.
    func.body.blocks.swap(1, 2);
    for (index, block) in func.body.blocks.iter_mut().enumerate() {
        block.id = BlockId(index);
        let remap = |id: &mut BlockId| {
            if id.0 == 1 {
                id.0 = 2;
            } else if id.0 == 2 {
                id.0 = 1;
            }
        };
        match &mut block.terminator {
            Terminator::Goto(target) => remap(target),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, target) in targets {
                    remap(target);
                }
                remap(otherwise);
            }
            _ => {}
        }
    }
    assert!(scope(&func).rejection_reason(&vc).is_some());
}

#[test]
fn oversized_scope_or_wire_record_does_not_restore_refutation_credit() {
    let mut func = function();
    let vc = query(&func, Formula::Bool(true), vec![]);
    func.body.locals.extend((5..MAX_LOCALS + 1).map(|index| LocalDecl {
        index,
        ty: Ty::usize(),
        name: None,
    }));
    assert!(scope(&func).rejection_reason(&vc).is_some());
    let func = function();
    let mut vc = query(&func, Formula::Bool(true), vec![]);
    vc.obligation.as_mut().unwrap().wrappers =
        vec![ObligationWrapper::ConjoinFactsLast { facts: vec![] }; 129];
    assert!(scope(&func).rejection_reason(&vc).unwrap().contains("bound"));
}

#[test]
fn total_fact_cost_and_prospective_path_fanout_are_bounded_before_cloning() {
    let leaf = Formula::Bool(true);
    let small = Formula::And(vec![leaf.clone(); 128]);
    // 128 independently small formulas exceed the TOTAL borrowed budget.
    assert!(
        reconstruct(
            &leaf,
            &[ObligationWrapper::ConjoinFactsLast { facts: vec![small.clone(); 128] }]
        )
        .is_none()
    );
    // The input is tiny but copying this body across 128 paths exceeds
    // the output budget; refuse BEFORE constructing those copies.
    assert!(
        reconstruct(
            &small,
            &[ObligationWrapper::PathGuardOr { paths: vec![PathGuardTerm::Raw; 128] }]
        )
        .is_none()
    );
    assert!(
        reconstruct(
            &leaf,
            &[ObligationWrapper::PathGuardOr { paths: vec![PathGuardTerm::Raw; 128] }]
        )
        .is_some()
    );
}

#[test]
fn an_irreducible_cycle_beside_a_natural_loop_cannot_escape_the_scope() {
    let mut func = function();
    func.body.blocks[3].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(2)),
        targets: vec![(0, BlockId(4))],
        otherwise: BlockId(5),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    func.body.blocks.extend([
        BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Goto(BlockId(5)) },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(4))],
                otherwise: BlockId(6),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
    ]);
    let vc = query(&func, Formula::Bool(true), vec![]);
    assert!(scope(&func).rejection_reason(&vc).unwrap().contains("irreducible"));
}

/// Explicit development input from a real Trust `-Ztrust-dump=mir:` run.
/// This checks diagnostic dependency handling, not snapshot authenticity
/// or source-to-MIR refinement. The surrounding runner pins the bytes.
#[test]
#[ignore = "requires TRUST_LOOP_REFUTATION_INPUT naming a retained actual compiler extraction"]
fn retained_a12_extraction_withholds_satisfiable_loop_state() {
    let path = std::env::var("TRUST_LOOP_REFUTATION_INPUT").expect("explicit retained input path");
    let metadata = std::fs::metadata(&path).unwrap();
    assert!(metadata.is_file() && metadata.len() <= 4 * 1024 * 1024);
    let func: VerifiableFunction = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    assert_eq!(func.def_path, "a12_FRONTIER_multipath_loop::binary_search");
    let vcs = crate::generate_vcs(&func);
    assert!(vcs.iter().any(|vc| matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")));
    let original = serde_json::to_value(&vcs).unwrap();
    let scope = GenericRefutationScope::for_function(&func, &vcs, &[]);
    let mut held = 0;
    for vc in &vcs {
        if !matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds) {
            continue;
        }
        let result =
            crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
        if matches!(&result[0].1, VerificationResult::Failed { .. }) {
            let reason = scope.rejection_reason(vc).expect("actual A12 query must be held");
            println!("held actual extracted bounds query at {:?}: {reason}", vc.location);
            held += 1;
        }
    }
    assert!(held > 0, "control must actually reach SAT, not pass vacuously on a solver failure");
    assert_eq!(serde_json::to_value(&vcs).unwrap(), original);
    println!("held={held}; original_obligations={}", vcs.len());
}

#[test]
#[ignore = "requires TRUST_SUPPORTED_LOOP_INPUT naming a retained actual compiler extraction"]
fn retained_supported_loop_extraction_preserves_real_refutation() {
    let path = std::env::var("TRUST_SUPPORTED_LOOP_INPUT").expect("explicit retained input path");
    let metadata = std::fs::metadata(&path).unwrap();
    assert!(metadata.is_file() && metadata.len() <= 4 * 1024 * 1024);
    let func: VerifiableFunction = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    assert_eq!(func.def_path, "supported_loop_failure::supported_loop_failure");
    let vcs = crate::generate_vcs(&func);
    assert!(!vcs.iter().any(|vc| matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")));
    let original = serde_json::to_value(&vcs).unwrap();
    let scope = GenericRefutationScope::for_function(&func, &vcs, &[]);
    let mut refuted = 0;
    for vc in &vcs {
        if !matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds) {
            continue;
        }
        let result =
            crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
        if matches!(&result[0].1, VerificationResult::Failed { .. }) {
            assert!(scope.rejection_reason(vc).is_none(), "supported loop remains unaffected");
            refuted += 1;
        }
    }
    assert!(refuted > 0, "the real out-of-bounds query must actually reach SAT");
    assert_eq!(serde_json::to_value(&vcs).unwrap(), original);
    println!("preserved_actual_refutations={refuted}; original_obligations={}", vcs.len());
}

fn configured_production_discharge(
    func: &VerifiableFunction,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    crate::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        func,
        &crate::modular::SummaryDatabase::new(),
        false,
        &crate::VcgenContext::for_function(func.def_path.clone()),
        &std::collections::HashSet::<(BlockId, usize)>::new(),
    )
}

#[test]
#[ignore = "requires TRUST_LOOP_REFUTATION_INPUT naming a retained actual compiler extraction"]
fn retained_a12_production_discharge_partition_withholds_loop_state() {
    let path = std::env::var("TRUST_LOOP_REFUTATION_INPUT").expect("explicit retained input path");
    let metadata = std::fs::metadata(&path).unwrap();
    assert!(metadata.is_file() && metadata.len() <= 4 * 1024 * 1024);
    let func: VerifiableFunction = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    assert_eq!(func.def_path, "a12_FRONTIER_multipath_loop::binary_search");
    let (solver_vcs, preclassified) = configured_production_discharge(&func);
    assert!(!solver_vcs.iter().any(|vc| matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")));
    let gaps = preclassified
        .iter()
        .filter(|(vc, _)| {
            matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")
        })
        .count();
    assert!(gaps > 0, "the real discharge path must move loop gaps into preclassified results");
    assert!(
        preclassified
            .iter()
            .filter(|(vc, _)| matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported"))
            .all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
    );
    let original = serde_json::to_value((&solver_vcs, &preclassified)).unwrap();
    let scope = GenericRefutationScope::for_function(&func, &solver_vcs, &preclassified);
    let mut held = 0;
    for vc in &solver_vcs {
        if !matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds) {
            continue;
        }
        let result =
            crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
        if matches!(&result[0].1, VerificationResult::Failed { .. }) {
            let reason =
                scope.rejection_reason(vc).expect("actual post-discharge A12 query must be held");
            println!("held post-discharge A12 query at {:?}: {reason}", vc.location);
            held += 1;
        }
    }
    assert!(held > 0, "the actual post-discharge query must reach SAT, not merely Unknown");
    assert_eq!(serde_json::to_value((&solver_vcs, &preclassified)).unwrap(), original);
    println!(
        "held={held}; solver_vcs={}; preclassified={}; gaps={gaps}",
        solver_vcs.len(),
        preclassified.len()
    );
}

#[test]
#[ignore = "requires TRUST_SUPPORTED_LOOP_INPUT naming a retained actual compiler extraction"]
fn retained_supported_loop_production_discharge_preserves_real_refutation() {
    let path = std::env::var("TRUST_SUPPORTED_LOOP_INPUT").expect("explicit retained input path");
    let metadata = std::fs::metadata(&path).unwrap();
    assert!(metadata.is_file() && metadata.len() <= 4 * 1024 * 1024);
    let func: VerifiableFunction = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    assert_eq!(func.def_path, "supported_loop_failure::supported_loop_failure");
    let (solver_vcs, preclassified) = configured_production_discharge(&func);
    assert!(!solver_vcs.iter().chain(preclassified.iter().map(|(vc, _)| vc)).any(|vc|
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")));
    let original = serde_json::to_value((&solver_vcs, &preclassified)).unwrap();
    let scope = GenericRefutationScope::for_function(&func, &solver_vcs, &preclassified);
    let mut refuted = 0;
    for vc in &solver_vcs {
        if !matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds) {
            continue;
        }
        let result =
            crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
        if matches!(&result[0].1, VerificationResult::Failed { .. }) {
            assert!(
                scope.rejection_reason(vc).is_none(),
                "the supported loop remains unaffected after discharge"
            );
            refuted += 1;
        }
    }
    assert!(refuted > 0, "the real out-of-bounds query must reach SAT after discharge");
    assert_eq!(serde_json::to_value((&solver_vcs, &preclassified)).unwrap(), original);
    println!(
        "preserved_actual_refutations={refuted}; solver_vcs={}; preclassified={}",
        solver_vcs.len(),
        preclassified.len()
    );
}

/// D5-A: which formula names denote a screened destination's VALUE.
#[test]
fn call_dest_name_matching_is_exact_or_by_value_projection() {
    let dest = UnpinnedCallDest {
        name: "_3".into(),
        callee: "c::guard".into(),
        call_span: None,
        precondition_precedes_value: false,
        influence: None,
    };
    assert!(dest.names_value("_3"));
    assert!(dest.names_value("_3.0"));
    assert!(dest.names_value("_3[1]"));
    assert!(!dest.names_value("_31"), "a longer local is a different local");
    assert!(!dest.names_value("_3*"), "a dereference is memory, not the result");
    assert!(!dest.names_value("*_3"));
    assert!(!dest.names_value("_2"));
    // D5-A-DOWNCAST-1: the payload through a downcast and the variant carrier.
    assert!(dest.names_value("_3@1.0"), "`Some`'s payload is the result");
    assert!(dest.names_value("_3@1"));
    assert!(dest.names_value("__trust_mir__discr__3"), "the variant is the result");
    assert!(dest.names_value("__trust_mir__discr__3@1.0"));
    assert!(!dest.names_value("__trust_mir__discr__31"), "another local's carrier");
    assert!(!dest.names_value("_31@1.0"));
    assert!(!dest.names_value("_3@1.0*"), "memory behind the payload is not the result");
    // The independence exemption keeps the pre-widening skip set.
    assert!(dest.names_value_direct("_3.0"));
    assert!(!dest.names_value_direct("_3@1.0"));
    assert!(!dest.names_value_direct("__trust_mir__discr__3"));
}

/// D5-A: the screen reads guards and facts, not only the raw violation, and
/// an empty screen (every non-compiler caller) withholds nothing.
#[test]
fn call_dest_screen_reads_the_whole_query_and_is_inert_when_empty() {
    let func = function();
    let guarded = query(
        &func,
        Formula::Ge(Box::new(var("len")), Box::new(Formula::Int(0))),
        vec![Formula::Var("run#s1_t".into(), Sort::Bool)],
    );
    let mut scope = GenericRefutationScope::for_function(&func, &[], &[]);
    assert!(scope.rejection_reason(&guarded).is_none(), "no census, no restriction");
    scope.call_dests = vec![UnpinnedCallDest {
        name: "run".into(),
        callee: "test::helper".into(),
        call_span: None,
        precondition_precedes_value: false,
        influence: None,
    }];
    let reason = scope.rejection_reason(&guarded).expect("the guard reads the call result");
    assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX));
    assert!(reason.contains("test::helper"));
    let independent =
        query(&func, Formula::Ge(Box::new(var("len")), Box::new(Formula::Int(0))), vec![]);
    assert!(scope.rejection_reason(&independent).is_none());
    let mut foreign = independent.clone();
    foreign.function = Symbol::intern("another_function");
    assert!(
        scope.rejection_reason(&foreign).is_some(),
        "a row from another function cannot be judged by this census; withhold"
    );
}

/// D5-A: the census is inert on a context owned by another function, and
/// an empty census yields no screened destination.
#[test]
fn call_dest_census_respects_the_context_owner() {
    let func = function();
    let screen = LocalCallDestScreen::new([(1, 2)], &crate::SummaryDatabase::new());
    let foreign = crate::VcgenContext::for_function("not::this_function")
        .with_local_call_dest_screen(screen.clone());
    assert!(unpinned_local_call_dests(&func, &foreign).is_empty());
    let empty = crate::VcgenContext::for_function(func.def_path.clone());
    assert!(unpinned_local_call_dests(&func, &empty).is_empty());
    assert!(LocalCallDestScreen::default().is_empty());
    assert!(!screen.is_empty());
}

/// D5-A (measured 2026-09-24 on stage 1): the compiler's summary DB holds an
/// entry for EVERY same-crate callee of an L1 body. Only a summary the
/// injector could rebind into a caller pins the destination; a bare entry
/// (here `guard`, no postcondition) must leave it screened, or
/// `shift_via_guard`'s false refutation stands.
#[test]
fn only_an_injectable_summary_pins_a_call_destination() {
    let mut db = crate::SummaryDatabase::new();
    db.insert(crate::modular::FunctionSummary::new("fx::guard"));
    db.insert(crate::modular::FunctionSummary::new("fx::one").with_verified_callee_postcondition(
        Formula::Eq(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(1))),
    ));
    let names: FxHashSet<&str> = db.postcondition_injecting_names().collect();
    assert_eq!(names, FxHashSet::from_iter(["fx::one"]));
    assert_eq!(db.names().count(), 2, "the bare entry is still in the DB");
    // `_0 == 1` with no `requires` also DETERMINES the result: it pins.
    let pinning: Vec<(&str, usize)> = db.postcondition_pinning_callees().collect();
    assert_eq!(pinning, vec![("fx::one", 0)]);
}

// -----------------------------------------------------------------------
// Injected is not pinned (2026-09-28, `p_falsefail::dead_else`).
// -----------------------------------------------------------------------

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}
fn result() -> Formula {
    int("_0")
}
fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}
fn ge(a: Formula, b: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(b))
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn two_formals(name: &str) -> crate::modular::FunctionSummary {
    crate::modular::FunctionSummary::new(name).with_param_names(vec!["a".into(), "b".into()])
}

/// Each summary INJECTS a clause about the destination; only the ones whose
/// clause fixes `_0` as a function of the formals, with no `requires`, PIN it.
#[test]
fn an_injected_postcondition_pins_only_when_it_determines_an_unguarded_result() {
    let cases: Vec<(&str, crate::modular::FunctionSummary, bool)> = vec![
        // p_falsefail `smax`/`rmax`: guarded AND a bound — the measured case.
        (
            "fx::smax",
            two_formals("fx::smax")
                .with_precondition(le(int("b"), int("a")))
                .with_verified_callee_postcondition(le(result(), int("a"))),
            false,
        ),
        // A bound with no guard at all: the same false refutation.
        (
            "fx::umax",
            two_formals("fx::umax").with_verified_callee_postcondition(ge(result(), int("a"))),
            false,
        ),
        // Determining, but guarded: `b <= a` may be false in the model.
        (
            "fx::gmax",
            two_formals("fx::gmax")
                .with_precondition(le(int("b"), int("a")))
                .with_verified_callee_postcondition(eq(result(), int("a"))),
            false,
        ),
        // Determining and unguarded, either orientation, inside a conjunction.
        (
            "fx::first",
            two_formals("fx::first").with_verified_callee_postcondition(Formula::And(vec![
                ge(result(), int("b")),
                eq(int("a"), result()),
            ])),
            true,
        ),
        // Not a determination: `_0` on both sides, or only one disjunct.
        (
            "fx::selfref",
            two_formals("fx::selfref").with_verified_callee_postcondition(eq(result(), result())),
            false,
        ),
        (
            "fx::either",
            two_formals("fx::either").with_verified_callee_postcondition(Formula::Or(vec![
                eq(result(), int("a")),
                eq(result(), int("b")),
            ])),
            false,
        ),
    ];
    for (name, summary, pins) in cases {
        assert!(
            crate::generate::summary_may_inject_postcondition(&summary),
            "{name}: the premise — the injector does emit a clause for this summary"
        );
        assert_eq!(crate::generate::summary_pins_result(&summary), pins, "{name}");
        let mut db = crate::SummaryDatabase::new();
        db.insert(summary);
        assert_eq!(db.postcondition_injecting_names().collect::<Vec<_>>(), vec![name]);
        assert_eq!(db.postcondition_pinning_callees().count(), usize::from(pins), "{name}");
    }
}

/// `fn caller(a: u64) { let r = CALLEE(a, 3); .. }` with an identified call
/// (`(7, 11)`); with `twice_written`, `r` is first set to `0` in the call's
/// block, so the call is not the destination's one whole write.
fn identified_caller(callee: &str, twice_written: bool) -> VerifiableFunction {
    let mut func = function();
    func.name = "caller".into();
    func.def_path = "test::caller".into();
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u64(), name: None },
        LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: Ty::u64(), name: Some("r".into()) },
    ];
    func.body.arg_count = 1;
    func.body.return_ty = Ty::u64();
    let stmts = if twice_written {
        vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(0, 64))),
            span: SourceSpan::default(),
        }]
    } else {
        vec![]
    };
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts,
            terminator: Terminator::Call {
                unwind: trust_types::UnwindEdge::Unreachable,
                func: callee.into(),
                args: vec![
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(trust_types::ConstValue::Uint(3, 64)),
                ],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                is_foreign: false,
                callee_identity: Some(trust_types::CalleeIdentity {
                    stable_crate_id: 7,
                    def_index: 11,
                    substs_digest: [0, 0],
                }),
                callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    func
}

fn screened_dests(func: &VerifiableFunction, db: &crate::SummaryDatabase) -> Vec<String> {
    let context = crate::VcgenContext::for_function(func.def_path.clone())
        .with_local_call_dest_screen(LocalCallDestScreen::new([(7, 11)], db));
    unpinned_local_call_dests(func, &context).into_iter().map(|dest| dest.callee).collect()
}

/// The census answers per CALL SITE: a determining summary leaves the
/// destination to the solver; a bounding or guarded one screens it; and a
/// determining one screens it too at a site the injector refuses.
#[test]
fn the_call_dest_screen_pins_only_where_a_determining_clause_was_injected() {
    let mut bounded = crate::SummaryDatabase::new();
    bounded.insert(
        two_formals("fx::smax")
            .with_precondition(le(int("b"), int("a")))
            .with_verified_callee_postcondition(le(result(), int("a"))),
    );
    let mut determining = crate::SummaryDatabase::new();
    determining.insert(
        two_formals("fx::first").with_verified_callee_postcondition(eq(result(), int("a"))),
    );

    let smax_site = identified_caller("fx::smax", false);
    assert_eq!(screened_dests(&smax_site, &bounded), vec!["fx::smax".to_string()]);
    assert_eq!(
        screened_dests(&smax_site, &crate::SummaryDatabase::new()),
        vec!["fx::smax".to_string()],
        "control: no summary at all screens it too"
    );

    let first_site = identified_caller("fx::first", false);
    assert!(
        crate::generate::callee_postcondition_site_admits(
            &first_site,
            &Place::local(2),
            2,
            match &first_site.body.blocks[0].terminator {
                Terminator::Call { args, .. } => args,
                _ => unreachable!(),
            },
        ),
        "the premise — the injector admits this site"
    );
    assert!(screened_dests(&first_site, &determining).is_empty());

    let refused = identified_caller("fx::first", true);
    assert!(
        !crate::local_defs::dest_fact_is_version_pinnable(&refused, 2),
        "the premise — a twice-written destination is refused by the injector"
    );
    assert_eq!(screened_dests(&refused, &determining), vec!["fx::first".to_string()]);
}

/// Give the fixture's call a span no other call carries.
fn with_call_span(mut func: VerifiableFunction) -> VerifiableFunction {
    if let Terminator::Call { span, .. } = &mut func.body.blocks[0].terminator {
        *span = SourceSpan {
            file: "caller.rs".into(),
            line_start: 3,
            col_start: 13,
            line_end: 3,
            col_end: 25,
        };
    }
    func
}

fn the_call_span(func: &VerifiableFunction) -> SourceSpan {
    match &func.body.blocks[0].terminator {
        Terminator::Call { span, .. } => span.clone(),
        _ => unreachable!(),
    }
}

fn screened_scope(
    func: &VerifiableFunction,
    db: &crate::SummaryDatabase,
) -> GenericRefutationScope {
    let context = crate::VcgenContext::for_function(func.def_path.clone())
        .with_local_call_dest_screen(LocalCallDestScreen::new([(7, 11)], db));
    GenericRefutationScope::for_function_with_call_dests(func, &[], &[], &context)
}

/// The shape of the measured `[precond]` query of `let r = smax(a, 3)`:
/// `¬(3 <= a)` beside the call's own guarded injected fact
/// `(3 <= a) → r <= a`, which is how the destination gets into it.
fn row_mentioning_the_dest(
    func: &VerifiableFunction,
    kind: VcKind,
    location: SourceSpan,
) -> VerificationCondition {
    let dest = Formula::Var(crate::place_to_var_name(func, &Place::local(2)), Sort::Int);
    let pre = le(Formula::Int(3), int("a"));
    VerificationCondition {
        kind,
        function: Symbol::intern(&func.name),
        location,
        formula: Formula::And(vec![
            Formula::Implies(Box::new(pre.clone()), Box::new(le(dest, int("a")))),
            Formula::Not(Box::new(pre)),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

fn bounded_smax() -> crate::SummaryDatabase {
    let mut db = crate::SummaryDatabase::new();
    db.insert(
        two_formals("fx::smax")
            .with_precondition(le(int("b"), int("a")))
            .with_verified_callee_postcondition(le(result(), int("a"))),
    );
    db
}

/// 2026-09-28 (Track B build, `e9_requires_hypothesis_callee_reuse::
/// use_outside_sub`): once a bounded/guarded callee stopped pinning its
/// result, the whole-query screen also held the CALL'S OWN precondition
/// row — a genuine `rmax(0, 5)` violation read `[precond] UNKNOWN` instead
/// of `FAILED` — because the query mentions the destination through the
/// call's own guarded fact. The destination has no value at that row's
/// program point, so that one row is exempt for that one destination; a row
/// that READS the result stays held.
#[test]
fn the_calls_own_precondition_row_is_not_held_over_its_destination() {
    let func = with_call_span(identified_caller("fx::smax", false));
    let db = bounded_smax();
    let scope = screened_scope(&func, &db);
    let at_call = the_call_span(&func);

    let own_precondition = row_mentioning_the_dest(
        &func,
        VcKind::Precondition { callee: "fx::smax".into() },
        at_call.clone(),
    );
    assert!(
        scope.rejection_reason(&own_precondition).is_none(),
        "the call's own precondition row is judged before the call returns"
    );

    // Controls: every other row over the destination is still held.
    let reads_the_result = row_mentioning_the_dest(
        &func,
        VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Sub,
            operand_tys: (Ty::u64(), Ty::u64()),
        },
        at_call.clone(),
    );
    assert!(scope.rejection_reason(&reads_the_result).is_some());
    let another_callee = row_mentioning_the_dest(
        &func,
        VcKind::Precondition { callee: "fx::other".into() },
        at_call.clone(),
    );
    assert!(scope.rejection_reason(&another_callee).is_some());
    let another_site = row_mentioning_the_dest(
        &func,
        VcKind::Precondition { callee: "fx::smax".into() },
        SourceSpan::default(),
    );
    assert!(
        scope.rejection_reason(&another_site).is_some(),
        "a precondition row at another location is not this call's"
    );
}

/// `func` with the call result's ADDRESS taken in its `Return` block
/// (`_3 = &_2`), so the result reaches memory and the dependence exemption
/// ([`GenericRefutationScope::row_is_independent_of`]) can decide nothing:
/// only the own-precondition exemption is left to judge a row.
fn escaping(mut func: VerifiableFunction) -> VerifiableFunction {
    func.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u64()) },
        name: None,
    });
    let block = func
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, Terminator::Return))
        .expect("the fixture returns");
    block.stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
        span: SourceSpan::default(),
    });
    func
}

/// The OWN-PRECONDITION exemption needs the destination to have NO value
/// before the call. A second whole write (it could flow into the arguments
/// or the path), a parameter destination (its entry value), and a call on
/// a control-flow cycle (the previous iteration's result) each keep the row
/// held. Every fixture here lets the result escape ([`escaping`]), so the
/// dependence exemption cannot release the row instead: this test is about
/// the first exemption alone (the second is pinned below).
#[test]
fn a_destination_that_may_hold_a_value_before_the_call_keeps_its_precondition_row_held() {
    let db = bounded_smax();
    let held = |func: &VerifiableFunction| {
        let func = escaping(func.clone());
        let row = row_mentioning_the_dest(
            &func,
            VcKind::Precondition { callee: "fx::smax".into() },
            the_call_span(&func),
        );
        screened_scope(&func, &db).rejection_reason(&row).is_some()
    };

    assert!(!held(&with_call_span(identified_caller("fx::smax", false))), "the premise");
    assert!(held(&with_call_span(identified_caller("fx::smax", true))), "twice written");

    let mut parameter_dest = with_call_span(identified_caller("fx::smax", false));
    parameter_dest.body.arg_count = 2;
    assert!(held(&parameter_dest), "a parameter holds its entry value");

    let mut looping = with_call_span(identified_caller("fx::smax", false));
    looping.body.blocks[1].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(1)),
        targets: vec![(0, BlockId(0))],
        otherwise: BlockId(2),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    looping.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    assert!(held(&looping), "a loop carries the previous result into the next call");

    let mut duplicate_site = with_call_span(identified_caller("fx::smax", false));
    let mut second_call = duplicate_site.body.blocks[0].clone();
    second_call.id = BlockId(1);
    if let Terminator::Call { dest, target, .. } = &mut second_call.terminator {
        *dest = Place::local(0);
        *target = Some(BlockId(2));
    }
    duplicate_site.body.blocks[1] = second_call;
    duplicate_site.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    assert!(
        held(&duplicate_site),
        "two calls to the callee at one span: the row cannot be attributed to one of them"
    );
}

// -----------------------------------------------------------------------
// Mentioned is not depended on (2026-09-29, review blocker 2): the
// DEPENDENCE exemption. The real-MIR rows (`unused_result`, `indep_after`,
// `data_dep`, `ctrl_dep_*`) live in `tests/call_dest_refutation_scope_realmir.rs`;
// these pin each condition of `row_is_independent_of` on its own.
// -----------------------------------------------------------------------

fn span_at(line: u32) -> SourceSpan {
    SourceSpan {
        file: "caller.rs".into(),
        line_start: line,
        col_start: 5,
        line_end: line,
        col_end: 11,
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn uint(value: u128) -> Operand {
    Operand::Constant(trust_types::ConstValue::Uint(value, 64))
}

fn assign_rvalue(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

/// `_dest = CheckedSub(lhs, rhs)` at `caller.rs:line`.
fn checked_sub(dest: usize, lhs: Operand, rhs: Operand, line: u32) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::CheckedBinaryOp(trust_types::BinOp::Sub, lhs, rhs),
        span: span_at(line),
    }
}

/// `assert(!_checked.1) -> target`.
fn overflow_assert(checked: usize, target: usize, line: u32) -> Terminator {
    Terminator::Assert {
        cond: Operand::Move(Place::field(checked, 1)),
        expected: false,
        msg: trust_types::AssertMessage::Overflow(trust_types::BinOp::Sub),
        target: BlockId(target),
        span: span_at(line),
        unwind: trust_types::UnwindEdge::Unreachable,
    }
}

fn switch_on(discr: Operand, zero: usize, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr,
        targets: vec![(0, BlockId(zero))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

/// `fn caller(a: u64) -> u64 { let r = smax(a, 3); <tail> }`: the screened
/// call at bb0 (`caller.rs:3`) writing `_2`, then `tail` from bb1; `_3`..`_6`
/// are unnamed `u64` temporaries.
fn caller_with(tail: Vec<BasicBlock>) -> VerifiableFunction {
    let mut func = with_call_span(identified_caller("fx::smax", false));
    func.body.locals.extend((3..=6).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }));
    func.body.blocks.truncate(1);
    func.body.blocks.extend(tail);
    func
}

/// The query shape the review measured for `a - 10` after the call: the
/// call's own guarded injected fact over `r`, then the violation `a < 10`.
fn after_the_call(func: &VerifiableFunction, violation: Formula) -> Formula {
    let dest = Formula::Var(crate::place_to_var_name(func, &Place::local(2)), Sort::Int);
    let pre = le(Formula::Int(3), int("a"));
    Formula::And(vec![Formula::Implies(Box::new(pre), Box::new(le(dest, int("a")))), violation])
}

fn a_below_ten() -> Formula {
    Formula::Lt(Box::new(int("a")), Box::new(Formula::Int(10)))
}

fn sub_row(kind: VcKind, line: u32, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: Symbol::intern("caller"),
        location: span_at(line),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn sub_overflow() -> VcKind {
    VcKind::ArithmeticOverflow { op: trust_types::BinOp::Sub, operand_tys: (Ty::u64(), Ty::u64()) }
}

fn held(func: &VerifiableFunction, row: &VerificationCondition) -> bool {
    screened_scope(func, &bounded_smax()).rejection_reason(row).is_some()
}

/// `let r = smax(a, 3); a - 10`: bb1 `_3 = CheckedSub(copy _1, 10)` at line 4.
fn unread_result() -> VerifiableFunction {
    caller_with(vec![
        block(1, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 2, 4)),
        block(2, vec![], Terminator::Return),
    ])
}

/// The review's `unused_result` shape is RELEASED; and a row is released
/// only if it is PLACEABLE — its kind at an operation of that kind carrying
/// its span — and names nothing else it cannot resolve.
#[test]
fn an_unread_result_releases_a_placeable_row_and_nothing_else() {
    let func = unread_result();
    let formula = after_the_call(&func, a_below_ten());
    assert!(
        !held(&func, &sub_row(sub_overflow(), 4, formula.clone())),
        "`a - 10` reads nothing the call returns: its refutation is an execution"
    );
    assert!(held(&func, &sub_row(sub_overflow(), 9, formula.clone())), "no operation at the span");
    assert!(
        held(&func, &sub_row(VcKind::DivisionByZero, 4, formula.clone())),
        "an operation of another kind at the span does not place a division row"
    );
    assert!(
        held(&func, &sub_row(VcKind::Postcondition, 4, formula.clone())),
        "a postcondition is never placeable"
    );
    let mystery = after_the_call(
        &func,
        Formula::And(vec![a_below_ten(), Formula::Var("mystery".into(), Sort::Bool)]),
    );
    assert!(
        held(&func, &sub_row(sub_overflow(), 4, mystery)),
        "a name that resolves to no local cannot be shown independent"
    );
    // The scope WITHOUT a body (every non-compiler caller) exempts nothing.
    let mut bodiless = screened_scope(&func, &bounded_smax());
    bodiless.call_dest_body = None;
    assert!(bodiless.rejection_reason(&sub_row(sub_overflow(), 4, formula)).is_some());
}

/// DATA: the violation's operand is a copy of the result, even though the
/// query spells the violation over `a` alone — the MIR operand decides; and
/// a query that names a local computed from the result is held too.
#[test]
fn a_value_computed_from_the_result_is_held_wherever_it_appears() {
    let through_operand = caller_with(vec![
        block(
            1,
            vec![assign_rvalue(4, Rvalue::Use(copy(2))), checked_sub(3, copy(4), uint(10), 4)],
            overflow_assert(3, 2, 4),
        ),
        block(2, vec![], Terminator::Return),
    ]);
    let formula = after_the_call(&through_operand, a_below_ten());
    assert!(held(&through_operand, &sub_row(sub_overflow(), 4, formula)));

    let func = caller_with(vec![
        block(
            1,
            vec![assign_rvalue(4, Rvalue::Use(copy(2))), checked_sub(3, copy(1), uint(10), 4)],
            overflow_assert(3, 2, 4),
        ),
        block(2, vec![], Terminator::Return),
    ]);
    let names_the_copy = after_the_call(
        &func,
        Formula::And(vec![
            a_below_ten(),
            le(
                Formula::Var(crate::place_to_var_name(&func, &Place::local(4)), Sort::Int),
                int("a"),
            ),
        ]),
    );
    assert!(held(&func, &sub_row(sub_overflow(), 4, names_the_copy)));
    let control = after_the_call(&func, a_below_ten());
    assert!(!held(&func, &sub_row(sub_overflow(), 4, control)), "the copy is never read");
}

/// CONTROL: a branch on the result decides whether the violation runs, or
/// which value it reads — even when neither the query nor the operands name
/// anything but `a` and the result's own fact. A branch AFTER the violation
/// decides neither.
#[test]
fn a_branch_on_the_result_holds_every_row_it_can_reach() {
    let reach = caller_with(vec![
        block(1, vec![], switch_on(copy(2), 3, 2)),
        block(2, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 3, 4)),
        block(3, vec![], Terminator::Return),
    ]);
    let formula = after_the_call(&reach, a_below_ten());
    assert!(held(&reach, &sub_row(sub_overflow(), 4, formula.clone())), "reachability");

    let value = caller_with(vec![
        block(1, vec![], switch_on(copy(2), 2, 3)),
        block(2, vec![assign_rvalue(4, Rvalue::Use(uint(0)))], Terminator::Goto(BlockId(4))),
        block(3, vec![assign_rvalue(4, Rvalue::Use(uint(10)))], Terminator::Goto(BlockId(4))),
        block(4, vec![checked_sub(3, copy(1), copy(4), 4)], overflow_assert(3, 5, 4)),
        block(5, vec![], Terminator::Return),
    ]);
    assert!(held(&value, &sub_row(sub_overflow(), 4, formula.clone())), "a chosen value");

    let after = caller_with(vec![
        block(1, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 2, 4)),
        block(2, vec![], switch_on(copy(2), 3, 3)),
        block(3, vec![], Terminator::Return),
    ]);
    assert!(!held(&after, &sub_row(sub_overflow(), 4, formula)), "a later branch");
}

/// Once the result reaches memory or a callee, nothing can be shown
/// independent of it: its address taken, passed to a call, or a call run
/// only on a branch the result decides.
#[test]
fn a_result_that_reaches_memory_or_a_callee_exempts_nothing() {
    let formula = after_the_call(&unread_result(), a_below_ten());
    let address = escaping(unread_result());
    assert_eq!(call_result_influence(&address, 2), None);
    assert!(held(&address, &sub_row(sub_overflow(), 4, formula.clone())));

    let call = |args: Vec<Operand>| Terminator::Call {
        unwind: trust_types::UnwindEdge::Unreachable,
        func: "fx::sink".into(),
        args,
        dest: Place::local(5),
        target: Some(BlockId(3)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: true,
        callee_identity: None,
        callee_key: None,
    };
    let passed = caller_with(vec![
        block(1, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 2, 4)),
        block(2, vec![], call(vec![copy(2)])),
        block(3, vec![], Terminator::Return),
    ]);
    assert_eq!(call_result_influence(&passed, 2), None);
    assert!(held(&passed, &sub_row(sub_overflow(), 4, formula.clone())));

    let guarded_call = caller_with(vec![
        block(1, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 4, 4)),
        block(4, vec![], switch_on(copy(2), 5, 2)),
        block(2, vec![], call(vec![copy(1)])),
        block(3, vec![], Terminator::Goto(BlockId(5))),
        block(5, vec![], Terminator::Return),
    ]);
    assert_eq!(call_result_influence(&guarded_call, 2), None);
    let unguarded_call = caller_with(vec![
        block(1, vec![checked_sub(3, copy(1), uint(10), 4)], overflow_assert(3, 2, 4)),
        block(2, vec![], call(vec![copy(1)])),
        block(3, vec![], Terminator::Return),
    ]);
    assert!(call_result_influence(&unguarded_call, 2).is_some(), "the control");
    assert!(!held(&unguarded_call, &sub_row(sub_overflow(), 4, formula)));
}

/// Where the row carries an AUTHENTICATED obligation record, its raw
/// violation and path guards must not mention the result at all — a
/// reading that does not trust the span.
#[test]
fn an_authenticated_core_that_mentions_the_result_is_held() {
    let func = unread_result();
    let fact = match after_the_call(&func, a_below_ten()) {
        Formula::And(mut parts) => parts.remove(0),
        _ => unreachable!(),
    };
    let dest = Formula::Var(crate::place_to_var_name(&func, &Place::local(2)), Sort::Int);
    let recorded = |body: Formula, guards: Vec<Formula>| {
        let wrappers = vec![
            ObligationWrapper::PathGuardOr { paths: vec![PathGuardTerm::Guarded { guards }] },
            ObligationWrapper::ConjoinFactsLast { facts: vec![fact.clone()] },
        ];
        let formula = reconstruct(&body, &wrappers).expect("reconstructs");
        let mut row = sub_row(sub_overflow(), 4, formula);
        row.obligation = Some(ObligationRecord { body, wrappers, subject: None, width: None });
        row
    };
    let independent = recorded(a_below_ten(), vec![le(int("a"), Formula::Int(100))]);
    assert!(!held(&func, &independent));
    let in_body = recorded(
        Formula::Lt(Box::new(dest.clone()), Box::new(Formula::Int(10))),
        vec![le(int("a"), Formula::Int(100))],
    );
    assert!(held(&func, &in_body), "the violation itself reads the result");
    let in_guard = recorded(a_below_ten(), vec![le(dest, Formula::Int(100))]);
    assert!(held(&func, &in_guard), "the path to the violation reads the result");
}

/// The dependence exemption also releases a call's own precondition row
/// that the own-precondition exemption refuses (the destination is written
/// twice), when the actuals do not read the result; actuals that DO read an
/// earlier value of it keep the row held.
#[test]
fn the_dependence_exemption_releases_a_precondition_row_whose_actuals_do_not_read_the_result() {
    let db = bounded_smax();
    let row_for = |func: &VerifiableFunction| {
        row_mentioning_the_dest(
            func,
            VcKind::Precondition { callee: "fx::smax".into() },
            the_call_span(func),
        )
    };
    let twice = with_call_span(identified_caller("fx::smax", true));
    let scope = screened_scope(&twice, &db);
    assert!(!scope.call_dests[0].precondition_precedes_value, "the premise");
    assert!(scope.rejection_reason(&row_for(&twice)).is_none());

    let mut reads_prior = twice.clone();
    if let Terminator::Call { args, .. } = &mut reads_prior.body.blocks[0].terminator {
        args[0] = copy(2);
    }
    assert!(screened_scope(&reads_prior, &db).rejection_reason(&row_for(&reads_prior)).is_some());
}

// -----------------------------------------------------------------------
// S1-S3 (2026-10-16): screens that hold an ungrounded generic SAT with no
// loop contract and no call-destination census installed.
// -----------------------------------------------------------------------

const U64_MAX: i128 = u64::MAX as i128;

fn add(a: Formula, b: Formula) -> Formula {
    Formula::Add(Box::new(a), Box::new(b))
}
fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}
fn span(line: u32) -> SourceSpan {
    SourceSpan { file: "s.rs".into(), line_start: line, col_start: 4, line_end: line, col_end: 9 }
}
fn twin(func: &VerifiableFunction, at: SourceSpan, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: trust_types::HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Add)".into(),
            detail: "d".into(),
        },
        function: Symbol::intern(&func.name),
        location: at,
        formula,
        contract_metadata: None,
        obligation: None,
    }
}
fn add_overflow() -> VcKind {
    VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, operand_tys: (Ty::u64(), Ty::u64()) }
}
fn guarded_row(
    func: &VerifiableFunction,
    at: SourceSpan,
    raw: Formula,
    paths: Vec<PathGuardTerm>,
) -> VerificationCondition {
    let wrappers = vec![ObligationWrapper::PathGuardOr { paths }];
    VerificationCondition {
        kind: add_overflow(),
        function: Symbol::intern(&func.name),
        location: at,
        formula: reconstruct(&raw, &wrappers).unwrap(),
        contract_metadata: None,
        obligation: Some(ObligationRecord { body: raw, wrappers, subject: None, width: None }),
    }
}
/// A loop-free body with one call, `r = <callee>(a, 3)`.
fn plain(callee: &str) -> VerifiableFunction {
    identified_caller(callee, false)
}
fn bare_scope(
    func: &VerifiableFunction,
    generated: &[VerificationCondition],
) -> GenericRefutationScope {
    GenericRefutationScope::for_function(func, generated, &[])
}

/// S1: a `Collapsed` path term holds the row; the same row with a genuinely
/// unconditional `Raw` path is untouched. The two render identically, so the
/// query ay sees is the same — only the record says the guards were lost.
#[test]
fn s1_a_collapsed_path_term_is_held_and_a_raw_one_is_not() {
    let func = plain("test::helper");
    let raw = gt(add(var("a"), Formula::Int(1)), Formula::Int(U64_MAX));
    let collapsed = guarded_row(&func, span(3), raw.clone(), vec![PathGuardTerm::Collapsed]);
    let unconditional = guarded_row(&func, span(3), raw, vec![PathGuardTerm::Raw]);
    assert_eq!(collapsed.formula, unconditional.formula, "rendering is unchanged");
    let scope = bare_scope(&func, &[]);
    let reason = scope.rejection_reason(&collapsed).expect("a collapsed path is held");
    assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
    assert!(reason.contains("path condition collapsed"), "{reason}");
    assert_eq!(scope.rejection_reason(&unconditional), None);
    sat(&unconditional);
}

/// S1: the hardened twin carries no record, so it follows the collapsed L0
/// row that is ITS obligation — at its own span, of its own check family, over
/// its own operands. Another twin at the same span (a macro expansion, a
/// desugared `for`) is not held through that sibling.
#[test]
fn s1_a_recordless_twin_follows_its_collapsed_sibling_only() {
    let func = plain("test::helper");
    let raw = gt(add(var("a"), Formula::Int(1)), Formula::Int(U64_MAX));
    let sibling = guarded_row(&func, span(3), raw.clone(), vec![PathGuardTerm::Collapsed]);
    let scope = bare_scope(&func, std::slice::from_ref(&sibling));
    assert!(scope.rejection_reason(&twin(&func, span(3), raw.clone())).is_some());
    assert_eq!(scope.rejection_reason(&twin(&func, span(4), raw.clone())), None);
    let other_operands = gt(add(var("r"), Formula::Int(1)), Formula::Int(U64_MAX));
    assert_eq!(
        scope.rejection_reason(&twin(&func, span(3), other_operands)),
        None,
        "a twin over other operands at the same span is another obligation"
    );
    let mut bounds = twin(&func, span(3), raw.clone());
    bounds.kind = VcKind::HardenedBoundary {
        category: trust_types::HardenedVcCategory::PanicBoundary,
        callee: "mir_assert::BoundsCheck".into(),
        detail: "d".into(),
    };
    assert_eq!(scope.rejection_reason(&bounds), None, "another check family");
    let kept_too = guarded_row(&func, span(3), raw.clone(), vec![PathGuardTerm::Raw]);
    let scope = bare_scope(&func, &[sibling.clone(), kept_too]);
    assert_eq!(
        scope.rejection_reason(&twin(&func, span(3), raw.clone())),
        None,
        "a matching sibling that kept its guards: ambiguous, so kept"
    );
    let kept = guarded_row(&func, span(3), raw.clone(), vec![PathGuardTerm::Raw]);
    let scope = bare_scope(&func, std::slice::from_ref(&kept));
    assert_eq!(scope.rejection_reason(&twin(&func, span(3), raw)), None);
}

/// An L0 `r + 1` overflow row at `at`, `range ∧ extra.. ∧ violation`, with its
/// obligation record (the twin's sibling).
fn l0_row(
    func: &VerifiableFunction,
    at: SourceSpan,
    violation: Formula,
    facts: Vec<Formula>,
) -> VerificationCondition {
    let mut row = query(func, violation, facts);
    row.kind = add_overflow();
    row.location = at;
    row
}
fn u64_range(name: &str) -> Formula {
    Formula::And(vec![le(Formula::Int(0), var(name)), le(var(name), Formula::Int(U64_MAX))])
}

/// S3: a FOREIGN call's result that nothing pins (`r = dep::Cap::len(..)`,
/// `r + 1` over `u64`) holds a recorded row of a kind the L0 pass does not
/// rewrite, and the recordless twin THROUGH its sibling's record — or through
/// the sibling's generation-time decline, which drops the record. A twin with
/// no sibling at its span is not this screen's; a hypothesis that RESTRICTS the
/// value keeps the refutation; a same-crate callee is not this screen's.
#[test]
fn s3_an_unpinned_foreign_destination_is_held_and_a_restricted_one_kept() {
    let func = plain("dep::Cap::len");
    let violation = gt(add(var("r"), Formula::Int(1)), Formula::Int(U64_MAX));
    let sibling = l0_row(&func, span(5), violation.clone(), vec![u64_range("r")]);
    sat(&sibling);
    let scope = bare_scope(&func, &[]);
    let reason = scope.rejection_reason(&sibling).expect("the recorded row over a free value");
    assert!(reason.contains("unmodelled return of a foreign call (`r`)"), "{reason}");

    let free = twin(&func, span(5), sibling.formula.clone());
    assert_eq!(scope.rejection_reason(&free), None, "no sibling: nothing names the violation");
    let scope = bare_scope(&func, std::slice::from_ref(&sibling));
    let reason = scope.rejection_reason(&free).expect("the twin through its sibling's record");
    assert!(reason.contains("unmodelled return of a foreign call (`r`)"), "{reason}");
    assert_eq!(
        scope.rejection_reason(&twin(&func, span(6), sibling.formula.clone())),
        None,
        "the sibling's record speaks for its own span only"
    );

    let declined = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: crate::generate::HAVOC_DECLINE_KIND.into(),
            detail: "the obligation's verdict is the return value of an unmodelled call (`r`), which nothing in this body constrains".into(),
        },
        formula: Formula::Bool(true),
        obligation: None,
        ..sibling.clone()
    };
    let scope = bare_scope(&func, std::slice::from_ref(&declined));
    assert!(scope.rejection_reason(&free).is_some(), "the twin of a declined sibling");

    let pinned_sibling = l0_row(
        &func,
        span(5),
        violation.clone(),
        vec![u64_range("r"), le(var("r"), Formula::Int(15))],
    );
    let scope = bare_scope(&func, std::slice::from_ref(&pinned_sibling));
    assert_eq!(scope.rejection_reason(&pinned_sibling), None, "a restricted value keeps its row");
    let pinned = twin(&func, span(5), pinned_sibling.formula.clone());
    assert_eq!(scope.rejection_reason(&pinned), None, "and its twin");

    let local = plain("test::helper");
    let local_sibling = l0_row(&local, span(5), violation, vec![u64_range("r")]);
    let scope = bare_scope(&local, std::slice::from_ref(&local_sibling));
    let same_crate = twin(&local, span(5), local_sibling.formula.clone());
    assert_eq!(scope.rejection_reason(&same_crate), None, "same-crate is D5-A's");
}

/// S3, review issue 3: a twin is read through its sibling's recorded BODY only.
/// A genuine `a + 1` overflow whose path runs under a guard on the foreign value
/// (`r == 15`) refutes in its L0 sibling, and the twin keeps the same refutation
/// — trying the guard conjunct as the violation would have held it.
#[test]
fn s3_a_genuine_twin_under_a_foreign_value_guard_keeps_its_refutation() {
    let func = plain("dep::Cap::len");
    let violation = gt(add(var("a"), Formula::Int(1)), Formula::Int(U64_MAX));
    let sibling = l0_row(
        &func,
        span(7),
        violation,
        vec![u64_range("r"), u64_range("a"), eq(var("r"), Formula::Int(15))],
    );
    let twin_row = twin(&func, span(7), sibling.formula.clone());
    sat(&sibling);
    sat(&twin_row);
    let scope = bare_scope(&func, std::slice::from_ref(&sibling));
    assert_eq!(scope.rejection_reason(&sibling), None, "the L0 sibling refutes");
    assert_eq!(scope.rejection_reason(&twin_row), None, "and so does its twin");
}

/// S3: an obligation violated for EVERY value of the foreign result is a real
/// bug whatever the callee returns; its twin keeps its refutation.
#[test]
fn s3_a_violation_for_every_foreign_value_is_kept() {
    let func = plain("dep::val");
    // `r + 2^64 > u64::MAX` holds at every `r`.
    let always = gt(add(var("r"), Formula::Int(U64_MAX + 1)), Formula::Int(U64_MAX));
    let sibling = l0_row(&func, span(6), always, vec![u64_range("r")]);
    let scope = bare_scope(&func, std::slice::from_ref(&sibling));
    assert_eq!(scope.rejection_reason(&sibling), None);
    assert_eq!(scope.rejection_reason(&twin(&func, span(6), sibling.formula.clone())), None);
}

/// `fn counter(len: usize, run: bool) { let mut hi = 0; while run { hi = hi + 3 } }`
/// over a plain (wrapping) add, so the loop-carried `hi` grows by 3 a pass.
fn counter_loop() -> VerifiableFunction {
    let mut func = function();
    let three = Operand::Constant(trust_types::ConstValue::Uint(3, 64));
    func.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(0, 64))),
        span: SourceSpan::default(),
    }];
    func.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::BinaryOp(trust_types::BinOp::Add, Operand::Copy(Place::local(3)), three),
        span: SourceSpan::default(),
    }];
    func
}

/// S2: a query naming the loop-header join of `hi` is held when no value `hi`
/// takes in the first passes satisfies it (`hi + 3 > u64::MAX` needs `hi` near
/// the top of its type, which a loop starting at 0 and stepping by 3 reaches
/// only after ~2^62 iterations — the utf8simd shape) — and KEPT when a shallow
/// value does (`hi > 9` holds at iteration 4: a genuine in-loop violation keeps
/// its counterexample). Reading through a definition the query carries
/// (`t = hi`, `t + 3 > u64::MAX`) holds the same. A query over the entry value
/// only is not this screen's.
#[test]
fn s2_a_join_is_held_only_when_no_shallow_value_satisfies_the_query() {
    let func = counter_loop();
    let scope = bare_scope(&func, &[]);
    let LoopJoins::Exact { joins, shallow } = &scope.loop_joins else { panic!("bounded body") };
    assert!(shallow.is_some(), "the shallow walk ran");
    let join = joins.keys().find(|s| s.starts_with("hi#")).expect("`hi` is loop-carried");
    let hi = || Formula::Var(join.clone(), Sort::Int);
    let deep = query(&func, gt(add(hi(), Formula::Int(3)), Formula::Int(U64_MAX)), vec![]);
    sat(&deep);
    let reason = scope.rejection_reason(&deep).expect("no shallow `hi` overflows");
    assert!(reason.contains("loop-carried value at a loop header"), "{reason}");
    assert!(reason.contains(join.as_str()), "{reason}");

    let through = query(
        &func,
        gt(add(var("t"), Formula::Int(3)), Formula::Int(U64_MAX)),
        vec![eq(var("t"), hi())],
    );
    assert!(scope.rejection_reason(&through).is_some(), "read through `t = hi`");

    let shallow_bug = query(&func, gt(hi(), Formula::Int(9)), vec![]);
    sat(&shallow_bug);
    assert_eq!(
        scope.rejection_reason(&shallow_bug),
        None,
        "`hi = 12` is the value of iteration 4: a genuine refutation is kept"
    );
    let entry = query(&func, gt(var("len"), Formula::Int(3)), vec![]);
    assert_eq!(scope.rejection_reason(&entry), None);
}
