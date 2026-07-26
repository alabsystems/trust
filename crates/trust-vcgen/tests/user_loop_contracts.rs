use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

fn span(line_start: u32, line_end: u32) -> SourceSpan {
    SourceSpan {
        file: "loop_contracts.rs".to_string(),
        line_start,
        col_start: 0,
        line_end,
        col_end: 80,
    }
}

fn counted_loop() -> VerifiableFunction {
    // i = 0; while i < n { i = i + 1; }
    VerifiableFunction {
        name: "counted".to_string(),
        def_path: "test::counted".to_string(),
        span: span(1, 20),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".to_string()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".to_string()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".to_string()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: span(7, 7),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span(10, 10),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span(10, 10),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: span(13, 13),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
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

fn loop_spec(kind: LoopContractKind, body: &str) -> LoopContractSpec {
    LoopContractSpec {
        kind,
        source_loop_id: 0,
        loop_head: span(9, 15),
        header_span: span(9, 11),
        span: span(11, 11),
        body: body.to_string(),
    }
}

fn add_second_loop(func: &mut VerifiableFunction) {
    // Add a second, independent natural loop after the first exit.
    func.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond2".to_string()) });
    func.body.blocks[3].terminator = Terminator::Goto(BlockId(4));
    func.body.blocks.extend([
        BasicBlock {
            id: BlockId(4),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(4)),
                targets: vec![(1, BlockId(5))],
                otherwise: BlockId(6),
                exhaustive_enum_unreachable: false,
                span: span(21, 21),
            },
        },
        BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Goto(BlockId(4)) },
        BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
    ]);
}

fn nested_spanless_header_loops() -> VerifiableFunction {
    // The inner loop's body is also part of the outer natural-loop body. Both
    // headers deliberately lack spans, which forces SF-6's fallback lane.
    VerifiableFunction {
        name: "nested".to_string(),
        def_path: "test::nested".to_string(),
        span: span(1, 60),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".to_string()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".to_string()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("outer_cond".to_string()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("inner_cond".to_string()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(6),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: span(20, 20),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(1, BlockId(4))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: span(30, 30),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: span(40, 40),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
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

fn contains_increment(formula: &Formula) -> bool {
    matches!(
        formula,
        Formula::Add(lhs, rhs)
            if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i")
                && matches!(rhs.as_ref(), Formula::Int(1))
    ) || formula.children().into_iter().any(contains_increment)
}

fn contains_negated_post_increment(formula: &Formula) -> bool {
    matches!(formula, Formula::Not(post) if contains_increment(post))
        || formula.children().into_iter().any(contains_negated_post_increment)
}

#[test]
fn native_invariant_and_decreases_generate_real_transition_obligations() {
    let mut func = counted_loop();
    let specs = vec![
        loop_spec(LoopContractKind::Invariant, "i <= n"),
        loop_spec(LoopContractKind::Decreases, "n - i"),
    ];
    assert!(bind_compiler_loop_contracts(&mut func, &specs).is_empty());
    assert!(func.contracts.iter().all(|contract| contract.body.starts_with("bb1: ")));

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        preclassified.iter().all(|(vc, _)| {
            !matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")
        }),
        "supported loop clauses must not degrade to transport-only Unknown: {preclassified:#?}"
    );
    let all_vcs: Vec<_> = solver_vcs.iter().chain(preclassified.iter().map(|(vc, _)| vc)).collect();
    let initiation = all_vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. }))
        .expect("E4 entry obligation");
    let preservation = all_vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("E4 preservation obligation");
    let decreases = all_vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "loop-decreases"))
        .expect("E5 decreases obligation");

    assert_ne!(preservation.formula, Formula::Bool(true));
    assert_ne!(preservation.formula, Formula::Bool(false));
    assert!(
        contains_increment(&preservation.formula),
        "preservation must mention the post-iteration state, not P && !P: {:?}",
        preservation.formula
    );
    assert!(
        contains_increment(&decreases.formula),
        "decreases must compare the authored measure before/after the body: {:?}",
        decreases.formula
    );
    // i=0 makes initiation a closed instance over n; it is not the old raw
    // `!P(i,n)` that forgot the preheader assignment.
    assert!(!initiation.formula.free_variables().contains("i"), "{:?}", initiation.formula);
}

#[test]
fn compiler_while_with_spanless_header_terminator_pairs_from_loop_body_evidence() {
    let mut func = counted_loop();
    let Terminator::SwitchInt { span: header_span, .. } = &mut func.body.blocks[1].terminator
    else {
        unreachable!("counted_loop header is a SwitchInt")
    };
    *header_span = SourceSpan::default();

    let specs = vec![loop_spec(LoopContractKind::Invariant, "i <= n")];
    let failures = bind_compiler_loop_contracts(&mut func, &specs);
    assert!(
        failures.is_empty(),
        "a compiler while-loop with a span-less header terminator must use contained body evidence: {failures:#?}",
    );
    assert_eq!(func.contracts.len(), 1);
    assert_eq!(func.contracts[0].body, "bb1: i <= n");
}

#[test]
fn function_level_span_inside_natural_loop_does_not_poison_contained_pairing() {
    let mut func = counted_loop();
    let Terminator::SwitchInt { span: header_span, .. } = &mut func.body.blocks[1].terminator
    else {
        unreachable!("counted_loop header is a SwitchInt")
    };
    *header_span = SourceSpan::default();
    let Statement::Assign { span: body_span, .. } = &mut func.body.blocks[2].stmts[0] else {
        unreachable!("counted_loop body begins with an assignment")
    };
    // Real natural-loop block sets can carry argument-copy statements whose
    // span is the function signature, before and outside the authored loop.
    *body_span = span(2, 2);

    let failures = bind_compiler_loop_contracts(
        &mut func,
        &[loop_spec(LoopContractKind::Invariant, "i <= n")],
    );
    assert!(
        failures.is_empty(),
        "out-of-loop rider spans must be skipped before choosing the earliest contained evidence: {failures:#?}",
    );
    assert_eq!(func.contracts[0].body, "bb1: i <= n");
}

#[test]
fn inner_loop_exact_header_never_pairs_to_containing_outer_natural_loop() {
    let mut func = nested_spanless_header_loops();
    let Terminator::SwitchInt { span: inner_header_span, .. } = &mut func.body.blocks[3].terminator
    else {
        unreachable!("nested inner-loop header is a SwitchInt")
    };
    *inner_header_span = span(28, 29);
    let specs = vec![LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 1,
        loop_head: span(28, 35),
        header_span: span(28, 29),
        span: span(29, 29),
        body: "i <= n".to_string(),
    }];

    let failures = bind_compiler_loop_contracts(&mut func, &specs);
    assert!(
        failures.is_empty(),
        "the inner source span should select only the inner loop's earliest source evidence: {failures:#?}",
    );
    assert_eq!(func.contracts.len(), 1);
    assert_eq!(
        func.contracts[0].body, "bb3: i <= n",
        "exact inner-header evidence must not make the containing outer header authoritative",
    );
}

#[test]
fn spanless_outer_loop_with_nested_candidate_fails_even_when_source_order_differs() {
    let mut func = nested_spanless_header_loops();
    // The outer header's body has source evidence at line 20, before the inner
    // loop's line-30 evidence. Source order used to select bb1 and accept the
    // structurally nested bb3 candidate. Neither ordering nor nesting is an
    // authenticated HIR-loop-to-MIR-header identity, so both candidates must
    // now make the span fallback fail closed.
    let specs = vec![LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        loop_head: span(18, 45),
        header_span: span(18, 19),
        span: span(19, 19),
        body: "i <= n".to_string(),
    }];

    let failures = bind_compiler_loop_contracts(&mut func, &specs);
    assert_eq!(failures.len(), 1, "nested candidates must fail exactly once");
    assert!(
        failures[0].1.contains("span fallback requires exactly one distinct header"),
        "unexpected fail-closed reason: {failures:#?}",
    );
    assert_eq!(func.contracts.len(), 1);
    assert!(
        func.contracts[0].body.starts_with("__trust_unpaired_loop_contract__:"),
        "a span-only outer contract must not be assigned by source order: {:?}",
        func.contracts[0],
    );
}

#[test]
fn outer_spanless_loop_with_only_nested_source_evidence_fails_closed() {
    let mut func = nested_spanless_header_loops();
    // Remove every source-bearing statement exclusive to the outer natural
    // loop. The line-30 inner assignment is now the earliest (and only)
    // contained evidence for both headers. Choosing the structurally innermost
    // header would silently attach this OUTER contract to the INNER loop.
    func.body.blocks[2].stmts.clear();
    func.body.blocks[5].stmts.clear();
    let specs = vec![LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        loop_head: span(18, 45),
        header_span: span(18, 19),
        span: span(19, 19),
        body: "i <= n".to_string(),
    }];

    let failures = bind_compiler_loop_contracts(&mut func, &specs);
    assert_eq!(failures.len(), 1, "ambiguous nested evidence must fail exactly once");
    assert!(
        failures[0].1.contains("span fallback requires exactly one distinct header"),
        "unexpected fail-closed reason: {failures:#?}",
    );
    assert_eq!(func.contracts.len(), 1);
    assert!(
        func.contracts[0].body.starts_with("__trust_unpaired_loop_contract__:"),
        "an ambiguous outer contract must not be assigned to either natural-loop header: {:?}",
        func.contracts[0],
    );
}

#[test]
fn decreases_rejects_a_body_that_mutates_its_upper_bound() {
    let mut func = counted_loop();
    func.body.blocks[2].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
        span: span(14, 14),
    });
    assert!(
        bind_compiler_loop_contracts(
            &mut func,
            &[loop_spec(LoopContractKind::Decreases, "n - i")],
        )
        .is_empty()
    );

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        !solver_vcs.iter().any(|vc| {
            matches!(&vc.kind, VcKind::NonTermination { context, .. }
                if context == "loop-decreases")
        }),
        "a pre-state guard must not authorize post-state `0 - (i + 1)`: {solver_vcs:#?}",
    );
    let unsupported: Vec<_> = preclassified
        .iter()
        .filter(|(vc, result)| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "UserLoopContractUnsupported")
                && matches!(result, VerificationResult::Unknown { .. })
        })
        .collect();
    assert_eq!(
        unsupported.len(),
        1,
        "the rejected E5 clause must remain as one visible fail-closed Unknown: {preclassified:#?}",
    );
    assert_eq!(unsupported[0].0.formula, Formula::Bool(true));
}

#[test]
fn wrong_invariant_is_not_preserved_by_a_tautological_contradiction() {
    let mut func = counted_loop();
    assert!(
        bind_compiler_loop_contracts(
            &mut func,
            &[loop_spec(LoopContractKind::Invariant, "i < n")],
        )
        .is_empty()
    );
    let (solver_vcs, _) = generate_vcs_with_discharge(&func);
    let preservation = solver_vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("preservation VC");
    let Formula::And(parts) = &preservation.formula else {
        panic!("preservation must be a transition conjunction: {:?}", preservation.formula);
    };
    assert!(
        parts.iter().any(contains_negated_post_increment),
        "post-state invariant must contain i+1: {parts:#?}"
    );
    assert!(
        !parts.iter().any(|left| {
            parts.iter().any(|right| matches!(right, Formula::Not(inner) if inner.as_ref() == left))
        }),
        "a wrong invariant must not become the unsat P && !P shortcut"
    );
}

#[test]
fn unpaired_or_unparseable_authored_clause_fails_closed() {
    let mut func = counted_loop();
    let mut wrong_span = loop_spec(LoopContractKind::Invariant, "???");
    wrong_span.loop_head = span(40, 45);
    wrong_span.header_span = span(40, 41);
    let failures = bind_compiler_loop_contracts(&mut func, &[wrong_span]);
    assert_eq!(failures.len(), 2, "parse and pairing failures are both diagnosed");
    let (_, preclassified) = generate_vcs_with_discharge(&func);
    assert!(preclassified.iter().any(|(vc, result)| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")
            && matches!(result, VerificationResult::Unknown { .. })
    }));
}

#[test]
fn unpaired_decreases_is_not_reinterpreted_as_recursive_metadata() {
    let mut func = counted_loop();
    let mut wrong_span = loop_spec(LoopContractKind::Decreases, "n - i");
    wrong_span.loop_head = span(40, 45);
    wrong_span.header_span = span(40, 41);
    let failures = bind_compiler_loop_contracts(&mut func, &[wrong_span]);
    assert_eq!(failures.len(), 1, "the missing loop-header pairing must be diagnosed");

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(preclassified.iter().any(|(vc, result)| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")
            && matches!(result, VerificationResult::Unknown { .. })
    }));
    assert!(!solver_vcs.iter().any(|vc| {
        matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "loop-decreases")
    }));
}

#[test]
fn ill_sorted_loop_clauses_fail_closed_before_solver_dispatch() {
    let mut func = counted_loop();
    let specs = vec![
        loop_spec(LoopContractKind::Invariant, "i + 1"),
        loop_spec(LoopContractKind::Decreases, "i < n"),
    ];
    assert!(bind_compiler_loop_contracts(&mut func, &specs).is_empty());

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    let loop_unknowns = preclassified
        .iter()
        .filter(|(vc, result)| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported")
                && matches!(result, VerificationResult::Unknown { .. })
        })
        .count();
    assert_eq!(loop_unknowns, 2, "both ill-sorted authored clauses must remain visible");
    assert!(!solver_vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::LoopInvariantInitiation { .. }
                | VcKind::LoopInvariantConsecution { .. }
        ) || matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "loop-decreases")
    }));
}

#[test]
fn loop_span_pairing_does_not_leak_clause_to_later_loop() {
    let mut func = counted_loop();
    add_second_loop(&mut func);
    let first = loop_spec(LoopContractKind::Invariant, "i <= n");
    let second = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 1,
        loop_head: span(20, 25),
        header_span: span(20, 22),
        span: span(22, 22),
        body: "i <= n".to_string(),
    };
    assert!(bind_compiler_loop_contracts(&mut func, &[first, second]).is_empty());
    assert_eq!(func.contracts[0].body, "bb1: i <= n");
    assert_eq!(func.contracts[1].body, "bb4: i <= n");
}

#[test]
fn one_source_loop_group_cannot_split_across_inconsistent_span_evidence() {
    let mut func = counted_loop();
    add_second_loop(&mut func);
    let first = loop_spec(LoopContractKind::Invariant, "i <= n");
    let mut same_source_loop = loop_spec(LoopContractKind::Decreases, "n - i");
    same_source_loop.loop_head = span(20, 25);
    same_source_loop.header_span = span(20, 22);
    same_source_loop.span = span(22, 22);

    let failures = bind_compiler_loop_contracts(&mut func, &[first, same_source_loop]);
    assert_eq!(failures.len(), 2, "the whole source-id group must fail closed");
    assert!(
        func.contracts
            .iter()
            .all(|contract| contract.body.starts_with("__trust_unpaired_loop_contract__:")),
        "no clause in an inconsistent source-id group may choose a header independently"
    );
}

#[test]
fn ambiguous_header_span_does_not_choose_the_earliest_loop() {
    let mut func = counted_loop();
    add_second_loop(&mut func);
    let mut invariant = loop_spec(LoopContractKind::Invariant, "i <= n");
    invariant.loop_head = span(9, 25);
    invariant.header_span = span(9, 22);
    let mut decreases = loop_spec(LoopContractKind::Decreases, "n - i");
    decreases.loop_head = invariant.loop_head.clone();
    decreases.header_span = invariant.header_span.clone();

    let failures = bind_compiler_loop_contracts(&mut func, &[invariant, decreases]);
    assert_eq!(failures.len(), 2, "ambiguous evidence must fail every clause in the group");
    assert!(failures.iter().all(|(_, reason)| reason.contains("ambiguously matched 2")));
    assert!(
        func.contracts
            .iter()
            .all(|contract| contract.body.starts_with("__trust_unpaired_loop_contract__:")),
        "source ordering must not silently select bb1"
    );
}

#[test]
fn broad_fallback_span_does_not_choose_first_independent_loop() {
    let mut func = counted_loop();
    add_second_loop(&mut func);
    for header in [1, 4] {
        let Terminator::SwitchInt { span, .. } = &mut func.body.blocks[header].terminator else {
            unreachable!("both loop headers are SwitchInt")
        };
        *span = SourceSpan::default();
    }
    func.body.blocks[5].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
        span: span(23, 23),
    });
    let spec = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 2,
        loop_head: span(9, 25),
        header_span: span(9, 10),
        span: span(10, 10),
        body: "i <= n".to_string(),
    };

    let failures = bind_compiler_loop_contracts(&mut func, &[spec]);
    assert_eq!(failures.len(), 1);
    assert!(
        failures[0].1.contains("span fallback requires exactly one distinct header"),
        "an over-broad fallback span must fail closed instead of selecting bb1: {failures:#?}",
    );
    assert!(func.contracts[0].body.starts_with("__trust_unpaired_loop_contract__:"));
}

#[test]
fn multiple_backedges_to_one_header_are_one_binding_candidate() {
    let mut func = counted_loop();
    // Split the loop body into two possible latches. `detect_loops` reports
    // one natural-loop row per backedge, but both rows carry header bb1.
    func.body.blocks[2].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(3)),
        targets: vec![(1, BlockId(1))],
        otherwise: BlockId(4),
        exhaustive_enum_unreachable: false,
        span: span(13, 13),
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(4),
        stmts: vec![],
        terminator: Terminator::Goto(BlockId(1)),
    });

    let failures = bind_compiler_loop_contracts(
        &mut func,
        &[loop_spec(LoopContractKind::Invariant, "i <= n")],
    );
    assert!(failures.is_empty(), "duplicate backedge rows are not ambiguous: {failures:#?}");
    assert_eq!(func.contracts[0].body, "bb1: i <= n");
}
