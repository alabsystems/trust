// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn function(ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "crc_poly_select".into(),
        def_path: "test::crc_poly_select".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("crc".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
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

#[test]
fn unsigned_literal_remainder_admission_is_domain_bound() {
    let unsigned = function(Ty::u32());
    for source in ["crc % 2 == 0", "crc % 1 == 0", "crc % 4294967295 < 4294967295"] {
        let formula = parse_spec_expr(source).unwrap();
        assert!(formula_uses_unmodeled_machine_arithmetic(&formula), "context-free filter");
        assert!(
            !formula_uses_unmodeled_machine_arithmetic_in_function(&unsigned, &formula),
            "total unsigned literal remainder must keep its exact Int reading: {source}",
        );
    }
    for source in [
        "crc % 0 == 0",
        "crc % -1 == 0",
        "crc % crc == 0",
        "crc % 4294967296 == 0",
        "(crc + 1) % 2 == 0",
        "crc / 2 == 0",
        "missing % 2 == 0",
        "crc % 2 + 1 == 1",
    ] {
        let formula = parse_spec_expr(source).unwrap();
        assert!(
            formula_uses_unmodeled_machine_arithmetic_in_function(&unsigned, &formula),
            "{source}"
        );
    }
    let rem = parse_spec_expr("crc % 2 == 0").unwrap();
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(&function(Ty::i32()), &rem));
    let signed_overflow = parse_spec_expr("crc % -1 == 0").unwrap();
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(
        &function(Ty::i32()),
        &signed_overflow
    ));
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(
        &function(Ty::PtrSizedInt { signed: false }),
        &rem
    ));
    let mut ambiguous = unsigned.clone();
    ambiguous.body.locals.push(LocalDecl { index: 2, ty: Ty::i32(), name: Some("crc".into()) });
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(&ambiguous, &rem));
    let mut misplaced = unsigned.clone();
    misplaced.body.locals[1].index = 7;
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(&misplaced, &rem));
    let quantified = Formula::Forall(vec![("crc".into(), Sort::Int)], Box::new(rem));
    assert!(formula_uses_unmodeled_machine_arithmetic_in_function(&unsigned, &quantified));
}

fn postcondition_rows(function: &VerifiableFunction) -> Vec<VerificationCondition> {
    crate::generate_vcs(function)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

#[test]
fn unsigned_literal_remainder_generated_value_and_range_vcs_certify_and_replay() {
    let mut function = function(Ty::u32());
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Rem,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(2, 32)),
        ),
        span: SourceSpan::default(),
    };
    function.preconditions.push(
        crate::range::rust_type_range_constraint(&Formula::var("crc", Sort::Int), &Ty::u32())
            .unwrap(),
    );
    for source in ["result == crc % 2", "result < 2"] {
        function.contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: function.span.clone(),
            body: source.into(),
        }];
        let rows = postcondition_rows(&function);
        assert_eq!(rows.len(), 1, "{source}");
        let vc = &rows[0];
        let (certificate, stop) = trust_certify::certify_vc_reporting_stop(vc);
        let certificate = certificate
            .unwrap_or_else(|| panic!("missing Clean certificate: {source}, {stop:?}, {vc:?}"));
        assert!(trust_certify::replay_vc_evidence(vc, &certificate));
        for field in ["term", "context"] {
            let mut wire = serde_json::to_value(&certificate).unwrap();
            let payload = wire.get_mut("CleanCic").expect("actual CIC evidence");
            assert!(payload.get(field).unwrap().as_array().is_some_and(|bytes| !bytes.is_empty()));
            payload[field] = serde_json::json!([255]);
            let tampered = serde_json::from_value(wire).unwrap();
            assert!(!trust_certify::replay_vc_evidence(vc, &tampered), "tampered {field}");
        }
        let mut changed = vc.clone();
        changed.function = format!("{}::other", changed.function).into();
        assert!(!trust_certify::replay_vc_evidence(&changed, &certificate));
        changed = vc.clone();
        changed.formula = Formula::Bool(true);
        assert!(!trust_certify::replay_vc_evidence(&changed, &certificate));
    }
    // Still a real false claim about a defined operation, never an unsupported
    // clause or a kernel certificate for a replacement goal.
    function.contracts = vec![Contract {
        kind: ContractKind::Ensures,
        span: function.span.clone(),
        body: "result == 0".into(),
    }];
    let rows = postcondition_rows(&function);
    assert_eq!(rows.len(), 1);
    assert!(trust_certify::certify_vc(&rows[0]).is_none());
    let backend = trust_router::InProcessAyBackend::new();
    assert!(matches!(
        trust_router::VerificationBackend::verify(&backend, &rows[0]),
        trust_types::VerificationResult::Failed { .. }
    ));
}

#[test]
fn unsigned_literal_remainder_crc_summary_preserves_goal_and_negative_controls() {
    const CALLEE: &str = "clean_origin::crc32_poly_select";
    let mut function = function(Ty::u32());
    function.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: None });
    function.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: CALLEE.into(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: function.span.clone(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: trust_types::UnwindEdge::Unreachable,
                callee_identity: None,
                callee_key: None,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: function.span.clone(),
            }],
            terminator: Terminator::Return,
        },
    ];
    function.preconditions.push(
        crate::range::rust_type_range_constraint(&Formula::var("crc", Sort::Int), &Ty::u32())
            .unwrap(),
    );
    let var = |name: &str| Box::new(Formula::var(name, Sort::Int));
    let lit = |value| Box::new(Formula::Int(value));
    // The exact existing Clean-origin SelectBeqGeneral definitional carrier.
    // This test supplies compiler facts, not evidence for a source declaration.
    let summary = crate::clean_origin_summary(
        CALLEE,
        vec!["arg".into()],
        vec![Formula::Eq(
            var("_0"),
            Box::new(Formula::Ite(
                Box::new(Formula::Eq(Box::new(Formula::Rem(var("arg"), lit(2))), lit(0))),
                lit(0),
                lit(3988292384),
            )),
        )],
        &[],
    )
    .unwrap();
    let mut summaries = crate::SummaryDatabase::new();
    summaries.insert(summary);
    for (source, expected_proved) in [
        ("(crc % 2 == 0 && result == 0) || (crc % 2 == 1 && result == 3988292384)", true),
        ("result == 0", false),
        ("(crc % 2 == 0 && result == 3988292384) || (crc % 2 == 1 && result == 0)", false),
    ] {
        function.contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: function.span.clone(),
            body: source.into(),
        }];
        let rows: Vec<_> = crate::generate::generate_vcs_with_summaries(&function, &summaries)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .collect();
        assert_eq!(rows.len(), 1, "original clause must not become SpecUnverifiable: {source}");
        let backend = trust_router::InProcessAyBackend::new();
        let result = trust_router::VerificationBackend::verify(&backend, &rows[0]);
        let original_post = parse_spec_expr(source).unwrap();
        let mut has_original_negated_goal = false;
        rows[0].formula.visit(&mut |node| {
            if matches!(node, Formula::Not(goal) if goal.as_ref() == &original_post) {
                has_original_negated_goal = true;
            }
        });
        assert!(has_original_negated_goal, "the original clause must remain the violation goal");
        eprintln!("CRC actual VC: {}", serde_json::to_string(&rows[0]).unwrap());
        eprintln!("CRC actual AY: {result:?}");
        assert_eq!(
            rows[0].contract_metadata.as_ref().and_then(|metadata| metadata.source_contract_index),
            Some(0),
        );
        if expected_proved {
            // Admission is the contract of this regression. The pinned AY
            // strict checker currently withholds this true formula's UNSAT
            // proof (unverified trust rule), and Clean can decline its fragment.
            // Neither Unknown nor a missing certificate is a proof. The native
            // UI check-pass expectation remains unchanged and pending.
            assert!(
                !matches!(result, trust_types::VerificationResult::Failed { .. }),
                "{result:?}"
            );
        } else {
            assert!(matches!(result, trust_types::VerificationResult::Failed { .. }), "{result:?}");
        }
        let (certificate, stop) = trust_certify::certify_vc_reporting_stop(&rows[0]);
        eprintln!(
            "CRC source={source:?}: Clean={}, stop={stop:?}, formula={:?}",
            certificate.is_some(),
            rows[0].formula
        );
        if let Some(certificate) = certificate {
            assert!(expected_proved, "a satisfiable neighbor must not certify");
            assert!(trust_certify::replay_vc_evidence(&rows[0], &certificate));
        }
    }
}
