//! Original-body admission for enum return inference. The JSON is the genuine
//! C6 `-Ztrust-dump=mir-only` output of the adjacent Rust fixture, sorted by
//! def_path with all twelve free functions retained. It is not a scalarized
//! substitute body. Compiler identity: c6d3ebc2042626ee4a24e77bf33cbf40b916a122.

use trust_types::{Formula, Operand, Place, Projection, Sort, VerifiableFunction};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let functions: Vec<VerifiableFunction> =
        serde_json::from_str(include_str!("fixtures/d5b_enum_helpers.json")).unwrap();
    assert_eq!(functions.len(), 12, "all original free source bodies are retained");
    functions
        .into_iter()
        .find(|function| function.def_path == format!("enum_helpers::{name}"))
        .unwrap()
}

fn access(function: &VerifiableFunction, local: usize, projections: Vec<Projection>) -> Formula {
    trust_vcgen::try_operand_to_formula(function, &Operand::Copy(Place { local, projections }))
        .expect("typed original source field")
}

fn eq(lhs: Formula, rhs: Formula) -> Formula {
    Formula::Eq(Box::new(lhs), Box::new(rhs))
}

fn replace(formula: &Formula, name: &str, replacement: &Formula) -> Formula {
    if formula.var_name() == Some(name) {
        return replacement.clone();
    }
    formula.clone().map_children(&mut |child| replace(&child, name, replacement))
}

// The expected relation is a test oracle for the ORIGINAL decision table,
// never a production contract or source of summary authority.
fn coverage_relation(function: &VerifiableFunction) -> Formula {
    let tag = |local| {
        let place = trust_vcgen::place_to_var_name(function, &Place::local(local));
        Formula::Var(format!("__trust_mir__discr_{place}"), Sort::Int)
    };
    let is = |local, variant| eq(tag(local), Formula::Int(variant));
    let payload = |local, variant| {
        access(function, local, vec![Projection::Downcast(variant), Projection::Field(0)])
    };
    let same_bound = |variant| {
        Formula::And(vec![
            is(1, variant as i128),
            is(2, variant as i128),
            Formula::Ge(Box::new(payload(1, variant)), Box::new(payload(2, variant))),
        ])
    };
    eq(
        Formula::Var("_0".into(), Sort::Bool),
        Formula::Or(vec![
            is(2, 3),
            Formula::And(vec![is(1, 0), Formula::Or(vec![is(2, 0), is(2, 1), is(2, 2)])]),
            same_bound(1),
            same_bound(2),
        ]),
    )
}

#[test]
fn original_payload_enum_body_relation_requires_real_kernel_admission() {
    let source = load("coverage_supports");
    let correct = coverage_relation(&source);
    let wrong = eq(Formula::Var("_0".into(), Sort::Bool), Formula::Bool(true));
    let good_rows =
        trust_vcgen::inferred_enum_return_check_vcs(&source, &correct).unwrap_or_else(|reason| {
            let mut diagnostic = source.clone();
            diagnostic.postconditions = vec![correct.clone()];
            for row in trust_vcgen::generate_vcs(&diagnostic) {
                eprintln!("original enum row: {:?}: {}", row.kind, row.formula.to_smtlib());
            }
            panic!("original-body admission refused: {reason}");
        });
    let bad_rows = trust_vcgen::inferred_enum_return_check_vcs(&source, &wrong).unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let good: Vec<_> =
                good_rows.iter().map(|row| trust_certify::certify_vc(row).is_some()).collect();
            let bad: Vec<_> =
                bad_rows.iter().map(|row| trust_certify::certify_vc(row).is_some()).collect();
            eprintln!("enum original-body kernel admission: correct={good:?}, wrong={bad:?}");
            assert!(
                bad.iter().any(|certified| !certified),
                "wrong relation cannot install a summary"
            );
            assert!(
                good.iter().all(|certified| *certified),
                "every original-body row must kernel-check"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn actual_enum_body_inference_requires_all_original_rows_and_refuses_wrong_candidates() {
    for helper in ["coverage_supports", "signed_tag_is_low"] {
        let source = load(helper);
        let inferred = trust_vcgen::infer_return_candidate(&source)
            .unwrap_or_else(|reason| panic!("{helper}: real enum inference declined: {reason}"));
        let wrong = eq(Formula::Var("_0".into(), Sort::Bool), Formula::Bool(true));
        let wrong_rows = trust_vcgen::inferred_enum_return_check_vcs(&source, &wrong).unwrap();
        std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || {
            let correct: Vec<_> = inferred.check_vcs().iter().map(|row| trust_certify::certify_vc(row).is_some()).collect();
            let wrong: Vec<_> = wrong_rows.iter().map(|row| trust_certify::certify_vc(row).is_some()).collect();
            eprintln!("{helper}: original-body inferred candidate: correct={correct:?}, wrong={wrong:?}, expression={:?}", inferred.postcondition());
            let router = test_router::deterministic_test_router();
            for (index, row) in inferred.check_vcs().iter().enumerate().filter(|(index, _)| !correct[*index]) {
                let result = router.verify_all(std::slice::from_ref(row)).into_iter().next().unwrap().1;
                eprintln!("D5B_ENUM_KERNEL_MISS {index}: solver={result:?}; row={}", serde_json::to_string(row).unwrap());
            }
            assert!(correct.iter().all(|certified| *certified), "all original-body rows must certify");
            assert!(wrong.iter().any(|certified| !certified), "wrong candidate must not mint a summary");
        }).unwrap().join().unwrap();
    }
}

fn checked_summary() -> trust_vcgen::FunctionSummary {
    checked_summary_for("coverage_supports")
}

fn checked_summary_for(name: &str) -> trust_vcgen::FunctionSummary {
    let source = load(name);
    let inferred = trust_vcgen::infer_return_candidate(&source).unwrap();
    assert!(!inferred.check_vcs().is_empty());
    assert!(inferred.check_vcs().iter().all(|row| trust_certify::certify_vc(row).is_some()));
    trust_vcgen::FunctionSummary::new(source.def_path.clone())
        .with_body_inferred_return(&inferred)
        .with_extracted_body(std::sync::Arc::new(source))
}

#[test]
fn checked_enum_return_composes_exact_calls_without_scope_or_name_leaks() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let helper = load("signed_tag_is_low");
            let source = load("signed_tag_forward");
            let inferred = trust_vcgen::infer_return_candidate(&helper).unwrap();
            assert!(
                inferred.check_vcs().iter().all(|row| trust_certify::certify_vc(row).is_some())
            );
            let identity = source
                .body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator {
                    trust_types::Terminator::Call { callee_identity, .. } => *callee_identity,
                    _ => None,
                })
                .unwrap();
            let input = trust_vcgen::InferredReturnCall::new(identity, &inferred).unwrap();
            let mut rows = trust_types::vc_context::VcContext::new();
            let composed = trust_vcgen::infer_return_candidate_with_calls_rows(
                &source,
                std::slice::from_ref(&input),
                &mut rows,
            )
            .expect("original forwarded enum body is in the checked composition fragment");
            assert!(!composed.check_vcs().is_empty());
            assert!(
                composed.check_vcs().iter().all(|row| trust_certify::certify_vc(row).is_some())
            );
            assert!(trust_vcgen::infer_return_candidate(&source).is_err(), "scope must not leak");

            // The genuine forwarding body writes its result straight to _0.
            // That return place is allowed, but an incoming Bool parameter is
            // still immutable even though its type matches the callee result.
            let mut parameter_dest = source.clone();
            parameter_dest.body.arg_count = 2;
            parameter_dest.body.locals.push(trust_types::LocalDecl {
                index: 2,
                ty: trust_types::Ty::Bool,
                name: Some("incoming".into()),
            });
            for block in &mut parameter_dest.body.blocks {
                if let trust_types::Terminator::Call { dest, .. } = &mut block.terminator {
                    *dest = Place::local(2);
                }
            }
            assert!(
                trust_vcgen::infer_return_candidate_with_calls_rows(
                    &parameter_dest,
                    std::slice::from_ref(&input),
                    &mut rows,
                )
                .is_err(),
                "a callee result must not overwrite an incoming parameter"
            );

            let mut other_identity = identity;
            other_identity.def_index = other_identity.def_index.wrapping_add(1);
            let impostor = trust_vcgen::InferredReturnCall::new(other_identity, &inferred).unwrap();
            assert!(
                trust_vcgen::infer_return_candidate_with_calls_rows(
                    &source,
                    std::slice::from_ref(&impostor),
                    &mut rows,
                )
                .is_err(),
                "same name cannot replace an exact callee identity"
            );
            assert!(
                trust_vcgen::infer_return_candidate_with_calls_rows(
                    &source,
                    &[input.clone(), impostor],
                    &mut rows,
                )
                .is_err(),
                "different identities cannot share a name-keyed summary"
            );

            let mut renamed = source.clone();
            for block in &mut renamed.body.blocks {
                if let trust_types::Terminator::Call { func, .. } = &mut block.terminator {
                    *func = "unrelated::same_spelling".into();
                }
            }
            assert!(
                trust_vcgen::infer_return_candidate_with_calls_rows(
                    &renamed,
                    std::slice::from_ref(&input),
                    &mut rows,
                )
                .is_err(),
                "identity and body name must agree"
            );

            let mut cyclic = source.clone();
            for block in &mut cyclic.body.blocks {
                if let trust_types::Terminator::Call { target, .. } = &mut block.terminator {
                    *target = Some(trust_types::BlockId(0));
                }
            }
            assert!(
                trust_vcgen::infer_return_candidate_with_calls_rows(&cyclic, &[input], &mut rows,)
                    .is_err(),
                "call continuation cycles must refuse"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn actual_fieldless_enum_caller_retains_signed_tags_and_checked_domain() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = load("signed_tag_forward");
            let expected = eq(access(&source, 1, vec![]), Formula::Int(-3));
            let summary = checked_summary_for("signed_tag_is_low");
            let before = caller_rows(source.clone(), expected.clone(), None);
            let after = caller_rows(source.clone(), expected.clone(), Some(summary.clone()));
            let wrong = caller_rows(source, Formula::Not(Box::new(expected)), Some(summary));
            assert_eq!((before.len(), after.len(), wrong.len()), (1, 1, 1));
            assert!(!before[0].proved && !before[0].certified && before[0].held.is_some());
            assert!(after[0].proved && after[0].certified);
            assert!(wrong[0].refuted && !wrong[0].certified && wrong[0].held.is_none());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[derive(Debug)]
struct CallerRow {
    proved: bool,
    refuted: bool,
    certified: bool,
    held: Option<String>,
}

fn caller_rows(
    mut source: VerifiableFunction,
    expected: Formula,
    summary: Option<trust_vcgen::FunctionSummary>,
) -> Vec<CallerRow> {
    source.postconditions = vec![eq(Formula::Var("_0".into(), Sort::Bool), expected)];
    let key = source
        .body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            trust_types::Terminator::Call { callee_identity: Some(identity), .. } => {
                Some((identity.stable_crate_id, identity.def_index))
            }
            _ => None,
        })
        .expect("genuine identified helper call");
    let mut db = trust_vcgen::SummaryDatabase::new();
    if let Some(summary) = summary {
        db.insert(summary);
    }
    let db = db.definitional_precondition_free_subset();
    let context = trust_vcgen::VcgenContext::for_function(source.def_path.clone())
        .with_local_call_dest_screen(trust_vcgen::LocalCallDestScreen::new([key], &db));
    let (rows, discharged) = trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        &source, &db, false, &context, &std::collections::HashSet::new(),
    );
    let scope = trust_vcgen::GenericRefutationScope::for_function_with_call_dests(
        &source,
        &rows,
        &discharged,
        &context,
    );
    let router = test_router::deterministic_test_router();
    rows.iter()
        .filter(|row| matches!(row.kind, trust_types::VcKind::Postcondition))
        .map(|row| {
            let result = router.verify_all(std::slice::from_ref(row)).into_iter().next().unwrap().1;
            if !matches!(result, trust_types::VerificationResult::Proved { .. })
                && std::env::var_os("TRUST_ENUM_CALLER_DEBUG").is_some()
            {
                eprintln!(
                    "D5B_ENUM_CALLER_MISS result={result:?}, row={}",
                    serde_json::to_string(row).unwrap()
                );
            }
            CallerRow {
                proved: matches!(result, trust_types::VerificationResult::Proved { .. }),
                refuted: matches!(result, trust_types::VerificationResult::Failed { .. }),
                certified: trust_certify::certify_vc(row).is_some(),
                held: scope.rejection_reason(row),
            }
        })
        .collect()
}

#[test]
fn actual_callers_keep_discriminants_distinct_from_payload_and_bind_arguments_in_order() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let summary = checked_summary();
            for (name, expected) in [
                ("coverage_reflexive", Formula::Bool(true)),
                ("coverage_wrong", Formula::Bool(false)),
                ("coverage_constants", Formula::Bool(true)),
                ("coverage_bounded_against_unbounded", Formula::Bool(false)),
                ("coverage_zero_against_unbounded", Formula::Bool(false)),
                ("coverage_large_against_unbounded", Formula::Bool(false)),
                ("coverage_unbounded_against_bounded", Formula::Bool(true)),
                (
                    "coverage_depths",
                    Formula::Ge(
                        Box::new(access(&load("coverage_depths"), 1, vec![])),
                        Box::new(access(&load("coverage_depths"), 2, vec![])),
                    ),
                ),
                (
                    "coverage_depths_reversed",
                    Formula::Ge(
                        Box::new(access(&load("coverage_depths_reversed"), 2, vec![])),
                        Box::new(access(&load("coverage_depths_reversed"), 1, vec![])),
                    ),
                ),
            ] {
                let source = load(name);
                let before = caller_rows(source.clone(), expected.clone(), None);
                let after = caller_rows(source.clone(), expected.clone(), Some(summary.clone()));
                let wrong =
                    caller_rows(source, Formula::Not(Box::new(expected)), Some(summary.clone()));
                eprintln!(
                    "D5B_ENUM_CALLER {name}: before={before:?}, after={after:?}, wrong={wrong:?}"
                );
                assert_eq!(before.len(), 1, "{name}: original caller postcondition retained");
                assert_eq!(after.len(), 1, "{name}: original caller postcondition retained");
                assert_eq!(wrong.len(), 1, "{name}: wrong caller postcondition retained");
                assert!(!before[0].proved && !before[0].certified, "{name}: control needs summary");
                assert!(after[0].proved && after[0].certified, "{name}: exact original relation");
                assert!(
                    wrong[0].refuted && !wrong[0].certified && wrong[0].held.is_none(),
                    "{name}: genuine contrary result must stay refuted: {wrong:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn swapped_payload_and_tag_candidates_fail_original_body_kernel_checks() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = load("coverage_supports");
            let relation = coverage_relation(&source);
            let tag = Formula::Var("__trust_mir__discr_far".into(), Sort::Int);
            let payload = access(&source, 1, vec![Projection::Downcast(1), Projection::Field(0)]);
            let Formula::Var(payload_name, _) = &payload else { panic!("typed payload variable") };
            for mutant in [
                replace(&relation, "__trust_mir__discr_far", &payload),
                replace(&relation, payload_name, &tag),
                replace(
                    &replace(
                        &replace(
                            &relation,
                            "__trust_mir__discr_far",
                            &Formula::Var("__swap".into(), Sort::Int),
                        ),
                        payload_name,
                        &tag,
                    ),
                    "__swap",
                    &payload,
                ),
            ] {
                assert_ne!(relation, mutant, "the mutant must change a real used channel");
                let rows = trust_vcgen::inferred_enum_return_check_vcs(&source, &mutant).unwrap();
                assert!(
                    rows.iter().any(|row| trust_certify::certify_vc(row).is_none()),
                    "a swapped tag/payload relation cannot mint a summary"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn typed_entry_binding_and_sat_screen_refuse_foreign_mutated_aliased_or_redefined_actuals() {
    use trust_types::{Rvalue, SourceSpan, Statement, Ty};
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let summary = checked_summary();
            let source = load("coverage_reflexive");
            let mut mutants = Vec::new();

            let mut foreign = source.clone();
            let Ty::Adt { name, .. } = &mut foreign.body.locals[2].ty else {
                panic!("enum actual")
            };
            *name = "foreign::CoverageBound".into();
            mutants.push(("foreign nominal owner", foreign, summary.clone()));

            let mut reordered = summary.clone();
            reordered.param_names.swap(0, 1);
            mutants.push(("changed public formal order", source.clone(), reordered));
            let mut changed_clause = summary.clone();
            changed_clause.postconditions = vec![Formula::Bool(true)];
            mutants.push(("changed public clause", source.clone(), changed_clause));
            let forged = trust_vcgen::FunctionSummary::new(summary.name.clone())
                .with_param_names(summary.param_names.clone())
                .with_definitional_postcondition(summary.postconditions[0].clone());
            mutants.push(("unsealed projected clause", source.clone(), forged));

            let mut redefined = source.clone();
            let original_construction = redefined.body.blocks[0].stmts[0].clone();
            redefined.body.blocks[1].stmts.insert(0, original_construction);
            mutants.push(("actual rewritten after call", redefined, summary.clone()));

            let mut aliased = source.clone();
            let local = aliased.body.locals.len();
            aliased.body.locals.push(trust_types::LocalDecl {
                index: local,
                name: None,
                ty: Ty::RawPtr {
                    mutable: false,
                    pointee: Box::new(aliased.body.locals[2].ty.clone()),
                },
            });
            aliased.body.blocks[0].stmts.push(Statement::Assign {
                place: Place::local(local),
                rvalue: Rvalue::AddressOf(false, Place::local(2)),
                span: SourceSpan::default(),
            });
            mutants.push(("actual storage address escapes", aliased, summary.clone()));

            let mut foreign_constructor = source.clone();
            let Statement::Assign {
                rvalue: Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
                ..
            } = &mut foreign_constructor.body.blocks[0].stmts[0]
            else {
                unreachable!()
            };
            *name = "foreign::CoverageBound".into();
            mutants.push((
                "constructor owner differs from declared type",
                foreign_constructor,
                summary.clone(),
            ));

            let mut projected = source.clone();
            let local = projected.body.locals.len();
            projected.body.locals.push(trust_types::LocalDecl {
                index: local,
                name: None,
                ty: Ty::Tuple(vec![projected.body.locals[2].ty.clone()]),
            });
            projected.body.blocks[0].stmts.push(Statement::Assign {
                place: Place::local(local),
                rvalue: Rvalue::Aggregate(
                    trust_types::AggregateKind::Tuple,
                    vec![Operand::Copy(Place::local(2))],
                ),
                span: SourceSpan::default(),
            });
            let trust_types::Terminator::Call { args, .. } =
                &mut projected.body.blocks[0].terminator
            else {
                unreachable!()
            };
            args[0] = Operand::Move(Place { local, projections: vec![Projection::Field(0)] });
            mutants.push((
                "projected enum history lacks a checked tag binding",
                projected,
                summary.clone(),
            ));

            for (label, operand) in [
                (
                    "untyped symbolic actual",
                    Operand::Symbolic(Formula::Var("forged_enum".into(), Sort::Int)),
                ),
                (
                    "untyped scalar constant actual",
                    Operand::Constant(trust_types::ConstValue::Uint(1, 64)),
                ),
                (
                    "payload field used as enum actual",
                    Operand::Copy(Place { local: 2, projections: vec![Projection::Field(0)] }),
                ),
            ] {
                let mut changed = source.clone();
                let trust_types::Terminator::Call { args, .. } =
                    &mut changed.body.blocks[0].terminator
                else {
                    unreachable!()
                };
                args[0] = operand;
                mutants.push((label, changed, summary.clone()));
            }

            for (label, caller, summary) in mutants {
                let rows = caller_rows(caller, Formula::Bool(true), Some(summary));
                assert_eq!(rows.len(), 1, "{label}: keep the original postcondition");
                assert!(
                    !rows[0].proved && !rows[0].certified,
                    "{label}: cannot authorize a proof: {rows:?}"
                );
                assert!(
                    rows[0].held.is_some(),
                    "{label}: rejected binding cannot grant SAT credit: {rows:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn actual_enum_copy_chain_keeps_one_typed_value_and_refuses_a_rewritten_origin() {
    use trust_types::{Rvalue, SourceSpan, Statement};
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let summary = checked_summary();
            let mut source = load("coverage_reflexive");
            let local = source.body.locals.len();
            source.body.locals.push(trust_types::LocalDecl {
                index: local,
                name: None,
                ty: source.body.locals[2].ty.clone(),
            });
            source.body.blocks[0].stmts.push(Statement::Assign {
                place: Place::local(local),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            });
            let trust_types::Terminator::Call { args, .. } = &mut source.body.blocks[0].terminator
            else {
                unreachable!()
            };
            args[0] = Operand::Move(Place::local(local));
            let after = caller_rows(source.clone(), Formula::Bool(true), Some(summary.clone()));
            let wrong = caller_rows(source.clone(), Formula::Bool(false), Some(summary.clone()));
            assert_eq!((after.len(), wrong.len()), (1, 1));
            assert!(after[0].proved && after[0].certified);
            assert!(wrong[0].refuted && !wrong[0].certified && wrong[0].held.is_none());

            let original_construction = source.body.blocks[0].stmts[0].clone();
            source.body.blocks[1].stmts.insert(0, original_construction);
            let refused = caller_rows(source, Formula::Bool(true), Some(summary));
            assert_eq!(refused.len(), 1);
            assert!(
                !refused[0].proved && !refused[0].certified && refused[0].held.is_some(),
                "a copy cannot launder its rewritten tag/payload origin: {refused:?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn enum_inference_refuses_unsupported_shapes_names_and_unreachable_effects() {
    use trust_types::{
        AdtKind, BasicBlock, BlockId, Rvalue, SourceSpan, Statement, Terminator, Ty,
    };
    let source = load("coverage_supports");
    let mut mutants = Vec::new();
    for kind in [None, Some(AdtKind::Struct), Some(AdtKind::Union)] {
        let mut changed = source.clone();
        let Ty::Adt { adt_kind, .. } = &mut changed.body.locals[1].ty else { unreachable!() };
        *adt_kind = kind;
        mutants.push(("non-enum or missing kind", changed));
    }
    let mut hidden_binder = source.clone();
    hidden_binder.body.locals[1].ty =
        Ty::Unsupported { kind: "TyKind::Alias".into(), detail: "opaque associated output".into() };
    mutants.push(("opaque alias parameter", hidden_binder));
    let mut huge_width = source.clone();
    let Ty::Adt { fields, .. } = &mut huge_width.body.locals[1].ty else { unreachable!() };
    let mut changed_fields = fields.to_vec();
    changed_fields[1].1 = Ty::Int { width: 128, signed: false };
    *fields = changed_fields.into();
    let Ty::Adt { variants, .. } = &mut huge_width.body.locals[1].ty else { unreachable!() };
    let mut changed_variants = variants.to_vec();
    changed_variants[1].fields[0].1 = Ty::Int { width: 128, signed: false };
    *variants = changed_variants.into();
    mutants.push(("unsupported payload width", huge_width));
    let mut malformed_tags = source.clone();
    let Ty::Adt { variants, .. } = &mut malformed_tags.body.locals[1].ty else { unreachable!() };
    let mut changed_variants = variants.to_vec();
    changed_variants[1].discriminant = changed_variants[0].discriminant;
    *variants = changed_variants.into();
    mutants.push(("duplicate tag", malformed_tags));
    let mut reassigned = source.clone();
    reassigned.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        },
    );
    mutants.push(("parameter written", reassigned));
    let mut hidden_effect = source.clone();
    hidden_effect.body.blocks.push(BasicBlock {
        id: BlockId(hidden_effect.body.blocks.len()),
        stmts: vec![Statement::Unsupported {
            kind: "hidden-effect".into(),
            detail: "unreachable is still scanned".into(),
            operands: vec![],
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Unreachable,
    });
    mutants.push(("unreachable unsupported effect", hidden_effect));
    let mut hidden_drop = source.clone();
    hidden_drop.body.blocks.push(BasicBlock {
        id: BlockId(hidden_drop.body.blocks.len()),
        stmts: vec![],
        terminator: Terminator::Drop {
            place: Place::local(1),
            target: BlockId(0),
            span: SourceSpan::default(),
            unwind: trust_types::UnwindEdge::Unreachable,
        },
    });
    mutants.push(("unreachable drop", hidden_drop));
    let mut hidden_call = source.clone();
    hidden_call.body.blocks.push(BasicBlock {
        id: BlockId(hidden_call.body.blocks.len()),
        stmts: vec![],
        terminator: load("coverage_reflexive").body.blocks[0].terminator.clone(),
    });
    mutants.push(("unreachable user call", hidden_call));
    let mut opaque = source.clone();
    opaque.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Symbolic(Formula::Bool(true))),
            span: SourceSpan::default(),
        },
    );
    mutants.push(("overwritten opaque operand", opaque));
    let mut authored = source.clone();
    authored.postconditions.push(Formula::Bool(true));
    mutants.push(("authored clause", authored));
    for (label, mutant) in mutants {
        assert!(trust_vcgen::infer_return_candidate(&mutant).is_err(), "{label}: must decline");
    }
}

#[test]
fn enum_parameter_source_name_collisions_keep_existing_unique_formula_channels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            for name in ["needs", "_0", "__trust_mir__discr_needs"] {
                let mut source = load("coverage_supports");
                source.body.locals[1].name = Some(name.into());
                let inferred = trust_vcgen::infer_return_candidate(&source).unwrap();
                assert_ne!(inferred.param_names()[0], inferred.param_names()[1]);
                assert!(inferred.param_names().iter().all(|name| name != "_0"));
                assert!(
                    inferred.check_vcs().iter().all(|row| trust_certify::certify_vc(row).is_some()),
                    "{name}: existing name demotion preserves every original-body check"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
