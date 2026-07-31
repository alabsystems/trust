#![allow(rustc::symbol_intern_string_literal)]

use super::*;

fn hir_contract_clause(ordinal: u32) -> rustc_hir::ContractClause {
    rustc_hir::ContractClause {
        span: rustc_span::DUMMY_SP,
        origin: ContractClauseOrigin::Attribute,
        citation: None,
        payload: None,
        ordinal,
        predicate_hir_id: None,
    }
}

#[test]
fn dense_contract_indices_follow_global_authored_ordinals_with_equal_spans() {
    let requires = [hir_contract_clause(1), hir_contract_clause(5)];
    let ensures = [hir_contract_clause(0), hir_contract_clause(3), hir_contract_clause(4)];
    let decreases = [hir_contract_clause(2)];

    let ordered = restore_hir_contract_authored_order(&requires, &ensures, &decreases).unwrap();
    assert_eq!(
        ordered
            .iter()
            .map(|entry| (entry.kind, entry.clause.ordinal, entry.clause.span))
            .collect::<Vec<_>>(),
        [
            (TrustContractKind::Ensures, 0, rustc_span::DUMMY_SP),
            (TrustContractKind::Requires, 1, rustc_span::DUMMY_SP),
            (TrustContractKind::Decreases, 2, rustc_span::DUMMY_SP),
            (TrustContractKind::Ensures, 3, rustc_span::DUMMY_SP),
            (TrustContractKind::Ensures, 4, rustc_span::DUMMY_SP),
            (TrustContractKind::Requires, 5, rustc_span::DUMMY_SP),
        ]
    );
}

#[test]
fn malformed_hir_contract_ordinals_fail_closed() {
    let duplicate_requires = [hir_contract_clause(0)];
    let duplicate_ensures = [hir_contract_clause(0)];
    assert_eq!(
        restore_hir_contract_authored_order(&duplicate_requires, &duplicate_ensures, &[])
            .map(|_| ()),
        Err(HirContractOrderError::DuplicateOrdinal { ordinal: 0 })
    );

    let out_of_range = [hir_contract_clause(2)];
    assert_eq!(
        restore_hir_contract_authored_order(&out_of_range, &[], &[]).map(|_| ()),
        Err(HirContractOrderError::OrdinalOutOfRange {
            kind: TrustContractKind::Requires,
            ordinal: 2,
            total: 1,
        })
    );
}

#[test]
fn summary_counts_function_and_loop_decreases_in_one_semantic_lane() {
    let summary = checked_contract_summary(2, 1, 3, 1, 2, 4).unwrap();

    assert_eq!(summary.total, 9);
    assert_eq!(summary.requires, 2);
    assert_eq!(summary.ensures, 1);
    assert_eq!(summary.invariants, 3);
    assert_eq!(summary.decreases, 3);
    assert_eq!(summary.opaque, 4);
}

#[test]
fn summary_count_overflow_fails_closed() {
    assert!(
        checked_contract_summary(u32::MAX as usize, 1, 0, 0, 0, 0).is_none(),
        "the total must not wrap past u32::MAX"
    );
    assert!(
        checked_contract_summary(0, 0, 0, u32::MAX as usize, 1, 0).is_none(),
        "combined function and loop decreases must not wrap"
    );
}

fn with_test_session_globals<R>(f: impl FnOnce() -> R) -> R {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::DEFAULT_EDITION, |_| f())
}

fn lowered_text(
    kind: TrustContractKind,
    origin: ContractClauseOrigin,
    body: &str,
) -> Option<String> {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    // Native syntax fixtures exercise the parser independently of a TyCtxt;
    // provide the exact scalar environment their sample `x`/`result` names
    // stand for so the production scope gate remains active in unit tests.
    let native_domains = [
        LoweredVariableDomain {
            name: "_0".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
        LoweredVariableDomain {
            name: "x".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
    ];
    let domains =
        if origin == ContractClauseOrigin::Native { native_domains.as_slice() } else { &[] };
    with_test_session_globals(|| {
        match lower_contract_snippet_body_with_domains(body, kind, origin, domains)? {
            TrustContractPredicateKind::Typed { text, .. }
            | TrustContractPredicateKind::Opaque { text } => {
                Some(text.as_str().strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX)?.to_string())
            }
            _ => None,
        }
    })
}

#[test]
fn native_function_clauses_fail_closed_on_unknown_source_names() {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    let domains = [
        LoweredVariableDomain {
            name: "_0".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
        LoweredVariableDomain {
            name: "x".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
    ];
    with_test_session_globals(|| {
        assert_eq!(
            lower_contract_snippet_body_with_domains(
                "result == ghost",
                TrustContractKind::Ensures,
                ContractClauseOrigin::Native,
                &domains,
            ),
            None,
        );
        assert!(
            lower_contract_snippet_body_with_domains(
                "result == x",
                TrustContractKind::Ensures,
                ContractClauseOrigin::Native,
                &domains,
            )
            .is_some()
        );
    });
}

#[test]
fn canonical_lowering_mints_an_exact_structural_query_proposition() {
    use rustc_middle::mir::trust_contract::{
        TrustContractProposition as Proposition, TrustContractPropositionDomain as Domain,
    };

    with_test_session_globals(|| {
        let TrustContractPredicateKind::Typed { text, proposition } =
            lowered_contract_text_with_domains(
                "(x) == (result)".to_string(),
                &[
                    LoweredVariableDomain {
                        name: "_0".to_string(),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    },
                    LoweredVariableDomain {
                        name: "x".to_string(),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    },
                ],
            )
        else {
            panic!("supported canonical comparison must be structurally typed")
        };
        assert_eq!(text.as_str(), "__trust_lowered_compiler_contract__:(x) == (result)");
        assert_eq!(
            proposition,
            Proposition::Eq(
                Box::new(Proposition::Var {
                    name: Symbol::intern("x"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
                Box::new(Proposition::Var {
                    name: Symbol::intern("_0"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
            )
        );

        assert!(matches!(
            lowered_contract_text("forall(i, 0..1, i == i)".to_string()),
            TrustContractPredicateKind::Opaque { .. }
        ));
    });
}

#[test]
fn loop_predicate_source_bindings_are_exact_used_hir_locals_only() {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    with_test_session_globals(|| {
        let predicate = lowered_contract_text_with_domains(
            "inner < limit".to_string(),
            &[
                LoweredVariableDomain {
                    name: "inner".to_string(),
                    domain: Domain::MachineInt { width: 32, signed: false },
                },
                LoweredVariableDomain {
                    name: "limit".to_string(),
                    domain: Domain::MachineInt { width: 32, signed: false },
                },
            ],
        );
        let bindings = exact_predicate_source_bindings(
            &predicate,
            &[
                LoweredSourceBinding { name: "outer".to_string(), hir_local_id: 7 },
                LoweredSourceBinding { name: "inner".to_string(), hir_local_id: 11 },
                LoweredSourceBinding { name: "limit".to_string(), hir_local_id: 13 },
            ],
        );
        assert_eq!(
            bindings
                .iter()
                .map(|binding| (binding.name.as_str(), binding.hir_local_id))
                .collect::<Vec<_>>(),
            vec![("inner", 11), ("limit", 13)],
            "unused visible bindings must not enter predicate provenance",
        );

        let ambiguous = exact_predicate_source_bindings(
            &predicate,
            &[
                LoweredSourceBinding { name: "inner".to_string(), hir_local_id: 11 },
                LoweredSourceBinding { name: "inner".to_string(), hir_local_id: 17 },
                LoweredSourceBinding { name: "limit".to_string(), hir_local_id: 13 },
            ],
        );
        assert!(
            ambiguous.iter().all(|binding| binding.name.as_str() != "inner"),
            "a conflicting source identity must fail closed instead of choosing one local",
        );

        let synthesized = lowered_contract_text_with_domains(
            "xs_len > 0".to_string(),
            &[LoweredVariableDomain {
                name: "xs_len".to_string(),
                domain: Domain::PointerSizedInt { width: 64, signed: false },
            }],
        );
        assert!(
            exact_predicate_source_bindings(&synthesized, &[]).is_empty(),
            "a synthesized projection leaf must not acquire whole-local authority",
        );
    });
}

#[test]
fn structural_query_identity_carries_bool_width_and_signedness() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractPropositionDomain as Domain,
    };

    with_test_session_globals(|| {
        let lower = |domain| {
            lowered_contract_text_with_domains(
                "x == x".to_string(),
                &[LoweredVariableDomain { name: "x".to_string(), domain }],
            )
        };
        let u8_tree = lower(Domain::MachineInt { width: 8, signed: false });
        let u16_tree = lower(Domain::MachineInt { width: 16, signed: false });
        let i8_tree = lower(Domain::MachineInt { width: 8, signed: true });
        let usize_tree = lower(Domain::PointerSizedInt { width: 64, signed: false });
        let bool_tree = lower(Domain::Bool);
        assert!(matches!(u8_tree, Predicate::Typed { .. }));
        assert!(matches!(bool_tree, Predicate::Typed { .. }));
        assert_ne!(u8_tree, u16_tree);
        assert_ne!(u8_tree, i8_tree);
        assert_ne!(u16_tree, usize_tree);
        assert_ne!(u8_tree, bool_tree);

        assert!(matches!(
            lowered_contract_text_with_domains(
                "x == true".to_string(),
                &[LoweredVariableDomain {
                    name: "x".to_string(),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }],
            ),
            Predicate::Opaque { .. }
        ));
        assert!(matches!(
            lowered_contract_text_with_domains("x == x".to_string(), &[]),
            Predicate::Opaque { .. }
        ));
    });
}

#[test]
fn snippet_fallback_lowers_public_sample_requires() {
    assert_eq!(
        lowered_text(
            TrustContractKind::Requires,
            ContractClauseOrigin::Attribute,
            "numerator >= 0 && denominator > 0"
        )
        .as_deref(),
        Some("((numerator) >= (0)) && ((denominator) > (0))")
    );
    assert_eq!(
        lowered_text(TrustContractKind::Requires, ContractClauseOrigin::Attribute, "low <= high")
            .as_deref(),
        Some("(low) <= (high)")
    );
}

#[test]
fn snippet_fallback_lowers_public_sample_ensures_closures() {
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "|ret| *ret >= 0"
        )
        .as_deref(),
        Some("(result) >= (0)")
    );
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "move |ret| *ret >= low"
        )
        .as_deref(),
        Some("(result) >= (low)")
    );
}

#[test]
fn snippet_fallback_lowers_integer_negation() {
    // `ensures(|r| *r == -x)` (abs). The leading `-` must lower to `-(...)`, which
    // the spec parser reads as `Formula::Neg` — previously the whole predicate was
    // rejected as unsupported, false-refuting valid negation postconditions.
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "move |r| *r == -x"
        )
        .as_deref(),
        Some("(result) == (-(x))")
    );
    assert_eq!(
        lowered_text(TrustContractKind::Requires, ContractClauseOrigin::Attribute, "x > -y")
            .as_deref(),
        Some("(x) > (-(y))")
    );
}

#[test]
fn snippet_fallback_lowers_division_and_modulo() {
    // `ensures(|r| *r == x / 2)` / `*r == x % 100`. The spec parser reads `/`/`%`
    // (parse_mul_div); div-by-zero/overflow are SEPARATE obligations, and the
    // predicate's division term matches the body's, so a correct postcondition
    // discharges and a wrong one is never falsely proved (Unknown/runtime-checked).
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "move |r| *r == x / 2"
        )
        .as_deref(),
        Some("(result) == ((x) / (2))")
    );
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "move |r| *r == x % 100"
        )
        .as_deref(),
        Some("(result) == ((x) % (100))")
    );
}

#[test]
fn snippet_fallback_extracts_attribute_body() {
    assert_eq!(
        contract_body_from_clause_snippet(
            "#[ensures(move |ret| *ret >= low)]",
            TrustContractKind::Ensures
        ),
        Some("move |ret| *ret >= low")
    );
}

#[test]
fn snippet_fallback_preserves_bool_literals() {
    assert_eq!(
        lower_contract_snippet_body(
            "true",
            TrustContractKind::Requires,
            ContractClauseOrigin::Attribute
        ),
        Some(TrustContractPredicateKind::BoolLiteral { value: true })
    );
    assert_eq!(
        lower_contract_snippet_body(
            "false",
            TrustContractKind::Requires,
            ContractClauseOrigin::Attribute
        ),
        Some(TrustContractPredicateKind::BoolLiteral { value: false })
    );
}

#[test]
fn snippet_fallback_rejects_bare_ensures_result_binding() {
    assert_eq!(
        lower_contract_snippet_body(
            "|ret| ret == ret",
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute
        ),
        None
    );
}

#[test]
fn native_ensures_lowers_bare_result_value() {
    assert_eq!(
        lowered_text(TrustContractKind::Ensures, ContractClauseOrigin::Native, "result == x + 1")
            .as_deref(),
        Some("(result) == ((x) + (1))")
    );
}

#[test]
fn native_function_decreases_preserves_its_arithmetic_measure() {
    with_test_session_globals(|| {
        assert_eq!(
            lower_contract_snippet_body(
                "hi - lo",
                TrustContractKind::Decreases,
                ContractClauseOrigin::Native,
            ),
            Some(TrustContractPredicateKind::Opaque { text: Symbol::intern("hi - lo") })
        );
    });
}

#[test]
fn native_function_decreases_is_early_typed_against_signature_domains() {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    let domains = [
        LoweredVariableDomain { name: "flag".to_string(), domain: Domain::Bool },
        LoweredVariableDomain {
            name: "n".to_string(),
            domain: Domain::MachineInt { width: 32, signed: false },
        },
    ];
    assert_eq!(validate_native_function_decreases_body("n - 1", &domains), Ok("n - 1".to_string()));

    let boolean = validate_native_function_decreases_body("flag", &domains).unwrap_err();
    assert!(boolean.contains("must have sort Int"), "unexpected error: {boolean}");

    let unknown = validate_native_function_decreases_body("ghost + 1", &domains).unwrap_err();
    assert!(unknown.contains("ghost"), "unexpected error: {unknown}");
    assert!(unknown.contains("not in scope"), "unexpected error: {unknown}");

    let malformed = validate_native_function_decreases_body("n +", &domains).unwrap_err();
    assert!(
        malformed.contains("unexpected end") || malformed.contains("Unexpected"),
        "unexpected error: {malformed}"
    );

    let scalar_len = validate_native_function_decreases_body("n.len()", &domains).unwrap_err();
    assert!(scalar_len.contains("requires an Array base"), "unexpected error: {scalar_len}");
}

#[test]
fn native_function_decreases_accepts_exact_aggregate_measures() {
    let sorts = BTreeMap::from([
        (
            "xs".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Int),
            ),
        ),
        (
            "flags".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Bool),
            ),
        ),
    ]);

    assert_eq!(
        validate_native_clause_body("xs.len()", TrustContractKind::Decreases, &sorts),
        Ok("xs.len()".to_string())
    );
    assert_eq!(
        validate_native_clause_body("xs[0]", TrustContractKind::Decreases, &sorts),
        Ok("xs[0]".to_string())
    );
    let boolean_element =
        validate_native_clause_body("flags[0]", TrustContractKind::Decreases, &sorts).unwrap_err();
    assert!(boolean_element.contains("must have sort Int"), "unexpected error: {boolean_element}");
}

#[test]
fn native_function_requires_accepts_exact_aggregate_accessors() {
    let sorts = BTreeMap::from([
        ("n".to_string(), trust_types::Sort::Int),
        (
            "xs".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Int),
            ),
        ),
    ]);

    assert_eq!(
        validate_native_clause_body("xs.len() > 0 && n == n", TrustContractKind::Requires, &sorts,),
        Ok("xs.len() > 0 && n == n".to_string()),
    );
    let scalar = validate_native_clause_body("n.len() > 0", TrustContractKind::Requires, &sorts)
        .unwrap_err();
    assert!(scalar.contains("requires an Array base"), "unexpected error: {scalar}");
}

#[test]
fn native_function_requires_len_mints_typed_query_proposition() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractProposition as Proposition,
        TrustContractPropositionDomain as Domain,
    };

    let sorts = BTreeMap::from([
        ("n".to_string(), trust_types::Sort::Int),
        (
            "xs".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Int),
            ),
        ),
    ]);
    let domains = [
        LoweredVariableDomain {
            name: "_0".to_string(),
            domain: Domain::MachineInt { width: 32, signed: false },
        },
        LoweredVariableDomain { name: "keep".to_string(), domain: Domain::Bool },
        LoweredVariableDomain {
            name: "n".to_string(),
            domain: Domain::PointerSizedInt { width: 64, signed: false },
        },
    ];
    let collection_domains = BTreeMap::from([(
        "xs".to_string(),
        LoweredCollectionDomain {
            element: Domain::MachineInt { width: 8, signed: false },
            fixed_length: None,
        },
    )]);

    with_test_session_globals(|| {
        let predicate = typed_native_function_requires(
            "xs.len() > 0 && n == n",
            &sorts,
            &domains,
            &collection_domains,
            Some(64),
        )
        .expect("the exact native Requires subset must be structurally typed");
        let Predicate::Typed { text, proposition } = predicate else {
            panic!("native Requires must not remain opaque")
        };
        assert_eq!(text.as_str(), "__trust_lowered_compiler_contract__:xs.len() > 0 && n == n",);
        let Proposition::And(terms) = proposition else { panic!("expected canonical conjunction") };
        assert!(terms.iter().any(|term| matches!(
            term,
            Proposition::Gt(lhs, _)
                if matches!(lhs.as_ref(), Proposition::Var { name, domain }
                    if name.as_str() == "xs_len"
                        && *domain
                            == (Domain::PointerSizedInt { width: 64, signed: false }))
        )));

        let mut colliding_domains = domains.to_vec();
        colliding_domains.push(LoweredVariableDomain {
            name: "xs_len".to_string(),
            domain: Domain::PointerSizedInt { width: 64, signed: false },
        });
        assert!(
            typed_native_function_requires(
                "xs.len() > 0",
                &sorts,
                &colliding_domains,
                &collection_domains,
                Some(64),
            )
            .is_none(),
            "a real `xs_len` parameter must not authorize the lowered `xs.len()` leaf",
        );
    });
}

#[test]
fn native_clause_rejects_visible_synthetic_name_aliases_before_lowering() {
    let array = trust_types::Sort::Array(
        Box::new(trust_types::Sort::Int),
        Box::new(trust_types::Sort::Int),
    );
    for reserved in [
        "_2",
        "old_x",
        "xs_len",
        "x_discr",
        "x_value",
        "x_sign",
        "x_value_sign",
        "priv_dropped",
        "s__slice_len",
        "__trust_constparam_0_N",
    ] {
        let sorts = BTreeMap::from([
            ("xs".to_string(), array.clone()),
            (reserved.to_string(), trust_types::Sort::Int),
        ]);
        let error =
            validate_native_clause_body("xs.len() == 0", TrustContractKind::LoopInvariant, &sorts)
                .unwrap_err();
        assert!(error.contains(reserved), "unexpected error for `{reserved}`: {error}");
        assert!(
            error.contains("synthetic contract-variable namespace"),
            "unexpected error for `{reserved}`: {error}"
        );
    }
}

#[test]
fn native_loop_clauses_are_early_typed_in_their_visible_environment() {
    let sorts = BTreeMap::from([
        ("flag".to_string(), trust_types::Sort::Bool),
        ("limit".to_string(), trust_types::Sort::Int),
        ("n".to_string(), trust_types::Sort::Int),
        (
            "state".to_string(),
            trust_types::Sort::Datatype { name: "State".to_string(), constructors: Vec::new() },
        ),
        (
            "xs".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Int),
            ),
        ),
    ]);

    assert_eq!(
        validate_native_clause_body(
            "n <= limit && n <= xs.len()",
            TrustContractKind::LoopInvariant,
            &sorts,
        ),
        Ok("n <= limit && n <= xs.len()".to_string())
    );
    assert_eq!(
        validate_native_clause_body("n", TrustContractKind::Decreases, &sorts),
        Ok("n".to_string())
    );

    let non_boolean =
        validate_native_clause_body("n + 1", TrustContractKind::LoopInvariant, &sorts).unwrap_err();
    assert!(non_boolean.contains("must have sort Bool"), "unexpected error: {non_boolean}");

    let non_integer =
        validate_native_clause_body("flag", TrustContractKind::Decreases, &sorts).unwrap_err();
    assert!(non_integer.contains("must have sort Int"), "unexpected error: {non_integer}");

    let unknown =
        validate_native_clause_body("ghost > 0", TrustContractKind::LoopInvariant, &sorts)
            .unwrap_err();
    assert!(unknown.contains("ghost"), "unexpected error: {unknown}");
    assert!(unknown.contains("not in scope"), "unexpected error: {unknown}");

    let scalar_index =
        validate_native_clause_body("flag[0]", TrustContractKind::LoopInvariant, &sorts)
            .unwrap_err();
    assert!(scalar_index.contains("requires an Array base"), "unexpected error: {scalar_index}");

    let scalar_field =
        validate_native_clause_body("flag.nope == 0", TrustContractKind::LoopInvariant, &sorts)
            .unwrap_err();
    assert!(
        scalar_field.contains("unsupported without exact field layout"),
        "unexpected error: {scalar_field}"
    );

    let unknown_datatype_field =
        validate_native_clause_body("state.nope > 0", TrustContractKind::LoopInvariant, &sorts)
            .unwrap_err();
    assert!(
        unknown_datatype_field.contains("unsupported without exact field layout"),
        "unexpected error: {unknown_datatype_field}"
    );
}

#[test]
fn native_e4_e5_clauses_mint_class_aware_structural_query_carriers() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractProposition as Proposition,
        TrustContractPropositionDomain as Domain,
    };

    let sorts = BTreeMap::from([
        ("limit".to_string(), trust_types::Sort::Int),
        ("n".to_string(), trust_types::Sort::Int),
    ]);
    let domains = [
        LoweredVariableDomain {
            name: "limit".to_string(),
            domain: Domain::MachineInt { width: 32, signed: false },
        },
        LoweredVariableDomain {
            name: "n".to_string(),
            domain: Domain::MachineInt { width: 32, signed: false },
        },
    ];

    with_test_session_globals(|| {
        let invariant = typed_native_clause(
            "n <= limit",
            TrustContractKind::LoopInvariant,
            &sorts,
            &domains,
            Some(64),
        )
        .expect("Boolean E4 clause must be typed");
        assert!(matches!(invariant, Predicate::Typed { proposition: Proposition::Le(_, _), .. }));

        let decreases = typed_native_clause(
            "limit - n",
            TrustContractKind::Decreases,
            &sorts,
            &domains,
            Some(64),
        )
        .expect("numeric E5 clause must be typed");
        assert!(matches!(decreases, Predicate::Typed { proposition: Proposition::Sub(_, _), .. }));

        assert!(
            typed_native_clause(
                "n <= limit",
                TrustContractKind::Decreases,
                &sorts,
                &domains,
                Some(64),
            )
            .is_none(),
            "a Boolean proposition cannot masquerade as an E5 measure",
        );
        assert!(
            typed_native_clause(
                "n",
                TrustContractKind::Decreases,
                &sorts,
                &domains[..1],
                Some(64),
            )
            .is_none(),
            "a numeric carrier needs the exact domain of every free variable",
        );
    });
}

#[test]
fn native_collection_loop_clause_mints_exact_literal_projection_domains() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractProposition as Proposition,
        TrustContractPropositionDomain as Domain,
    };

    let source_sorts = BTreeMap::from([
        ("_n".to_string(), trust_types::Sort::Int),
        ("first".to_string(), trust_types::Sort::Int),
        (
            "xs".to_string(),
            trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(trust_types::Sort::Int),
            ),
        ),
    ]);
    let visible_domains = [
        LoweredVariableDomain {
            name: "_n".to_string(),
            domain: Domain::PointerSizedInt { width: 64, signed: false },
        },
        LoweredVariableDomain {
            name: "first".to_string(),
            domain: Domain::MachineInt { width: 32, signed: false },
        },
    ];
    let collection_domains = BTreeMap::from([(
        "xs".to_string(),
        LoweredCollectionDomain {
            element: Domain::MachineInt { width: 32, signed: false },
            fixed_length: Some(4),
        },
    )]);

    with_test_session_globals(|| {
        let predicate = typed_native_clause_with_collection_domains(
            "_n == xs.len() && first == xs[0]",
            TrustContractKind::LoopInvariant,
            &source_sorts,
            &visible_domains,
            &collection_domains,
            Some(64),
        )
        .expect("a canonical literal collection read must retain its exact element domain");
        let Predicate::Typed { proposition: Proposition::And(terms), .. } = predicate else {
            panic!("the collection invariant must cross as one structural conjunction")
        };
        let mut variables = BTreeMap::new();
        fn collect(proposition: &Proposition, variables: &mut BTreeMap<String, Domain>) {
            match proposition {
                Proposition::Var { name, domain } => {
                    variables.insert(name.to_string(), *domain);
                }
                Proposition::Not(inner) | Proposition::Neg(inner) => collect(inner, variables),
                Proposition::And(terms) | Proposition::Or(terms) => {
                    for term in terms {
                        collect(term, variables);
                    }
                }
                Proposition::Implies(lhs, rhs)
                | Proposition::Eq(lhs, rhs)
                | Proposition::Lt(lhs, rhs)
                | Proposition::Le(lhs, rhs)
                | Proposition::Gt(lhs, rhs)
                | Proposition::Ge(lhs, rhs)
                | Proposition::Add(lhs, rhs)
                | Proposition::Sub(lhs, rhs)
                | Proposition::Mul(lhs, rhs)
                | Proposition::Div(lhs, rhs)
                | Proposition::Rem(lhs, rhs) => {
                    collect(lhs, variables);
                    collect(rhs, variables);
                }
                Proposition::Bool(_) | Proposition::Int(_) | Proposition::UInt(_) => {}
            }
        }
        for term in &terms {
            collect(term, &mut variables);
        }
        assert_eq!(
            variables,
            BTreeMap::from([
                ("_n".to_string(), Domain::PointerSizedInt { width: 64, signed: false }),
                ("first".to_string(), Domain::MachineInt { width: 32, signed: false }),
                ("xs[0]".to_string(), Domain::MachineInt { width: 32, signed: false }),
                ("xs_len".to_string(), Domain::PointerSizedInt { width: 64, signed: false }),
            ])
        );

        assert!(
            typed_native_clause_with_collection_domains(
                "_n == xs.len() && first == xs[0]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &BTreeMap::new(),
                Some(64),
            )
            .is_none(),
            "a logical Array sort without its exact element domain is not authority",
        );
        assert!(
            typed_native_clause_with_collection_domains(
                "first == xs[00]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &collection_domains,
                Some(64),
            )
            .is_none(),
            "alternate literal spellings must not alias the canonical projected leaf",
        );
        assert!(
            typed_native_clause_with_collection_domains(
                "first == xs[(0)]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &collection_domains,
                Some(64),
            )
            .is_none(),
            "literal-index parentheses must not alias the canonical projected leaf",
        );
        assert!(
            typed_native_clause_with_collection_domains(
                "first == xs[3]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &collection_domains,
                Some(64),
            )
            .is_some(),
            "the last fixed-array element must retain structural authority",
        );
        assert!(
            typed_native_clause_with_collection_domains(
                "first == xs[4]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &collection_domains,
                Some(64),
            )
            .is_none(),
            "an index at the fixed-array length must not mint a projected identity",
        );
        assert!(
            typed_native_clause_with_collection_domains(
                "_n == xs.len()",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &BTreeMap::new(),
                Some(64),
            )
            .is_none(),
            "an Array source sort alone must not authorize a shadowable length leaf",
        );
        let wrong_domain = BTreeMap::from([(
            "xs".to_string(),
            LoweredCollectionDomain { element: Domain::Bool, fixed_length: Some(4) },
        )]);
        assert!(
            typed_native_clause_with_collection_domains(
                "first == xs[0]",
                TrustContractKind::LoopInvariant,
                &source_sorts,
                &visible_domains,
                &wrong_domain,
                Some(64),
            )
            .is_none(),
            "an element domain inconsistent with the source Array sort must fail closed",
        );
    });
}

#[test]
fn attribute_ensures_never_acquires_native_bare_result_semantics() {
    assert_eq!(
        lower_contract_snippet_body(
            "result == x + 1",
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute
        ),
        None
    );
}

#[test]
fn native_verifier_vocabulary_lowers_to_downstream_supported_syntax() {
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Native,
            "x == x ==> result == x"
        )
        .as_deref(),
        Some("((x) == (x)) => ((result) == (x))")
    );
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Native,
            "forall i j: usize, i < j ==> result >= x"
        )
        .as_deref(),
        Some("forall i j: usize, ((i) < (j)) => ((result) >= (x))")
    );
    assert_eq!(
        lowered_text(
            TrustContractKind::Requires,
            ContractClauseOrigin::Native,
            "exists i: u8, i == x"
        )
        .as_deref(),
        Some("exists i: u8, (i) == (x)")
    );
}

#[test]
fn primed_identifiers_fail_closed_until_post_state_places_are_bound() {
    for kind in [
        TrustContractKind::Requires,
        TrustContractKind::Ensures,
        TrustContractKind::Invariant,
        TrustContractKind::LoopInvariant,
        TrustContractKind::Decreases,
        TrustContractKind::Assumes,
        TrustContractKind::Asserts,
        TrustContractKind::Refinement,
        TrustContractKind::Temporal,
    ] {
        assert_eq!(
            lower_contract_snippet_body(
                "balance' == balance - amount",
                kind,
                ContractClauseOrigin::Native
            ),
            None,
            "a free post-state name must not be accepted for {kind:?}"
        );
    }
    assert_eq!(primed_identifier_in_contract_snippet("x'' == x"), Some("x''"));
    assert_eq!(primed_identifier_in_contract_snippet("x == y"), None);
}

#[test]
fn attribute_compatibility_vocabulary_does_not_leak_into_native_grammar() {
    assert_eq!(
        lowered_text(
            TrustContractKind::Ensures,
            ContractClauseOrigin::Attribute,
            "|ret| forall(i, 0..n, i < n => *ret >= old(x))"
        )
        .as_deref(),
        Some("forall(i, 0..n, ((i) < (n)) => ((result) >= (old(x))))")
    );
}

#[test]
fn malformed_native_verifier_vocabulary_fails_closed() {
    for malformed in [
        "old(x) == x",
        "forall(i, 0, i == i)",
        "exists(i, 0..n, i == i",
        "forall i, i == i",
        "forall result: usize, result == result",
        "exists i: usize, i == i ==> result == result",
        "x ==> ==> result == x",
    ] {
        assert_eq!(
            lower_contract_snippet_body(
                malformed,
                TrustContractKind::Ensures,
                ContractClauseOrigin::Native
            ),
            None,
            "malformed predicate must be unsupported: {malformed}"
        );
    }
}
