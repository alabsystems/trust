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
        match lower_contract_snippet_body_with_domains(
            body,
            kind,
            origin,
            ClauseCitation::Absent,
            domains,
            &ProjectionEnvironment::default(),
            &mut None,
            &mut None,
        )? {
            TrustContractPredicateKind::Typed { text, .. }
            | TrustContractPredicateKind::Opaque { text } => {
                Some(text.as_str().strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX)?.to_string())
            }
            _ => None,
        }
    })
}

/// Build the projection environment a `&mut self` receiver of
/// `struct Grid { storage: Storage }` / `struct Storage { detached: bool, n: u64 }`
/// produces, plus a by-reference `s: &S` with one `u64` field, plus a scalar
/// `x: &mut u64`. The `&mut` heads carry their D2 primed spellings (`LeafEpoch`).
fn projection_fixture() -> ProjectionEnvironment {
    let mut canonical_text = FxHashMap::default();
    let mut epochs = FxHashMap::default();
    for (authored, canonical, epoch) in [
        ("self.storage.detached", "(*self).0.0", LeafEpoch::MutPointeeUnprimed),
        ("self.storage.n", "(*self).0.1", LeafEpoch::MutPointeeUnprimed),
        ("self'.storage.detached", "(*self).0.0", LeafEpoch::Primed),
        ("self'.storage.n", "(*self).0.1", LeafEpoch::Primed),
        ("x'", "(*x)", LeafEpoch::Primed),
        ("s.n", "s.0", LeafEpoch::Plain),
    ] {
        canonical_text.insert(authored.to_string(), canonical.to_string());
        epochs.insert(authored.to_string(), epoch);
    }
    let mut mut_params = FxHashSet::default();
    mut_params.insert("self".to_string());
    mut_params.insert("x".to_string());
    ProjectionEnvironment { canonical_text, epochs, mut_params }
}

fn projected_text(kind: TrustContractKind, body: &str) -> Option<String> {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    let domains = [
        LoweredVariableDomain { name: "_0".to_string(), domain: Domain::Bool },
        LoweredVariableDomain { name: "s.0".to_string(), domain: Domain::Bool },
        LoweredVariableDomain { name: "self*.0.0".to_string(), domain: Domain::Bool },
        LoweredVariableDomain {
            name: "self*.0.1".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
        LoweredVariableDomain {
            name: "x*".to_string(),
            domain: Domain::MachineInt { width: 64, signed: false },
        },
    ];
    with_test_session_globals(|| {
        match lower_contract_snippet_body_with_domains(
            body,
            kind,
            ContractClauseOrigin::Native,
            ClauseCitation::Absent,
            &domains,
            &projection_fixture(),
            &mut None,
            &mut None,
        )? {
            TrustContractPredicateKind::Typed { text, .. }
            | TrustContractPredicateKind::Opaque { text } => {
                Some(text.as_str().strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX)?.to_string())
            }
            _ => None,
        }
    })
}

/// A projected field clause must emit the POSITIONAL, prefix-deref spelling
/// whose `spec_parse` var name is byte-identical to the name
/// `trust_vcgen::place_to_var_name` mints for the same MIR place — `(*self).0.0`
/// parses to `self*.0.0`, which is what `(*_1).0.0` renders. Emitting the
/// authored `self.storage.detached` instead would leave a FREE variable that no
/// body fact can ever bind.
#[test]
fn native_field_projection_lowers_to_the_canonical_place_spelling() {
    assert_eq!(
        projected_text(TrustContractKind::Ensures, "!self.storage.detached").as_deref(),
        Some("!((*self).0.0)")
    );
    assert_eq!(
        projected_text(TrustContractKind::Ensures, "self.storage.n == 0").as_deref(),
        Some("((*self).0.1) == (0)")
    );
    assert_eq!(
        projected_text(TrustContractKind::Ensures, "result == s.n").as_deref(),
        Some("(result) == (s.0)")
    );
}

/// D2 primes (M0(b1), 2026-09-30). A prime on a `&mut` parameter's pointee names its
/// FINAL value, and resolves to the canonical place today's native lane reads at exit,
/// in a native uncited `ensures` only. See `LeafEpoch`.
#[test]
fn d2_primes_bind_a_mut_pointee_final_value_in_a_native_ensures_only() {
    use TrustContractKind::{Ensures, Requires};
    assert_eq!(
        projected_text(Ensures, "!self'.storage.detached").as_deref(),
        Some("!((*self).0.0)")
    );
    assert_eq!(
        projected_text(Ensures, "self'.storage.n == 0").as_deref(),
        Some("((*self).0.1) == (0)")
    );
    assert_eq!(projected_text(Ensures, "x' == 1").as_deref(), Some("((*x)) == (1)"));
    // A precondition is a one-state predicate: no post-state exists to name.
    assert_eq!(projected_text(Requires, "!self'.storage.detached"), None);
    // MIXED EPOCHS. The unprimed spelling of a `&mut` pointee still reads the EXIT
    // value, so each of these would compare exit with exit: `x' == *x + 1` over
    // `*x += 1` would lower to `x* == x* + 1`.
    assert_eq!(projected_text(Ensures, "self'.storage.n == self.storage.n"), None);
    assert_eq!(projected_text(Ensures, "x' == *x + 1"), None);
    // Not D2 spellings: a deref of a primed name, a prime on a shared or by-value
    // head, a double prime.
    assert_eq!(projected_text(Ensures, "*x' == 1"), None);
    assert_eq!(projected_text(Ensures, "s'.n == 0"), None);
    assert_eq!(projected_text(Ensures, "x'' == 1"), None);
}

/// §13.1 of `docs/STRICT_VERIFICATION_FRAGMENT.md`: every one of these spellings
/// used to make the WHOLE clause unparseable, silently, while the identical
/// constant in the function body was fine. They are the same integer written
/// four ways, and all four must now lower to the same canonical bare-decimal
/// text — which is what the downstream formula parser reads.
#[test]
fn every_rust_integer_literal_spelling_lowers_to_the_same_bare_decimal() {
    let lowered =
        |body: &str| lowered_text(TrustContractKind::Ensures, ContractClauseOrigin::Native, body);
    let bare = lowered("result <= 999999999");
    assert_eq!(bare.as_deref(), Some("(result) <= (999999999)"));
    for spelling in ["999_999_999", "0x3B9AC9FF", "999999999u32", "999_999_999usize"] {
        assert_eq!(
            lowered(&format!("result <= {spelling}")),
            bare,
            "`{spelling}` must lower exactly as the bare decimal does"
        );
    }
    // Not about magnitude: a separator in a two-digit literal was equally fatal.
    assert_eq!(
        lowered("result <= 1_0").as_deref(),
        Some("(result) <= (10)"),
        "a separator in a two-digit literal"
    );
    assert_eq!(lowered("result <= 0b111").as_deref(), Some("(result) <= (7)"));
    assert_eq!(lowered("result <= 0o17").as_deref(), Some("(result) <= (15)"));
    // The respelling is not specific to `ensures`: the same tokenizer serves
    // every clause kind that reaches the snippet lane.
    assert_eq!(
        lowered_text(TrustContractKind::Requires, ContractClauseOrigin::Native, "x <= 1_000")
            .as_deref(),
        Some("(x) <= (1000)")
    );
}

/// A widened literal grammar must not widen what is ACCEPTED as true. Each of
/// these is a spelling Rust's own lexer tolerates in some context but which
/// denotes no readable bound here, and each must keep failing closed — most of
/// all `300u8`, which would otherwise become the bound `result <= 300` that
/// every `u8` satisfies.
#[test]
fn a_literal_that_cannot_be_read_still_fails_the_whole_clause() {
    for body in [
        "result <= 300u8",
        "result <= 129i8",
        "result <= 123abc",
        "result <= 0x",
        "result <= 0b2",
        "result <= 0X1",
        // Above the `i128` the formula language carries an integer literal in.
        "result <= 999999999999999999999999999999999999999999",
        // No floating-point literal exists on this lane in either direction.
        "result <= 1.5",
    ] {
        assert_eq!(
            lowered_text(TrustContractKind::Ensures, ContractClauseOrigin::Native, body),
            None,
            "`{body}` must fail closed"
        );
    }
}

/// A tuple-field index is the canonical bare-decimal spelling and nothing else.
/// Respelling one would mint a place name `spec_parse` and
/// `trust_vcgen::place_to_var_name` do not agree on, and the clause would die
/// at a boundary that could no longer say why.
#[test]
fn a_projection_index_is_not_respelled() {
    assert_eq!(
        projected_text(TrustContractKind::Ensures, "result == s.n").as_deref(),
        Some("(result) == (s.0)")
    );
    for body in ["result == s.0_0", "result == s.0x0", "result == s.0usize"] {
        assert_eq!(projected_text(TrustContractKind::Ensures, body), None, "`{body}`");
    }
}

/// Every shape without a sound positional name must keep failing closed. A
/// false PROVE is catastrophic; an honest refusal is merely annoying.
#[test]
fn native_field_projection_fails_closed_on_unresolvable_chains() {
    for body in [
        // Not a field of the receiver's type.
        "!self.storage.missing",
        "!self.missing",
        // Not a parameter at all.
        "!other.storage.detached",
        // Deeper than the enumerated layout.
        "self.storage.detached.deeper == 0",
        // A method call is not a place.
        "s.n() == 0",
        // The result binding has no projected signature entry.
        "result.0 == 0",
        // The CANONICAL spelling is not author-reachable: only a chain that
        // resolves through the environment may mint a name.
        "!(*self).0.0",
        // A named-field struct has no positional source spelling.
        "self.0.0 == 0",
    ] {
        assert_eq!(projected_text(TrustContractKind::Ensures, body), None, "must reject `{body}`");
    }
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
                ClauseCitation::Absent,
                &domains,
                &ProjectionEnvironment::default(),
                &mut None,
                &mut None,
            ),
            None,
        );
        assert!(
            lower_contract_snippet_body_with_domains(
                "result == x",
                TrustContractKind::Ensures,
                ContractClauseOrigin::Native,
                ClauseCitation::Absent,
                &domains,
                &ProjectionEnvironment::default(),
                &mut None,
                &mut None,
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
            "xs__len > 0".to_string(),
            &[LoweredVariableDomain {
                name: "xs__len".to_string(),
                domain: Domain::PointerSizedInt { width: 64, signed: false },
            }],
        );
        assert!(
            exact_predicate_source_bindings(&synthesized, &[]).is_empty(),
            "a synthesized projection leaf must not acquire whole-local authority",
        );

        let collection = TrustContractPredicateKind::Typed {
            text: Symbol::intern("xs.len() > xs[0]"),
            proposition: TrustContractProposition::Gt(
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("xs__len"),
                    domain: Domain::PointerSizedInt { width: 64, signed: false },
                }),
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("xs[0]"),
                    domain: Domain::MachineInt { width: 32, signed: false },
                }),
            ),
        };
        let collection_bindings = exact_predicate_source_place_bindings(
            &collection,
            &[LoweredSourceBinding { name: "xs".to_string(), hir_local_id: 19 }],
        )
        .expect("both synthetic leaves have the same exact collection root");
        assert_eq!(
            collection_bindings
                .iter()
                .map(|binding| (binding.name.as_str(), binding.hir_local_id))
                .collect::<Vec<_>>(),
            vec![("xs", 19)],
        );
        assert!(
            exact_predicate_source_place_bindings(&collection, &[]).is_none(),
            "one missing root must reject the complete provenance map",
        );

        assert_eq!(
            exact_predicate_source_place_bindings(
                &TrustContractPredicateKind::BoolLiteral { value: true },
                &[],
            ),
            Some(Vec::new()),
            "a literal proposition has a complete empty source-root map",
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
fn structural_query_refuses_cross_domain_numeric_operations() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractPropositionDomain as Domain,
    };

    let domains = [
        LoweredVariableDomain {
            name: "u8v".to_string(),
            domain: Domain::MachineInt { width: 8, signed: false },
        },
        LoweredVariableDomain {
            name: "u16v".to_string(),
            domain: Domain::MachineInt { width: 16, signed: false },
        },
        LoweredVariableDomain {
            name: "i8v".to_string(),
            domain: Domain::MachineInt { width: 8, signed: true },
        },
        LoweredVariableDomain { name: "flag".to_string(), domain: Domain::Bool },
    ];

    with_test_session_globals(|| {
        for text in ["u8v == u16v", "u8v < i8v", "u16v + u8v == u16v", "flag == u8v"] {
            assert!(
                matches!(
                    lowered_contract_text_with_domains(text.to_string(), &domains),
                    Predicate::Opaque { .. }
                ),
                "mixed exact domains must fail closed: `{text}`",
            );
        }

        for text in ["u8v == 1", "u16v + 1 == u16v", "flag == true"] {
            assert!(
                matches!(
                    lowered_contract_text_with_domains(text.to_string(), &domains),
                    Predicate::Typed { .. }
                ),
                "a literal may inherit the one authenticated adjacent domain: `{text}`",
            );
        }
    });
}

#[test]
fn helper_scanner_preserves_unicode_strings_comments_and_refused_calls() {
    let source = concat!(
        "π + δhelper(x) + \"helper(a, b))\" + r#\"helper(c)\"# + ",
        " /* helper(d, e) */ helper( x ) + unknown(helper(y)) // helper(z)\n",
    );
    let mut calls = Vec::new();
    let rewritten = rewrite_contract_helper_calls(source, 0, &mut |name, actuals, _| {
        calls.push((name.to_string(), actuals.to_vec()));
        (name == "helper").then(|| format!("<{}>", actuals.join(",")))
    });

    assert_eq!(
        rewritten,
        concat!(
            "π + δhelper(x) + \"helper(a, b))\" + r#\"helper(c)\"# + ",
            " /* helper(d, e) */ <x> + unknown(helper(y)) // helper(z)\n",
        ),
    );
    assert!(calls.contains(&("helper".to_string(), vec!["x".to_string()])));
    assert!(calls.contains(&("unknown".to_string(), vec!["<y>".to_string()])));
    assert!(
        calls.iter().all(|(name, actuals)|
            !matches!((name.as_str(), actuals.as_slice()), ("helper", [value]) if matches!(value.as_str(), "a" | "c" | "d" | "z"))),
        "helper-looking text inside protected tokens must never reach semantic resolution",
    );
}

#[test]
fn helper_argument_scanner_ignores_nested_delimiters_inside_tokens() {
    assert_eq!(
        split_top_level_commas("x, \"a,b)\", r#\"c,d)\"#, /* , ) */ nested(y, z)").unwrap(),
        ["x", " \"a,b)\"", " r#\"c,d)\"#", " /* , ) */ nested(y, z)"],
    );
    let wrapped = "outer(\"λ)\", r#\")\"#, /* ) */ inner(x)) tail";
    assert_eq!(matching_close_paren(wrapped, 5), wrapped.rfind(')'));
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

/// NEGATIVE. `requires` is the only clause whose predicate is ASSUMED, so the
/// return-place vocabulary must never reach it.
///
/// Measured on the promoted toolchain trust-e26541e3 before this refusal
/// existed: `#[trust::requires(result == 0)]` lowered to `Eq(_0, 0)` and
/// emitted a real `assumption:requires` row. What kept it from becoming a
/// definition-entry assumption over the return place was the later
/// `contract_assumption_gate` (crates/trust-mir-extract), which warns
/// "predicate references `_0`, which is not a parameter" and skips it. That
/// gate stays as defence in depth; this refusal is the FIRST boundary, the one
/// that sees the text, and it matches the native lane, which refuses the same
/// spelling outright with "`result` is only allowed in an ensures clause"
/// (tests/ui/trust/typed_citation_result_scope.rs).
#[test]
fn attribute_requires_refuses_the_return_place_vocabulary() {
    for body in ["result == 0", "result == x", "_0 == 0", "x > 0 && result < x"] {
        assert_eq!(
            lowered_text(TrustContractKind::Requires, ContractClauseOrigin::Attribute, body),
            None,
            "`requires {body}` must not lower the return place into an entry assumption"
        );
    }
    // The refusal is scoped to the return-place vocabulary: ordinary
    // preconditions over parameters keep lowering.
    assert_eq!(
        lowered_text(TrustContractKind::Requires, ContractClauseOrigin::Attribute, "x > 0")
            .as_deref(),
        Some("(x) > (0)")
    );
    // The rule keys on the absence of a RESULT BINDING, not on the origin or
    // the clause keyword, so every other bindingless kind that reaches this
    // parser is covered too. A native `requires` is separately caught by
    // `lower_native_clause`'s hard error before it ever gets here.
    for kind in [
        TrustContractKind::Requires,
        TrustContractKind::Invariant,
        TrustContractKind::Assumes,
        TrustContractKind::Asserts,
    ] {
        for origin in [ContractClauseOrigin::Attribute, ContractClauseOrigin::Native] {
            assert_eq!(
                lowered_text(kind, origin, "result == x"),
                None,
                "`result` must not denote the return place in {kind:?} ({origin:?})"
            );
        }
    }
    // An `ensures` still binds it, which is the whole point. (The native lane
    // is the one `lowered_text` gives signature domains; an attribute bare-
    // `result` ensures is source-typed against real domains and is pinned by
    // its own tests.)
    assert_eq!(
        lowered_text(TrustContractKind::Ensures, ContractClauseOrigin::Native, "result == x")
            .as_deref(),
        Some("(result) == (x)")
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
                    if name.as_str() == "xs__len"
                        && *domain
                            == (Domain::PointerSizedInt { width: 64, signed: false }))
        )));

        // A real parameter named `xs_len` coexists with the minted `xs__len`
        // projection leaf: the two spellings are distinct by construction, so
        // the clause stays typed and each leaf keeps its own identity.
        let mut coexisting_sorts = sorts.clone();
        coexisting_sorts.insert("xs_len".to_string(), trust_types::Sort::Int);
        let mut coexisting_domains = domains.to_vec();
        coexisting_domains.push(LoweredVariableDomain {
            name: "xs_len".to_string(),
            domain: Domain::PointerSizedInt { width: 64, signed: false },
        });
        let coexisting = typed_native_function_requires(
            "xs.len() > 0 && xs_len > 0",
            &coexisting_sorts,
            &coexisting_domains,
            &collection_domains,
            Some(64),
        )
        .expect("a parameter named `xs_len` must not block the `xs.len()` projection");
        let Predicate::Typed { proposition, .. } = coexisting else {
            panic!("the coexisting clause must stay structurally typed")
        };
        let mut leaf_names = std::collections::BTreeSet::new();
        fn collect_leaves(
            proposition: &rustc_middle::mir::trust_contract::TrustContractProposition,
            names: &mut std::collections::BTreeSet<String>,
        ) {
            use rustc_middle::mir::trust_contract::TrustContractProposition as P;
            match proposition {
                P::Var { name, .. } => {
                    names.insert(name.as_str().to_string());
                }
                P::Float { .. } => {}
                P::Not(inner) | P::Neg(inner) => collect_leaves(inner, names),
                P::And(terms) | P::Or(terms) => {
                    terms.iter().for_each(|term| collect_leaves(term, names));
                }
                P::Implies(lhs, rhs)
                | P::Eq(lhs, rhs)
                | P::Lt(lhs, rhs)
                | P::Le(lhs, rhs)
                | P::Gt(lhs, rhs)
                | P::Ge(lhs, rhs)
                | P::Add(lhs, rhs)
                | P::Sub(lhs, rhs)
                | P::Mul(lhs, rhs)
                | P::Div(lhs, rhs)
                | P::Rem(lhs, rhs) => {
                    collect_leaves(lhs, names);
                    collect_leaves(rhs, names);
                }
                P::Bool(_) | P::Int(_) | P::UInt(_) => {}
            }
        }
        collect_leaves(&proposition, &mut leaf_names);
        assert!(leaf_names.contains("xs__len"), "missing projection leaf: {leaf_names:?}");
        assert!(leaf_names.contains("xs_len"), "missing parameter leaf: {leaf_names:?}");
    });
}

#[test]
fn native_clause_rejects_visible_synthetic_name_aliases_before_lowering() {
    let array = trust_types::Sort::Array(
        Box::new(trust_types::Sort::Int),
        Box::new(trust_types::Sort::Int),
    );
    for reserved in ["_2", "old_x", "priv_dropped", "s__slice_len", "__trust_constparam_0_N"] {
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
    // Projection-suffixed spellings are ordinary bindings now that minted
    // leaves live in the `__` family: a visible `xs_len` (or chained
    // `x_value_sign`) must not block a clause that also projects `xs.len()`.
    for ordinary in ["xs_len", "max_len", "x_discr", "x_value", "x_sign", "x_value_sign"] {
        let sorts = BTreeMap::from([
            ("xs".to_string(), array.clone()),
            (ordinary.to_string(), trust_types::Sort::Int),
        ]);
        assert_eq!(
            validate_native_clause_body("xs.len() == 0", TrustContractKind::LoopInvariant, &sorts),
            Ok("xs.len() == 0".to_string()),
            "visible `{ordinary}` must be admitted",
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
                Proposition::Float { .. } => {}
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
                ("xs__len".to_string(), Domain::PointerSizedInt { width: 64, signed: false }),
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

/// An UNCITED attribute `ensures` written in the `result` spelling is the SAME
/// clause as the native `ensures result == ...`, and must lower to the same
/// formula.
///
/// It did not. `ensures_closure_snippet_body` accepted only the migration
/// closure spelling and its `?` propagated straight into `Unsupported`, so
/// `#[trust::ensures(result == x + 1)]` left a pair of fail-closed sentinel
/// obligations that a non-strict policy downgrades to warnings — while the
/// byte-identical `ensures result == x + 1` in signature position lowered into a
/// real Postcondition VC and was proved or REFUTED. Measured on
/// `veripb-core-proved`: an uncited attribute `result >= x` over
/// `x.wrapping_sub(1)` reported `0 proved, 0 failed, 2 unknown` and the build
/// stayed green.
///
/// The equality is asserted against the native lowering of the same text rather
/// than a literal, so the two spellings cannot drift apart silently.
#[test]
fn uncited_attribute_ensures_lowers_exactly_as_the_native_result_spelling() {
    use rustc_middle::mir::trust_contract::TrustContractPropositionDomain as Domain;

    // The signature environment of `fn f(x: u64) -> u64`; `_0` is the return
    // place that `result` denotes.
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
    let lower = |origin, citation, body: &str| {
        with_test_session_globals(|| {
            lower_contract_snippet_body_with_domains(
                body,
                TrustContractKind::Ensures,
                origin,
                citation,
                &domains,
                &ProjectionEnvironment::default(),
                &mut None,
                &mut None,
            )
        })
    };

    let native = lower(ContractClauseOrigin::Native, ClauseCitation::Absent, "result == x + 1");
    assert!(native.is_some(), "the native `result` spelling must lower");
    assert_eq!(
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Absent, "result == x + 1"),
        native,
        "the attribute and native spellings of one clause must be one predicate"
    );

    // A CITED clause keeps the established treatment: the citation lane owns it
    // end to end and mints its own obligation inventory, so the snippet lane
    // must not add rows underneath it.
    assert_eq!(
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Present, "result == x + 1"),
        None
    );

    // Still fail-closed on a name the signature environment cannot ground: the
    // new path runs the SAME source-typing gate native clauses must pass, which
    // is what keeps an island-definition call (`eqOkW(machine, truth)`) out of
    // this lane and with the uncited island-defeq lane that owns it.
    assert_eq!(
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Absent, "result == ghost"),
        None
    );

    // The migration closure spelling is untouched, in both directions.
    assert_eq!(
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Absent, "|ret| *ret >= 0"),
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Present, "|ret| *ret >= 0"),
    );
    assert!(
        lower(ContractClauseOrigin::Attribute, ClauseCitation::Absent, "|ret| ret == ret")
            .is_none(),
        "a bare closure binding still denotes no value"
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

/// Trust (CITE-PRIME-NONASCII-1, 2026-10-05): the prime scanner lexes whole
/// identifiers with rustc's predicates. The ASCII byte scanner returned `a'`
/// for `éa'` and nothing at all for `δ'`.
#[test]
fn primed_identifier_scan_reads_whole_non_ascii_identifiers() {
    assert_eq!(primed_identifier_in_contract_snippet("éa' >= éa"), Some("éa'"));
    assert_eq!(primed_identifier_in_contract_snippet("δx' >= δx"), Some("δx'"));
    assert_eq!(primed_identifier_in_contract_snippet("δ' >= δ"), Some("δ'"));
    assert_eq!(primed_identifier_in_contract_snippet("e\u{301}a' == 0"), Some("e\u{301}a'"));
    // Unchanged ASCII behaviour.
    assert_eq!(primed_identifier_in_contract_snippet("result >= x'"), Some("x'"));
    assert_eq!(primed_identifier_in_contract_snippet("_x1' == 0"), Some("_x1'"));
    assert_eq!(primed_identifier_in_contract_snippet("1 + x == y"), None);
    assert_eq!(primed_identifier_in_contract_snippet("éa >= δx"), None);
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

/// The two halves of the citation lexer partition a snippet's identifiers:
/// `called_identifiers` keeps the `ident(` shapes (whitespace-tolerant), and
/// `bare_identifiers` keeps the rest — including e6 probe f04's zero-arity
/// citation spelling, which the uncited defeq lane used to be blind to
/// (measured TRUST_E9_DEBUG NO-ISLAND-CALL).
#[test]
fn citation_lexer_partitions_called_and_bare_identifiers() {
    // f04's clause: no argument list anywhere.
    assert_eq!(called_identifiers("result == forty_two_isl"), Vec::<String>::new());
    assert_eq!(bare_identifiers("result == forty_two_isl"), vec!["result", "forty_two_isl"]);

    // f06's clause: the callee is called, the argument is a literal.
    assert_eq!(called_identifiers("result == c42(0)"), vec!["c42"]);
    assert_eq!(bare_identifiers("result == c42(0)"), vec!["result"]);

    // An identifier inside an argument list is bare, not called.
    assert_eq!(called_identifiers("result == min2(a, b)"), vec!["min2"]);
    assert_eq!(bare_identifiers("result == min2(a, b)"), vec!["result", "a", "b"]);

    // Whitespace before `(` still reads as a call — for BOTH halves.
    assert_eq!(called_identifiers("f (x)"), vec!["f"]);
    assert_eq!(bare_identifiers("f (x)"), vec!["x"]);
}

/// D3 (cast half). The cast admission rule is a SOUNDNESS boundary, so it is
/// pinned value-by-value rather than by example.
///
/// The contract formula is over MATHEMATICAL integers — every integer
/// proposition domain maps to `Sort::Int` in
/// `CompilerContractValueDomain::logical_sort`, so `+`/`*` never wrap at a
/// machine width. Under that semantics `x as T` denotes the same value as `x`
/// EXACTLY when `range(src)` is a subset of `range(dst)`, and the identity
/// lowering is then exact. Every other integer cast truncates or reinterprets,
/// and lowering it as identity would be a false proof.
#[test]
fn value_preserving_int_cast_admits_exactly_the_widenings() {
    let u = |bits| (bits, false);
    let i = |bits| (bits, true);

    // Same signedness, widening or equal -> value-preserving.
    for (src, dst) in [(8, 16), (8, 64), (32, 64), (32, 128), (64, 64), (8, 8)] {
        assert!(
            value_preserving_int_cast_widths(u(src), u(dst)),
            "u{src} as u{dst} is a widening and must be admitted"
        );
        assert!(
            value_preserving_int_cast_widths(i(src), i(dst)),
            "i{src} as i{dst} is a widening and must be admitted"
        );
    }

    // Same signedness, NARROWING -> truncates -> refused.
    for (src, dst) in [(64, 32), (32, 8), (16, 8), (128, 64)] {
        assert!(
            !value_preserving_int_cast_widths(u(src), u(dst)),
            "u{src} as u{dst} TRUNCATES and must be refused"
        );
        assert!(
            !value_preserving_int_cast_widths(i(src), i(dst)),
            "i{src} as i{dst} TRUNCATES and must be refused"
        );
    }

    // Unsigned -> signed needs a STRICTLY wider target.
    assert!(
        value_preserving_int_cast_widths(u(8), i(16)),
        "u8 as i16 keeps every value (0..=255 fits -32768..=32767)"
    );
    assert!(
        !value_preserving_int_cast_widths(u(8), i(8)),
        "u8 as i8 must be refused: 255 becomes -1"
    );
    assert!(
        !value_preserving_int_cast_widths(u(64), i(64)),
        "u64 as i64 must be refused: u64::MAX becomes -1"
    );

    // Signed -> unsigned is NEVER value-preserving: negatives wrap.
    for (src, dst) in [(8, 8), (8, 64), (32, 64), (32, 128)] {
        assert!(
            !value_preserving_int_cast_widths(i(src), u(dst)),
            "i{src} as u{dst} must be refused: a negative operand wraps"
        );
    }
}

/// D3 (cast half), pointer-sized lane. `usize`/`isize` used to be refused
/// WHOLESALE, which is why the real guard `idx <= u32::MAX as usize` could not
/// be written. They now arrive already resolved to the compilation's exact
/// target pointer width, so they are decided by the same subset test as any
/// other pair — and the answer is genuinely target-dependent, which is the
/// point: the same clause is admitted on a 64-bit target and refused on a
/// 16-bit one, rather than one answer being baked in.
#[test]
fn pointer_sized_casts_are_decided_at_the_target_width() {
    let u = |bits| (bits, false);
    let i = |bits| (bits, true);

    // 64-bit target: usize is (64, false).
    assert!(
        value_preserving_int_cast_widths(u(32), u(64)),
        "on a 64-bit target `u32 as usize` is a widening -> admitted"
    );
    assert!(
        value_preserving_int_cast_widths(u(64), u(64)),
        "on a 64-bit target `usize as u64` is the identity -> admitted"
    );
    assert!(
        !value_preserving_int_cast_widths(u(64), u(32)),
        "on a 64-bit target `usize as u32` TRUNCATES -> refused"
    );
    assert!(
        !value_preserving_int_cast_widths(i(64), u(64)),
        "on a 64-bit target `isize as usize` drops negatives -> refused"
    );

    // 16-bit target: usize is (16, false). The SAME source clause flips.
    assert!(
        !value_preserving_int_cast_widths(u(32), u(16)),
        "on a 16-bit target `u32 as usize` TRUNCATES -> must be refused there"
    );
}

// Trust (SPEC-FLOAT-EQ-STRUCTURAL-1): the parser spells `x == 1.0` as IEEE
// `FpEq`. The query must still type it as the same `Proposition::Eq` over the
// float domain (it fell out as Opaque without the `FpEq` arm), narrowing the
// literal onto an `f32` peer exactly as `Eq` and the orderings do.
#[test]
fn float_literal_equality_stays_a_typed_proposition() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind as Predicate, TrustContractProposition as Proposition,
        TrustContractPropositionDomain as Domain,
    };

    assert!(
        matches!(trust_types::parse_spec_expr("x == 1.0"), Some(trust_types::Formula::FpEq(..))),
        "the parser's spelling this test relies on changed"
    );
    with_test_session_globals(|| {
        for (width, bits) in [(64, 1.0_f64.to_bits()), (32, u64::from(1.0_f32.to_bits()))] {
            let predicate = lowered_contract_text_with_domains(
                "x == 1.0".to_string(),
                &[LoweredVariableDomain { name: "x".to_string(), domain: Domain::Float { width } }],
            );
            let Predicate::Typed { proposition, .. } = &predicate else {
                panic!("an f{width} literal equality must stay typed, got {predicate:?}");
            };
            assert_eq!(
                proposition,
                &Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::Float { width },
                    }),
                    Box::new(Proposition::Float { bits, width }),
                )
            );
        }
        // A literal of the wrong format is not a typed equality.
        let mixed = lowered_contract_text_with_domains(
            "x == 0.1".to_string(),
            &[LoweredVariableDomain { name: "x".to_string(), domain: Domain::Float { width: 32 } }],
        );
        assert!(matches!(mixed, Predicate::Opaque { .. }), "{mixed:?}");
    });
}
