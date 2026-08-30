use trust_ir::ProofEvidence;
use trust_types::{SourceSpan, VcKind};

use super::*;

#[derive(Clone, Copy)]
enum Mutation {
    Honest,
    MissingRequires,
    MalformedReification,
    MissingResultBinding,
}

fn violation(mutation: Mutation) -> Formula {
    use Formula as F;
    let iv = |name: &str| F::Var(name.to_string(), Sort::Int);
    let bv = |name: &str| F::Var(name.to_string(), Sort::Bool);
    let le = |a, b| F::Le(Box::new(a), Box::new(b));
    let lt = |a, b| F::Lt(Box::new(a), Box::new(b));
    let gt = |a, b| F::Gt(Box::new(a), Box::new(b));
    let ge = |a, b| F::Ge(Box::new(a), Box::new(b));
    let eq = |a, b| F::Eq(Box::new(a), Box::new(b));
    let not = |a| F::Not(Box::new(a));
    let implies = |a, b| F::Implies(Box::new(a), Box::new(b));
    const IMAX: i128 = i128::MAX;
    const UMAX: u128 = u128::MAX;

    let arm = |second: F| {
        let reified_hi = if matches!(mutation, Mutation::MalformedReification) {
            eq(bv("_10"), F::Int(1))
        } else {
            eq(bv("_10"), gt(iv("_8"), iv("hi")))
        };
        let mut state = vec![
            F::And(vec![le(F::Int(0), iv("_6")), le(iv("_6"), F::UInt(UMAX))]),
            F::And(vec![le(F::Int(-IMAX - 1), iv("_8")), le(iv("_8"), F::Int(IMAX))]),
            eq(bv("_9"), lt(iv("_8"), iv("lo"))),
            reified_hi,
        ];
        if !matches!(mutation, Mutation::MissingResultBinding) {
            state.push(F::And(vec![
                implies(not(bv("_10")), eq(iv("_4"), iv("_8"))),
                implies(not(not(bv("_10"))), eq(iv("_4"), iv("hi"))),
            ]));
        }
        state.push(F::And(vec![
            eq(iv("_0"), iv("_4")),
            eq(iv("_5"), iv("_4")),
            F::And(vec![
                eq(iv("_0"), iv("_5")),
                F::And(vec![
                    eq(iv("_0"), iv("_5b")),
                    not(F::And(vec![le(iv("lo"), iv("_0")), le(iv("_0"), iv("hi"))])),
                ]),
            ]),
        ]));

        let mut members = vec![not(lt(iv("_8"), iv("lo"))), second];
        if !matches!(mutation, Mutation::MissingRequires) {
            members.push(le(iv("lo"), iv("hi")));
        }
        members.push(F::And(state));
        F::And(members)
    };

    F::And(vec![
        ge(iv("off"), F::Int(0)),
        F::Or(vec![arm(not(gt(iv("_8"), iv("hi")))), arm(gt(iv("_8"), iv("hi")))]),
    ])
}

fn vc(mutation: Mutation) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "r174::branch_clamp".into(),
        location: SourceSpan::default(),
        formula: violation(mutation),
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn exact_postcondition_kernel_and_lineage_recheck() {
    let vc = vc(Mutation::Honest);
    let ProofEvidence::CleanCic { term, context, lineage, .. } =
        certify_vc(&vc).expect("branch clamp must certify")
    else {
        panic!("expected CleanCic evidence");
    };
    assert!(recheck_vc_cleancic(&term, &context, &lineage, &vc));

    let mut wrong_identity = vc.clone();
    wrong_identity.function = format!("{}::other", wrong_identity.function.as_str()).into();
    assert!(!recheck_vc_cleancic(&term, &context, &lineage, &wrong_identity));

    let mut malformed_term = term.clone();
    malformed_term[0] ^= 1;
    assert!(!recheck_vc_cleancic(&malformed_term, &context, &lineage, &vc));
}

#[test]
fn missing_requires_declines() {
    assert!(certify_vc(&vc(Mutation::MissingRequires)).is_none());
}

#[test]
fn malformed_reification_declines_before_derivation() {
    let vc = vc(Mutation::MalformedReification);
    assert!(!formula_is_well_sorted_bool(&vc.formula));
    assert!(certify_vc(&vc).is_none());
}

#[test]
fn missing_result_binding_declines() {
    assert!(certify_vc(&vc(Mutation::MissingResultBinding)).is_none());
}

#[test]
fn misbound_derived_proposition_is_rejected_by_clean() {
    let a = Formula::Var("a".to_string(), Sort::Int);
    let b = Formula::Var("b".to_string(), Sort::Int);
    let wrong = le_int(chain_var_expr("b"), chain_var_expr("a"));
    let wrong_props = vec![wrong.clone(), wrong];
    let carrier = build_and_prop(&wrong_props).expect("two propositions make a carrier");
    let disjunct = Disjunct {
        prop: carrier.clone(),
        smt: "(and (< a b) (<= b a))".to_string(),
        refutation: DisjunctRefutation::DerivedChainAtoms {
            atoms: vec![(a.clone(), b.clone(), true), (b.clone(), a.clone(), false)],
            props: wrong_props,
        },
    };
    let fvar = FVarId::new(HYP_FVAR_BASE);
    let false_term = refute_disjunct(&disjunct, &[], Expr::fvar(fvar))
        .expect("the syntactic edge cycle alone builds a candidate term");
    let hyps = vec![Hyp { smt: disjunct.smt, prop: carrier, fvar, name: "h_0".to_string() }];
    let vars = ["a", "b"].into_iter().map(str::to_string).collect();
    let violation = Formula::And(vec![
        Formula::Lt(Box::new(a), Box::new(b.clone())),
        Formula::Le(Box::new(b), Box::new(Formula::Var("a".to_string(), Sort::Int))),
    ]);
    let identity = ObligationIdentity::from_violation(&violation).expect("well-sorted identity");
    assert!(finish_certificate(&hyps, &false_term, &vars, &identity).is_none());
}

fn test_order_edge(from: &str, to: &str, strict: bool, id: u64) -> OrderEdge {
    let a = Formula::Var(from.to_string(), Sort::Int);
    let b = Formula::Var(to.to_string(), Sort::Int);
    build_order_edge(&a, &b, strict, Expr::fvar(FVarId::new(10_000 + id)))
        .expect("simple Int variables make an order edge")
}

#[test]
fn all_nonstrict_cycle_is_not_a_contradiction() {
    let edges = vec![
        test_order_edge("a", "b", false, 0),
        test_order_edge("b", "c", false, 1),
        test_order_edge("c", "a", false, 2),
    ];
    assert!(refute_via_var_cycle_k(&edges).is_none());
}

#[test]
fn distribution_atom_edge_and_depth_caps_fail_closed() {
    let pieces: Vec<Formula> = (0..17)
        .map(|n| {
            Formula::Le(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(n)),
            )
        })
        .collect();
    let arm = Formula::And(vec![Formula::Not(Box::new(Formula::And(pieces)))]);
    assert!(distribute_negated_conjunctions(&[arm]).is_none());

    let too_many_atoms = Formula::And(
        (0..49)
            .map(|n| {
                Formula::Le(
                    Box::new(Formula::Var(format!("v{n}"), Sort::Int)),
                    Box::new(Formula::Var(format!("v{}", n + 1), Sort::Int)),
                )
            })
            .collect(),
    );
    assert!(parse_and_disjunct_entailed_order_atoms(&too_many_atoms).is_none());

    let mut exact_edge_cap = vec![
        test_order_edge("edge_a", "edge_b", true, 0),
        test_order_edge("edge_b", "edge_a", false, 1),
    ];
    while exact_edge_cap.len() < 48 {
        let n = exact_edge_cap.len();
        exact_edge_cap.push(test_order_edge(
            &format!("irrelevant_from_{n}"),
            &format!("irrelevant_to_{n}"),
            false,
            n as u64,
        ));
    }
    assert!(refute_via_var_cycle_k(&exact_edge_cap).is_some());

    let mut over_edge_cap = exact_edge_cap;
    over_edge_cap.push(test_order_edge("extra_from", "extra_to", false, 49));
    assert_eq!(over_edge_cap.len(), 49);
    assert!(refute_via_var_cycle_k(&over_edge_cap).is_none());

    let mut too_deep = vec![test_order_edge("n0", "n1", true, 100)];
    for n in 1..24 {
        too_deep.push(test_order_edge(&format!("n{n}"), &format!("n{}", n + 1), false, 100 + n));
    }
    too_deep.push(test_order_edge("n24", "n0", false, 124));
    assert!(refute_via_var_cycle_k(&too_deep).is_none());
}

#[test]
fn member_cap_accepts_256_and_declines_257() {
    let exact = vec![Formula::Bool(true); 256];
    let exact_refs: Vec<&Formula> = exact.iter().collect();
    assert_eq!(derive_disjunct_entailed_atoms(&exact_refs), Some(Vec::new()));

    let over = vec![Formula::Bool(true); 257];
    let over_refs: Vec<&Formula> = over.iter().collect();
    assert!(derive_disjunct_entailed_atoms(&over_refs).is_none());
}

fn bool_definition(n: usize) -> Formula {
    Formula::Eq(
        Box::new(Formula::Var(format!("b{n}"), Sort::Bool)),
        Box::new(Formula::Var(format!("p{n}"), Sort::Bool)),
    )
}

#[test]
fn reification_cap_accepts_64_and_declines_65() {
    let exact: Vec<Formula> = (0..64).map(bool_definition).collect();
    let exact_refs: Vec<&Formula> = exact.iter().collect();
    assert_eq!(derive_disjunct_entailed_atoms(&exact_refs), Some(Vec::new()));

    let over: Vec<Formula> = (0..65).map(bool_definition).collect();
    let over_refs: Vec<&Formula> = over.iter().collect();
    assert!(derive_disjunct_entailed_atoms(&over_refs).is_none());
}

fn derived_cap_pool(extra_consequence: bool) -> Vec<Formula> {
    let mut pool: Vec<Formula> = (0..64).map(bool_definition).collect();
    pool.extend((0..64).map(|n| Formula::Var(format!("b{n}"), Sort::Bool)));
    pool.extend((0..64).map(|n| Formula::Not(Box::new(Formula::Var(format!("b{n}"), Sort::Bool)))));
    if extra_consequence {
        pool.push(Formula::Implies(
            Box::new(Formula::Var("b0".to_string(), Sort::Bool)),
            Box::new(Formula::Var("extra".to_string(), Sort::Bool)),
        ));
    }
    pool
}

#[test]
fn derived_fact_cap_accepts_128_and_declines_129() {
    let exact = derived_cap_pool(false);
    let exact_refs: Vec<&Formula> = exact.iter().collect();
    assert_eq!(derive_disjunct_entailed_atoms(&exact_refs).map(|facts| facts.len()), Some(128));

    let over = derived_cap_pool(true);
    let over_refs: Vec<&Formula> = over.iter().collect();
    assert!(derive_disjunct_entailed_atoms(&over_refs).is_none());
}

/// A 37-edge graph whose duplicated two-level dead branches consume a
/// predictable inspection count before the final `a -> s` return edge.
fn inspection_boundary_cycle(target_position: usize) -> Vec<OrderEdge> {
    let mut edges = vec![test_order_edge("s", "a", true, 1_000)];
    for n in 0..10 {
        edges.push(test_order_edge("a", "d", false, 1_010 + n));
    }
    for n in 0..10 {
        edges.push(test_order_edge("d", "e", false, 1_020 + n));
    }
    while edges.len() < target_position {
        let n = edges.len();
        edges.push(test_order_edge(&format!("f{n}"), &format!("g{n}"), false, 1_100 + n as u64));
    }
    assert_eq!(edges.len(), target_position);
    edges.push(test_order_edge("a", "s", false, 1_200));
    while edges.len() < 37 {
        let n = edges.len();
        edges.push(test_order_edge(&format!("u{n}"), &format!("v{n}"), false, 1_300 + n as u64));
    }
    edges
}

#[test]
fn dfs_inspection_cap_accepts_4096_and_declines_4097() {
    let exact = inspection_boundary_cycle(25);
    assert!(refute_via_var_cycle_k_with_budget(&exact, 4095).is_none());
    assert!(refute_via_var_cycle_k_with_budget(&exact, 4096).is_some());
    assert!(refute_via_var_cycle_k(&exact).is_some());

    let over = inspection_boundary_cycle(26);
    assert!(refute_via_var_cycle_k_with_budget(&over, 4096).is_none());
    assert!(refute_via_var_cycle_k_with_budget(&over, 4097).is_some());
    assert!(refute_via_var_cycle_k(&over).is_none());
}
