// A context atom which this refuter cannot turn into a chain edge must not
// suppress an otherwise exact disjunctive certificate.
//
// This exercises only public certificate/recheck APIs.  The internal allocation
// invariant is pinned by the sibling unit test in `src/lib.rs`.

use trust_certify::{certify_vc, recheck_vc_cleancic};
use trust_ir::ProofEvidence;
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn lit(value: i128) -> Formula {
    Formula::Int(value)
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn nested_sum() -> Formula {
    Formula::Add(Box::new(Formula::Add(Box::new(int("x")), Box::new(int("x")))), Box::new(int("x")))
}

fn vc(function: &str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: function.into(),
        location: SourceSpan {
            file: "disjunctive_context_subset.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 1,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn bounded_disjunction(extra: Option<Formula>) -> Formula {
    let mut conjuncts = vec![le(lit(0), int("x"))];
    if let Some(extra) = extra {
        conjuncts.push(extra);
    }
    conjuncts.push(le(int("x"), lit(10)));
    conjuncts.push(Formula::Or(vec![lt(int("x"), lit(0)), gt(int("x"), lit(10))]));
    Formula::And(conjuncts)
}

fn clean_cic(vc: &VerificationCondition) -> (Vec<u8>, Vec<u8>, trust_ir::ProofDigest) {
    let ProofEvidence::CleanCic { term, context, lineage, .. } =
        certify_vc(vc).expect("the retained context must refute both disjuncts")
    else {
        panic!("expected CleanCic evidence");
    };
    assert!(
        recheck_vc_cleancic(&term, &context, &lineage, vc),
        "canonical regeneration must reproduce and Clean-recheck the exact payload"
    );
    (term, context, lineage)
}

#[test]
fn same_variable_nested_sum_context_certifies_and_exactly_rechecks() {
    // `collect_supported_atoms` accepts the equality's nested linear terms, but
    // the chain refuter cannot represent `(x+x)+x` as one edge.  Both relevance
    // passes retain the equality because its only variable is the disjunction's
    // own `x`.  The usable subset `0≤x≤10` still refutes BOTH alternatives.
    let formula = bounded_disjunction(Some(eq(nested_sum(), lit(15))));
    let vc = vc("same_variable_nested_sum_context", formula);
    let _ = clean_cic(&vc);
}

#[test]
fn skipping_context_never_weakens_the_disjunction() {
    // A real model exists: x=10 satisfies 0≤x≤10, 3x=30, and x>9.  Restoring a
    // certificate here would mean the conclusion/disjunct itself was weakened.
    let satisfiable = Formula::And(vec![
        le(lit(0), int("x")),
        le(int("x"), lit(10)),
        eq(nested_sum(), lit(30)),
        Formula::Or(vec![lt(int("x"), lit(0)), gt(int("x"), lit(9))]),
    ]);
    assert!(
        certify_vc(&vc("satisfiable_nested_sum_context", satisfiable)).is_none(),
        "a satisfiable candidate disjunction must remain uncertified"
    );
}

#[test]
fn wide_uint_context_was_already_filtered_and_preserves_proof_bytes() {
    let base = vc("wide_uint_context", bounded_disjunction(None));
    let wide =
        vc("wide_uint_context", bounded_disjunction(Some(eq(int("x"), Formula::UInt(u128::MAX)))));
    let (base_term, base_context, base_lineage) = clean_cic(&base);
    let (wide_term, wide_context, wide_lineage) = clean_cic(&wide);

    // UInt(u128::MAX) is rejected by collect_supported_atoms before context
    // construction, so changing the later skip policy must not perturb the
    // canonical proof/context bytes for this historical control.
    assert_eq!(wide_term, base_term);
    assert_eq!(wide_context, base_context);
    assert_ne!(
        wide_lineage, base_lineage,
        "lineage still binds the distinct full obligation formula"
    );
}
