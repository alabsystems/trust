//! Positive-share postconditions must expose their Boolean violation to the
//! existing arithmetic certificate machinery, retaining the original VC identity.
//! These are shared-engine tests, not a new native compiler acceptance claim.

use trust_certify::{certify_vc_reporting_stop, recheck_vc_cleancic, replay_vc_evidence};
use trust_ir::ProofEvidence;
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}
fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}
fn implies(a: Formula, b: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(b))
}
fn vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "budget::split_budget_ms".into(),
        location: SourceSpan {
            file: "positive_share.rs".into(),
            line_start: 11,
            col_start: 1,
            line_end: 19,
            col_end: 2,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}
fn positive_clause(bound: i128) -> Formula {
    implies(gt(int("total_ms"), Formula::Int(bound)), gt(int("_0"), Formula::Int(bound)))
}
fn alias_violation(clause: Formula) -> VerificationCondition {
    vc(Formula::And(vec![eq(int("_0"), int("total_ms")), not(clause)]))
}
fn certified(row: &VerificationCondition) -> ProofEvidence {
    let (evidence, stop) = certify_vc_reporting_stop(row);
    assert_eq!(stop, None, "this small proof must not require a stopped search");
    let evidence = evidence.expect("the original violation must be kernel certified");
    let ProofEvidence::CleanCic { term, context, .. } = &evidence else {
        panic!("only an actual CleanCic proof is acceptable");
    };
    assert!(!term.is_empty() && !context.is_empty());
    assert!(replay_vc_evidence(row, &evidence), "consumer regeneration must match the original VC");
    evidence
}

#[test]
fn exact_alias_and_negated_implication_certifies_and_replays() {
    certified(&alias_violation(positive_clause(0)));
}

#[test]
fn guarded_positive_share_spellings_certify_and_replay() {
    // The guarded spelling after its return branch has set _0 = total_ms.
    let mut guarded = alias_violation(positive_clause(0));
    let Formula::And(parts) = &mut guarded.formula else { unreachable!() };
    parts.insert(0, gt(int("total_ms"), Formula::Int(0)));
    certified(&guarded);

    // Nested conjunctions and a compound consequent must expose only their
    // logical consequences, without discarding the zero-domain branch.
    let clause = implies(
        Formula::And(vec![Formula::Bool(true), gt(int("total_ms"), Formula::Int(0))]),
        not(not(gt(int("_0"), Formula::Int(0)))),
    );
    certified(&alias_violation(clause));
}

#[test]
fn disjunction_positive_share_certifies_and_replays() {
    // The source-equivalent `total_ms == 0 || result >= 1` needs the actual
    // unsigned domain. This explicitly supplied premise is not inferred from
    // the variable name: without it, total_ms = result = -1 is a countermodel.
    let row = vc(Formula::And(vec![
        Formula::Ge(Box::new(int("total_ms")), Box::new(Formula::Int(0))),
        eq(int("_0"), int("total_ms")),
        not(Formula::Or(vec![
            eq(int("total_ms"), Formula::Int(0)),
            Formula::Ge(Box::new(int("_0")), Box::new(Formula::Int(1))),
        ])),
    ]));
    certified(&row);
}

#[test]
fn satisfiable_neighbors_never_certify() {
    let rows = [
        // total_ms=1, _0=other=0: wrong alias.
        vc(Formula::And(vec![eq(int("_0"), int("other")), not(positive_clause(0))])),
        // total_ms=1, _0=0: missing alias.
        vc(not(positive_clause(0))),
        // total_ms=_0=1: invalid stronger consequent.
        alias_violation(implies(
            gt(int("total_ms"), Formula::Int(0)),
            gt(int("_0"), Formula::Int(1)),
        )),
        // total_ms=_0=-1: disjunction without unsigned-domain premise.
        alias_violation(Formula::Or(vec![
            eq(int("total_ms"), Formula::Int(0)),
            Formula::Ge(Box::new(int("_0")), Box::new(Formula::Int(1))),
        ])),
        // total_ms=_0=1: only the second conjunct fails. Negating And
        // must not invent the false fact that the first conjunct fails too.
        alias_violation(implies(
            gt(int("total_ms"), Formula::Int(0)),
            Formula::And(vec![gt(int("_0"), Formula::Int(0)), gt(int("_0"), Formula::Int(1))]),
        )),
        // total_ms=_0=0: only the second disjunct of the antecedent holds.
        // A positive Or must not be split into asserted conjuncts.
        alias_violation(implies(
            Formula::Or(vec![
                gt(int("total_ms"), Formula::Int(0)),
                eq(int("total_ms"), Formula::Int(0)),
            ]),
            gt(int("_0"), Formula::Int(0)),
        )),
    ];
    for row in rows {
        let (evidence, stop) = certify_vc_reporting_stop(&row);
        assert_eq!(stop, None);
        assert!(evidence.is_none(), "a genuine countermodel exists: {:?}", row.formula);
    }
}

#[test]
fn nested_unasserted_implication_is_not_exposed_as_a_conjunct() {
    // The first disjunct is true when total_ms=1, _0=0; its sibling is not
    // asserted. Visiting that sibling as if asserted would falsely refute it.
    let row = vc(Formula::And(vec![
        eq(int("_0"), Formula::Int(0)),
        eq(int("total_ms"), Formula::Int(1)),
        Formula::Or(vec![Formula::Bool(true), not(positive_clause(0))]),
    ]));
    assert!(certify_vc_reporting_stop(&row).0.is_none());
}

#[test]
fn ill_sorted_implication_refuses_before_normalization() {
    let row = alias_violation(implies(int("total_ms"), gt(int("_0"), Formula::Int(0))));
    assert!(certify_vc_reporting_stop(&row).0.is_none());
}

#[test]
fn original_identity_and_regenerated_context_remain_authoritative() {
    let row = alias_violation(positive_clause(0));
    let evidence = certified(&row);
    let mut changed = row.clone();
    changed.function = "budget::different_function".into();
    assert!(!replay_vc_evidence(&changed, &evidence));
    changed = row.clone();
    changed.location.line_start += 1;
    assert!(!replay_vc_evidence(&changed, &evidence));
    changed = row.clone();
    changed.formula = Formula::And(vec![Formula::Bool(true), changed.formula]);
    assert!(!replay_vc_evidence(&changed, &evidence), "equivalent is not the original identity");

    let other = certified(&alias_violation(positive_clause(7)));
    let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else { unreachable!() };
    let ProofEvidence::CleanCic { context: other_context, .. } = other else { unreachable!() };
    assert_ne!(context, other_context);
    assert!(!recheck_vc_cleancic(&term, &other_context, &lineage, &row));
    let mut tampered_term = term.clone();
    tampered_term[0] ^= 1;
    assert!(!recheck_vc_cleancic(&tampered_term, &context, &lineage, &row));
}
