//! TINV step 7.2: the structural situatedness check the kernel gate applies to a
//! `VcKind::TypeInvariant` row. Since step 7.7 the kind gate admits the kind, so this check
//! is the whole of `VerificationCondition::kernel_authority_refusal` for a TINV row.

use trust_types::{
    Formula, ObligationRecord, ObligationWrapper, Sort, SourceSpan, TypeInvariantPoint,
    TypeInvariantSite, VcKind, VerificationCondition,
};

fn var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn tinv(formula: Formula, record: Option<ObligationRecord>) -> VerificationCondition {
    tinv_edge(formula, record, None)
}

fn tinv_edge(
    formula: Formula,
    record: Option<ObligationRecord>,
    edge: Option<usize>,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::TypeInvariant {
            ty: "c::Parser".into(),
            point: TypeInvariantPoint::Return,
            site: TypeInvariantSite { block: 1, statement_index: 0 },
            conjunct: 0,
            ordinal: 0,
            edge,
        },
        function: "c::Parser::bump".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: record,
    }
}

fn record(body: Formula, wrappers: Vec<ObligationWrapper>) -> ObligationRecord {
    ObligationRecord { body, wrappers, subject: None, width: None }
}

/// The 0(b)(c) linear preservation row: `i1 = i0 + 1 ∧ i0 < n ∧ ¬(i1 <= n)`.
fn linear_body() -> Formula {
    Formula::And(vec![
        Formula::Eq(
            Box::new(var("i1")),
            Box::new(Formula::Add(Box::new(var("i0")), Box::new(Formula::Int(1)))),
        ),
        Formula::Lt(Box::new(var("i0")), Box::new(var("n"))),
        Formula::Not(Box::new(Formula::Le(Box::new(var("i1")), Box::new(var("n"))))),
    ])
}

#[test]
fn a_situated_row_passes() {
    let body = linear_body();
    let vc = tinv(body.clone(), Some(record(body, vec![])));
    assert_eq!(vc.type_invariant_situatedness_refusal(), None);
    // Step 7.7: the kind is admitted, so the row gate is the whole verdict.
    assert_eq!(vc.kernel_authority_refusal(), None);
}

#[test]
fn hypotheses_from_wrappers_count() {
    let core = Formula::Not(Box::new(Formula::Le(Box::new(var("i1")), Box::new(var("n")))));
    let facts = vec![Formula::Le(Box::new(var("i1")), Box::new(var("n")))];
    let formula = Formula::And(facts.iter().cloned().chain([core.clone()]).collect());
    let vc = tinv(formula, Some(record(core, vec![ObligationWrapper::ConjoinFactsLast { facts }])));
    assert_eq!(vc.type_invariant_situatedness_refusal(), None);
}

#[test]
fn record_less_bare_and_forged_rows_are_refused() {
    let body = linear_body();
    // No record.
    assert!(tinv(body.clone(), None).type_invariant_situatedness_refusal().is_some());
    assert!(tinv(body.clone(), None).kernel_authority_refusal().is_some());
    // A record that does not replay to the formula.
    let forged = tinv(Formula::Bool(false), Some(record(body.clone(), vec![])));
    assert!(forged.type_invariant_situatedness_refusal().is_some());
    // A bare negated core: no hypothesis at all.
    let bare_core = Formula::Not(Box::new(Formula::Le(Box::new(var("i1")), Box::new(var("n")))));
    let bare = tinv(bare_core.clone(), Some(record(bare_core, vec![])));
    assert!(bare.type_invariant_situatedness_refusal().is_some());
    // A core naming state no hypothesis binds.
    let unbound = Formula::And(vec![
        Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))),
        Formula::Not(Box::new(Formula::Le(Box::new(var("b")), Box::new(var("n"))))),
    ]);
    let vc = tinv(unbound.clone(), Some(record(unbound, vec![])));
    assert!(vc.type_invariant_situatedness_refusal().is_some());
    // A ground core (no names at all) is a tautology check, not a program fact.
    let ground = Formula::And(vec![
        Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))),
        Formula::Not(Box::new(Formula::Le(Box::new(Formula::Int(1)), Box::new(Formula::Int(2))))),
    ]);
    let vc = tinv(ground.clone(), Some(record(ground, vec![])));
    assert!(vc.type_invariant_situatedness_refusal().is_some());
    // The negated core must be LAST.
    let misplaced = Formula::And(vec![
        Formula::Not(Box::new(Formula::Le(Box::new(var("i1")), Box::new(var("n"))))),
        Formula::Lt(Box::new(var("i1")), Box::new(var("n"))),
    ]);
    let vc = tinv(misplaced.clone(), Some(record(misplaced, vec![])));
    assert!(vc.type_invariant_situatedness_refusal().is_some());
}

/// TINV-9(a): an edge part's FIRST body conjunct is its edge guard, a routing condition
/// that binds no program state. A core whose names only the guard binds is refused; the
/// same names bound by a real hypothesis after the guard pass; and the same body with no
/// edge counts its first conjunct as an ordinary hypothesis.
#[test]
fn an_edge_guard_never_binds_the_core() {
    let guard = Formula::Lt(Box::new(var("i")), Box::new(var("n")));
    let neg_core = Formula::Not(Box::new(Formula::Le(Box::new(var("i")), Box::new(var("n")))));
    let only_guard = Formula::And(vec![guard.clone(), neg_core.clone()]);
    let part = tinv_edge(only_guard.clone(), Some(record(only_guard.clone(), vec![])), Some(0));
    assert!(part.type_invariant_situatedness_refusal().is_some(), "bound only by the guard");
    // The guard is skipped, not the facts: a ConjoinFactsLast binding still counts.
    let facts = vec![Formula::Le(Box::new(var("i")), Box::new(var("n")))];
    let formula = Formula::And(facts.iter().cloned().chain([only_guard.clone()]).collect());
    let wrapped = tinv_edge(
        formula,
        Some(record(only_guard.clone(), vec![ObligationWrapper::ConjoinFactsLast { facts }])),
        Some(0),
    );
    assert_eq!(wrapped.type_invariant_situatedness_refusal(), None);
    // A binding body hypothesis after the guard passes.
    let bound = Formula::And(vec![
        Formula::Bool(true),
        Formula::Eq(Box::new(var("i")), Box::new(var("n"))),
        neg_core.clone(),
    ]);
    let part = tinv_edge(bound.clone(), Some(record(bound, vec![])), Some(2));
    assert_eq!(part.type_invariant_situatedness_refusal(), None);
    // The SAME guard-only body on a whole row (no edge): its conjunct is a hypothesis.
    let whole = tinv(only_guard.clone(), Some(record(only_guard, vec![])));
    assert_eq!(whole.type_invariant_situatedness_refusal(), None);
    // An edge part with no guard slot: the binding hypothesis is in the guard position,
    // so it is skipped, and a bare negated core has no slot at all.
    let slotless = linear_body();
    let part = tinv_edge(slotless.clone(), Some(record(slotless, vec![])), Some(0));
    assert!(part.type_invariant_situatedness_refusal().is_some());
    let bare = tinv_edge(neg_core.clone(), Some(record(neg_core, vec![])), Some(0));
    assert!(bare.type_invariant_situatedness_refusal().is_some());
}
