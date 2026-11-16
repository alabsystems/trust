//! VGAPS-G1C rows: the element-read congruence certifies, and only where it is a
//! refutation.

use trust_ir::ProofEvidence;

use super::super::*;
use super::certify_element_congruence_disjunction;

fn iv(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}
fn eq_f(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn not_f(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}

/// The L0 `Sub` row of `if i < a.len() && a[i] > 0 { a[i] - 1 }` with two index
/// temps, as trust-vcgen renders it after VGAPS-G1: `_8 = i`, `_12 = i`,
/// `_7 = a*[_8]`, `_7 > 0`, `_11 = a*[_12]`, the congruence over the two reads, and the
/// violation `_11 - 1 < 0`. `index_of_second` is what `_12` is bound to.
fn guarded_reread(index_of_second: &str) -> Formula {
    Formula::And(vec![
        eq_f(iv("_8"), iv("i")),
        eq_f(iv("_12"), iv(index_of_second)),
        eq_f(iv("_7"), iv("a*[_8]")),
        Formula::Gt(Box::new(iv("_7")), Box::new(Formula::Int(0))),
        eq_f(iv("_11"), iv("a*[_12]")),
        Formula::Or(vec![not_f(eq_f(iv("_8"), iv("_12"))), eq_f(iv("a*[_8]"), iv("a*[_12]"))]),
        Formula::Lt(
            Box::new(Formula::Sub(Box::new(iv("_11")), Box::new(Formula::Int(1)))),
            Box::new(Formula::Int(0)),
        ),
    ])
}

fn const_names(term: &[u8]) -> BTreeSet<String> {
    let term = deserialize_term(term).expect("the producer's own serialization");
    let mut names = Vec::new();
    assert!(collect_const_names(&term, &mut names), "every node must be auditable");
    names.iter().map(|n| n.to_string()).collect()
}

#[test]
fn a_guarded_reread_through_two_index_temps_certifies_by_antisymmetry() {
    let violation = guarded_reread("i");
    let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
        certify_violation(&violation)
    else {
        panic!("the congruence row must kernel-certify");
    };
    assert!(
        recheck_cleancic(&term, &context, &lineage, &violation),
        "the producer and the public rechecker regenerate the same certificate"
    );
    let names = const_names(&term);
    for lemma in ["Int.le_antisymm", "Or.rec", "Int.le_trans"] {
        assert!(names.contains(lemma), "the certificate closes through `{lemma}`: {names:?}");
    }
}

/// The counter: `_12 = j`. Nothing forces the indices equal, `a*[_12]` may be 0, and
/// the system is satisfiable, so no lane may certify it.
#[test]
fn an_index_pair_the_context_does_not_force_equal_declines() {
    assert!(certify_violation(&guarded_reread("j")).is_none());
}

/// Before this lane no lane certified the row: the congruence lane is what certifies
/// it (its parser applied to the candidate is the only route), and the index
/// disequality is closed only through a context path in BOTH directions.
#[test]
fn the_disequality_needs_both_directions() {
    let violation = guarded_reread("i");
    let normalized = normalize_violation(&violation).expect("normalizes");
    let conjuncts = normalized.view();
    let identity = ObligationIdentity::from_violation(&violation).expect("identity");
    assert!(
        certify_element_congruence_disjunction(&conjuncts, &identity).is_some(),
        "the lane itself certifies the row"
    );
    // `_8 ≤ i ≤ _12` alone (drop `_12 ≤ i`): one direction only.
    let one_way = Formula::And(vec![
        eq_f(iv("_8"), iv("i")),
        Formula::Le(Box::new(iv("i")), Box::new(iv("_12"))),
        eq_f(iv("_7"), iv("a*[_8]")),
        Formula::Gt(Box::new(iv("_7")), Box::new(Formula::Int(0))),
        eq_f(iv("_11"), iv("a*[_12]")),
        Formula::Or(vec![not_f(eq_f(iv("_8"), iv("_12"))), eq_f(iv("a*[_8]"), iv("a*[_12]"))]),
        Formula::Lt(
            Box::new(Formula::Sub(Box::new(iv("_11")), Box::new(Formula::Int(1)))),
            Box::new(Formula::Int(0)),
        ),
    ]);
    assert!(certify_violation(&one_way).is_none(), "`_12` may exceed `i`: satisfiable");
}

/// The hardened twin of [`guarded_reread`]: the same conjuncts, the element's `u8`
/// range, and the twin's overflow core `Or([_11 - 1 < 0, _11 - 1 > 255])` in place of
/// the one-sided violation, so two disjunctions meet and the tie branch closes only
/// through the core.
fn hardened_twin(index_of_second: &str) -> Formula {
    let sub = || Box::new(Formula::Sub(Box::new(iv("_11")), Box::new(Formula::Int(1))));
    Formula::And(vec![
        eq_f(iv("_8"), iv("i")),
        eq_f(iv("_12"), iv(index_of_second)),
        eq_f(iv("_7"), iv("a*[_8]")),
        Formula::Gt(Box::new(iv("_7")), Box::new(Formula::Int(0))),
        eq_f(iv("_11"), iv("a*[_12]")),
        Formula::Le(Box::new(iv("_11")), Box::new(Formula::Int(255))),
        Formula::Or(vec![not_f(eq_f(iv("_8"), iv("_12"))), eq_f(iv("a*[_8]"), iv("a*[_12]"))]),
        Formula::Or(vec![
            Formula::Lt(sub(), Box::new(Formula::Int(0))),
            Formula::Gt(sub(), Box::new(Formula::Int(255))),
        ]),
    ])
}

#[test]
fn the_hardened_twin_certifies_through_its_overflow_core() {
    let violation = hardened_twin("i");
    let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
        certify_violation(&violation)
    else {
        panic!("the hardened twin must kernel-certify");
    };
    assert!(recheck_cleancic(&term, &context, &lineage, &violation));
    let names = const_names(&term);
    for lemma in ["Int.le_antisymm", "Or.rec"] {
        assert!(names.contains(lemma), "the certificate closes through `{lemma}`: {names:?}");
    }
}

/// The counter of the twin: `_12 = j`, satisfiable (`a*[_12] = 0`), declined.
#[test]
fn the_hardened_twin_of_another_index_declines() {
    assert!(certify_violation(&hardened_twin("j")).is_none());
}

/// The hardened twin as real MIR renders it (`mut_guard_then_use`, line 57): ONE `And`
/// per reaching path of the guard's switch, the congruence and the overflow core inside
/// each, conjuncts the refutation does not need inside (the switch atom, a length, a
/// `Bool` reification), and, when `wide`, the range of every other local outside: 30
/// more ranges, so the full context's edges pass the chain search's cap.
fn per_path_twin(index_of_second: &str, wide: bool) -> Formula {
    let sub = || Box::new(Formula::Sub(Box::new(iv("_18")), Box::new(Formula::Int(1))));
    let path = |switch: Formula| {
        Formula::And(vec![
            switch,
            Formula::Gt(Box::new(iv("_13")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(iv("_9")), Box::new(iv("len"))),
            Formula::And(vec![
                Formula::Or(vec![
                    not_f(eq_f(iv("_14"), iv("_19"))),
                    eq_f(iv("a*[_14]"), iv("a*[_19]")),
                ]),
                Formula::And(vec![
                    eq_f(iv("_9"), iv("i")),
                    eq_f(iv("_14"), iv("i")),
                    eq_f(iv("_13"), iv("a*[_14]")),
                    eq_f(
                        Formula::Var("_12".into(), Sort::Bool),
                        Formula::Gt(Box::new(iv("_13")), Box::new(Formula::Int(0))),
                    ),
                    eq_f(iv("_19"), iv(index_of_second)),
                    Formula::Le(Box::new(Formula::Int(0)), Box::new(iv("_18"))),
                    Formula::Le(Box::new(iv("_18")), Box::new(Formula::Int(255))),
                    eq_f(iv("_18"), iv("a*[_19]")),
                    Formula::Or(vec![
                        Formula::Lt(sub(), Box::new(Formula::Int(0))),
                        Formula::Gt(sub(), Box::new(Formula::Int(255))),
                    ]),
                ]),
            ]),
        ])
    };
    let switch = || Formula::Ge(Box::new(iv("_5")), Box::new(iv("len")));
    let mut conjuncts = vec![Formula::Ge(Box::new(iv("len")), Box::new(Formula::Int(0)))];
    if wide {
        for k in 0..30 {
            let x = iv(&format!("_w{k}"));
            conjuncts.push(Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))));
            conjuncts.push(Formula::Le(Box::new(x), Box::new(Formula::Int(255))));
        }
    }
    conjuncts.push(Formula::Or(vec![path(not_f(switch())), path(switch())]));
    Formula::And(conjuncts)
}

/// The two paths share the congruence and the core, so Or-elimination
/// (`extract_disjunction_common_conjuncts`) surfaces both and the twin closes as
/// [`hardened_twin`] does; with every other local's range in the context (`wide`) it
/// closes only against the context one hop out of the two disjunctions
/// (`one_hop_context`).
#[test]
fn the_per_path_twin_certifies() {
    for wide in [false, true] {
        let violation = per_path_twin("i", wide);
        let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
            certify_violation(&violation)
        else {
            panic!("the per-path twin (wide: {wide}) must kernel-certify");
        };
        assert!(recheck_cleancic(&term, &context, &lineage, &violation));
        let names = const_names(&term);
        for lemma in ["Int.le_antisymm", "Or.rec"] {
            assert!(names.contains(lemma), "the certificate closes through `{lemma}`: {names:?}");
        }
    }
}

/// The counters: `_19 = j`, satisfiable, declined, narrow and wide.
#[test]
fn the_per_path_twin_of_another_index_declines() {
    for wide in [false, true] {
        assert!(certify_violation(&per_path_twin("j", wide)).is_none());
    }
}
