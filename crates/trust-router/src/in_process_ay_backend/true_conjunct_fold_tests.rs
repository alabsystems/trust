// trust-router/in_process_ay_backend/true_conjunct_fold_tests.rs: a `true`
// conjunct, a `false` disjunct or a unary `or` folded away by ay's elaborator
// must not cost the in-process lane a correct UNSAT.
//
// Measured 2026-10-06 on the ay pin cb87694a9: over Int a, b the violation
// `Or([And([a <= b, And([true, Not(a <= b)])])])`, plainly UNSAT, came back
// `unknown (incomplete self-check-rejected)`, while the same formula without
// the `true`, and its conjunction-spine-flattened form, were Proved. ay folded
// the `true` conjunct and the complement pair to `false` keeping no
// derivation, and its strict proof gate (rightly) refused the bare `hole`
// left behind. Fixed in ay ba4e7b5d1 (descendant surface overrides no longer
// hijack the operand a fold lands on; a propositional fold-identity refuter
// derives the fold through `or`/`not`), carried onto the pin as a cherry-pick.
//
// Every UNSAT row must be Proved: an Unknown is a lost verdict, and a Failed
// would be unsound. The SAT controls must stay refuted, so the fix cannot be
// passing by proving everything.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, VerificationResult};

use super::{InProcessAyBackend, execute_direct};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}

/// `a <= b` over Int: a theory atom, so ay's bounded Bool interpreter cannot
/// close the root by itself.
fn le() -> Formula {
    Formula::Le(b(Formula::Var("a".into(), Sort::Int)), b(Formula::Var("b".into(), Sort::Int)))
}

fn not(f: Formula) -> Formula {
    Formula::Not(b(f))
}

fn assert_proved(formula: &Formula, what: &str) {
    let result = InProcessAyBackend::new().run(formula);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "{what}: an UNSAT violation must be Proved, got {result:?}"
    );
}

fn assert_refuted(formula: &Formula, what: &str) {
    let result = InProcessAyBackend::new().run(formula);
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "{what}: a SAT violation must be refuted, got {result:?}"
    );
}

/// The measured row: `(or (and l (and true (not l))))`.
#[test]
fn true_conjunct_under_unary_or_is_proved() {
    if !execute_direct::is_available() {
        return;
    }
    let formula = Formula::Or(vec![Formula::And(vec![
        le(),
        Formula::And(vec![Formula::Bool(true), not(le())]),
    ])]);
    assert_proved(&formula, "(or (and l (and true (not l))))");
}

/// Its controls, Proved on the unfixed pin too: no `true`, and the flattened
/// spine. They pin that the fix did not trade one shape for another.
#[test]
fn true_conjunct_controls_without_the_fold_stay_proved() {
    if !execute_direct::is_available() {
        return;
    }
    let no_true = Formula::Or(vec![Formula::And(vec![le(), not(le())])]);
    assert_proved(&no_true, "(or (and l (not l)))");
    let flat = Formula::Or(vec![Formula::And(vec![le(), Formula::Bool(true), not(le())])]);
    assert_proved(&flat, "(or (and l true (not l)))");
}

/// The sibling shapes ay's fix names: a `false` disjunct, the fold under a
/// negated `or`, and a unary `or` under `and`.
#[test]
fn true_conjunct_sibling_fold_shapes_are_proved() {
    if !execute_direct::is_available() {
        return;
    }
    let complement =
        || Formula::And(vec![le(), Formula::And(vec![Formula::Bool(true), not(le())])]);
    let rows = [
        ("(or X false)", Formula::Or(vec![complement(), Formula::Bool(false)])),
        (
            "(not (or (not l) (and true l)))",
            not(Formula::Or(vec![not(le()), Formula::And(vec![Formula::Bool(true), le()])])),
        ),
        (
            "(and l (or (and true (not l))))",
            Formula::And(vec![
                le(),
                Formula::Or(vec![Formula::And(vec![Formula::Bool(true), not(le())])]),
            ]),
        ),
    ];
    let lost: Vec<String> = rows
        .iter()
        .filter_map(|(what, formula)| {
            let result = InProcessAyBackend::new().run(formula);
            (!matches!(result, VerificationResult::Proved { .. }))
                .then(|| format!("{what}: {result:?}"))
        })
        .collect();
    assert!(lost.is_empty(), "UNSAT violations not Proved:\n{}", lost.join("\n"));
}

/// SAT controls of the same shapes: still refuted.
#[test]
fn true_conjunct_sat_controls_are_refuted() {
    if !execute_direct::is_available() {
        return;
    }
    let rows = [
        (
            "(or (and l (and true l)))",
            Formula::Or(vec![Formula::And(vec![
                le(),
                Formula::And(vec![Formula::Bool(true), le()]),
            ])]),
        ),
        (
            "(or (and l (and true (not l))) l)",
            Formula::Or(vec![
                Formula::And(vec![le(), Formula::And(vec![Formula::Bool(true), not(le())])]),
                le(),
            ]),
        ),
        (
            "(not (or (not l) (and true (not l))))",
            not(Formula::Or(vec![not(le()), Formula::And(vec![Formula::Bool(true), not(le())])])),
        ),
    ];
    for (what, formula) in &rows {
        assert_refuted(formula, what);
    }
}
