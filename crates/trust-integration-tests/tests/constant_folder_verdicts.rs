// trust-integration-tests/tests/constant_folder_verdicts.rs
//
// Constant-folder verdicts: dispatches ground VCs (no free variables, nothing
// but boolean structure and integer-literal equality) to trust-router's
// `ConstantFolderBackend` and pins the verdict it returns. The folder must
// accept each VC and decide it; a VC it declines or leaves Unknown fails.
//
// Until 2026-10-09 this file was `cross_backend_consistency.rs`: it sent each
// VC to every backend in a `test_backends()` list and asserted they agreed.
// Since the ay backend was removed that list held the constant folder alone,
// so the agreement loop compared nothing, and the 8 tests that needed a second
// backend (7 cases: 2 `Add` equalities, 2 `Lt` comparisons, an `Implies`, a
// free `Var` and an `Ite`; plus the meta-test asserting at least 2 backends)
// sat behind an empty `ay-backend = []` feature that no lane, script or
// manifest enabled. Those 8, the empty feature, and a distinct-names meta-test
// that cannot fail with one backend were deleted, and the suite was renamed to
// what it checks. A verdict-agreement differential needs a second decision
// procedure (for example trust-router's in-process ay backend behind
// `trust-router/ay-backend`) and a lane that runs it; none exists today.
// (trust-router's `tests/constant_polarity_audit.rs` does run several backends,
// but it checks only that none inverts the polarity of a `Bool` constant.)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow std HashMap — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_router::VerificationBackend;
use trust_router::constant_folder::ConstantFolderBackend;
use trust_types::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// The verdict classes a test pins. `Unknown` and `Timeout` are both
/// `Inconclusive`: the folder could not decide the VC.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Failed,
    Inconclusive, // Unknown or Timeout
}

impl From<&VerificationResult> for Verdict {
    fn from(r: &VerificationResult) -> Self {
        match r {
            VerificationResult::Proved { .. } => Verdict::Proved,
            VerificationResult::Failed { .. } => Verdict::Failed,
            VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                Verdict::Inconclusive
            }
            _ => Verdict::Inconclusive,
        }
    }
}

/// Build a VC with the given kind and formula.
fn make_vc(kind: VcKind, formula: Formula, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// The constant folder's verdict on `vc`. The folder must accept the VC and
/// decide it: a declined or undecided VC fails the test instead of passing it.
fn folded_verdict(vc: &VerificationCondition, test_label: &str) -> Verdict {
    let backend = ConstantFolderBackend;
    assert!(backend.can_handle(vc), "{test_label}: the constant folder declined the VC");
    let result = backend.verify(vc);
    let verdict = Verdict::from(&result);
    eprintln!("  [{}] {test_label}: {result:?} -> {verdict:?}", backend.name());
    assert_ne!(
        verdict,
        Verdict::Inconclusive,
        "{test_label}: the constant folder produced no definitive result: {result:?}"
    );
    verdict
}

// ---------------------------------------------------------------------------
// Constant-folder verdict tests
// ---------------------------------------------------------------------------

/// Trivially false formula (UNSAT) => Proved.
#[test]
fn constant_folder_trivially_false_is_proved() {
    let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(false), "trivial_false");
    assert_eq!(folded_verdict(&vc, "Bool(false)"), Verdict::Proved);
}

/// Trivially true formula (SAT) => Failed.
#[test]
fn constant_folder_trivially_true_is_failed() {
    let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true), "trivial_true");
    assert_eq!(folded_verdict(&vc, "Bool(true)"), Verdict::Failed);
}

/// Constant equality: 2 == 2 is SAT => Failed.
#[test]
fn constant_folder_eq_same_constants() {
    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(2)));
    let vc = make_vc(VcKind::Assertion { message: "eq_same".into() }, formula, "eq_same");
    assert_eq!(folded_verdict(&vc, "Eq(2,2)"), Verdict::Failed);
}

/// Constant inequality: 2 == 3 is UNSAT => Proved.
#[test]
fn constant_folder_eq_different_constants() {
    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "eq_diff");
    assert_eq!(folded_verdict(&vc, "Eq(2,3)"), Verdict::Proved);
}

/// Negation of true: Not(true) => false => UNSAT => Proved.
#[test]
fn constant_folder_not_true_is_proved() {
    let formula = Formula::Not(Box::new(Formula::Bool(true)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_true");
    assert_eq!(folded_verdict(&vc, "Not(true)"), Verdict::Proved);
}

/// Negation of false: Not(false) => true => SAT => Failed.
#[test]
fn constant_folder_not_false_is_failed() {
    let formula = Formula::Not(Box::new(Formula::Bool(false)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_false");
    assert_eq!(folded_verdict(&vc, "Not(false)"), Verdict::Failed);
}

/// And(true, true) => true => SAT => Failed.
#[test]
fn constant_folder_and_true_true() {
    let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(true)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "and_tt");
    assert_eq!(folded_verdict(&vc, "And(true,true)"), Verdict::Failed);
}

/// And(true, false) => false => UNSAT => Proved.
#[test]
fn constant_folder_and_true_false() {
    let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "and_tf");
    assert_eq!(folded_verdict(&vc, "And(true,false)"), Verdict::Proved);
}

/// Or(false, false) => false => UNSAT => Proved.
#[test]
fn constant_folder_or_false_false() {
    let formula = Formula::Or(vec![Formula::Bool(false), Formula::Bool(false)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "or_ff");
    assert_eq!(folded_verdict(&vc, "Or(false,false)"), Verdict::Proved);
}

/// Or(false, true) => true => SAT => Failed.
#[test]
fn constant_folder_or_false_true() {
    let formula = Formula::Or(vec![Formula::Bool(false), Formula::Bool(true)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "or_ft");
    assert_eq!(folded_verdict(&vc, "Or(false,true)"), Verdict::Failed);
}

/// Nested: Not(And(true, true)) => Not(true) => false => UNSAT => Proved.
#[test]
fn constant_folder_nested_not_and() {
    let formula =
        Formula::Not(Box::new(Formula::And(vec![Formula::Bool(true), Formula::Bool(true)])));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_and");
    assert_eq!(folded_verdict(&vc, "Not(And(true,true))"), Verdict::Proved);
}

/// Postcondition VC kind: the folder handles L1Functional-level VCs too.
#[test]
fn constant_folder_postcondition_trivial() {
    let vc = make_vc(VcKind::Postcondition, Formula::Bool(false), "postcond_false");
    assert_eq!(folded_verdict(&vc, "Postcondition(false)"), Verdict::Proved);
}

/// Index bounds VC kind with trivially false formula.
#[test]
fn constant_folder_index_bounds() {
    let vc = make_vc(VcKind::IndexOutOfBounds, Formula::Bool(false), "idx_bounds_false");
    assert_eq!(folded_verdict(&vc, "IndexOutOfBounds(false)"), Verdict::Proved);
}

/// Remainder by zero VC kind with trivially true formula.
#[test]
fn constant_folder_remainder_by_zero() {
    let vc = make_vc(VcKind::RemainderByZero, Formula::Bool(true), "rem_zero_true");
    assert_eq!(folded_verdict(&vc, "RemainderByZero(true)"), Verdict::Failed);
}
