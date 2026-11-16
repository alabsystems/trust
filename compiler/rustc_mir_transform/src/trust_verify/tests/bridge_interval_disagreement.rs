// Trust: fault injection at the interval producer only. The compiler's real AY
// solver, exact-row substitution and proof-authority construction still run.
use std::sync::atomic::{AtomicUsize, Ordering};

use super::*;

struct InjectedInterval {
    result: VerificationResult,
    calls: Arc<AtomicUsize>,
}

impl trust_router::VerificationBackend for InjectedInterval {
    fn name(&self) -> &str {
        "interval-disagreement-test"
    }

    fn can_handle(&self, _: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _: &VerificationCondition) -> VerificationResult {
        self.calls.fetch_add(1, Ordering::SeqCst);
        self.result.clone()
    }
}

struct BridgeRun {
    rows: Vec<(VerificationCondition, VerificationResult)>,
    bindings: Vec<Option<ResultObligationBinding>>,
    eligibility: Vec<Option<SolverRevalidationEligibility>>,
    proved: u32,
    failed: u32,
    calls: usize,
}

fn run_with_interval(vc: &VerificationCondition, result: VerificationResult) -> BridgeRun {
    let function = bridge_test_function();
    let scope = trust_vcgen::GenericRefutationScope::for_function(&function, &[], &[]);
    let obligation = authority_test_native_obligation("bridge:interval-disagreement", 447, 447);
    let mut bindings = vec![test_binding_for_obligation(0, vc, &obligation)];
    assert!(bindings[0].is_some());
    let calls = Arc::new(AtomicUsize::new(0));
    let (rows, proved, failed, eligibility) = bridge_v1_ay_proofs_into_native_results_with_interval(
        &scope,
        5_000,
        trust_types::determinism::EffortScale::BUILTIN,
        None,
        std::slice::from_ref(vc),
        &mut bindings,
        &mut ClockStops::default(),
        true,
        vec![(vc.clone(), bridge_test_unknown())],
        None,
        || {
            trust_router::Router::with_backends(vec![Box::new(InjectedInterval {
                result: result.clone(),
                calls: calls.clone(),
            })])
        },
    );
    BridgeRun { rows, bindings, eligibility, proved, failed, calls: calls.load(Ordering::SeqCst) }
}

fn satisfiable_vc(kind: VcKind) -> VerificationCondition {
    let mut vc = test_vc(447);
    vc.function = "bridge-test".into();
    vc.kind = kind;
    vc.formula = Formula::Eq(
        Box::new(Formula::Var("disagreement_input".into(), Sort::Int)),
        Box::new(Formula::Int(7)),
    );
    vc
}

fn false_interval_proof() -> VerificationResult {
    VerificationResult::Proved {
        solver: "interval-disagreement-test".into(),
        time_ms: 0,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

#[test]
fn admissible_ay_counterexample_replaces_held_interval_proof() {
    for kind in [VcKind::SliceBoundsCheck, VcKind::Precondition { callee: "checked_callee".into() }]
    {
        let vc = satisfiable_vc(kind);
        let run = run_with_interval(&vc, false_interval_proof());
        assert_eq!(run.calls, 1, "the contradictory interval producer must actually run");
        assert_eq!((run.proved, run.failed), (0, 1));
        assert_eq!(run.rows.len(), 1);
        assert_eq!(exact_vc_key(&run.rows[0].0), exact_vc_key(&vc));
        let VerificationResult::Failed { solver, counterexample: Some(model), .. } = &run.rows[0].1
        else {
            panic!("the real AY model must survive the complete bridge: {:?}", run.rows);
        };
        assert_eq!(solver.as_str(), "ay-in-process");
        assert!(
            model.assignments.iter().any(|(name, value)| {
                name == "disagreement_input" && *value == CounterexampleValue::Int(7)
            }),
            "the surviving model must actually satisfy the original violation: {model:?}"
        );
        assert!(
            run.bindings[0].as_ref().is_some_and(|binding| binding.matches_row(0, &run.rows[0].0)),
            "exact obligation binding must survive substitution"
        );
        assert!(
            run.eligibility[0].is_none(),
            "a counterexample must carry no S1 proof eligibility"
        );
        let authorities = build_result_proof_authorities_with_revalidations(
            &run.rows,
            &run.bindings,
            None,
            &[None],
            &[None],
        );
        assert!(authorities[0].is_none(), "the discarded interval proof grants no authority");
    }
}

#[test]
fn proof_only_kinds_still_reject_generic_ay_refutations() {
    for kind in
        [VcKind::Postcondition, VcKind::Assertion { message: "approximate assertion".into() }]
    {
        let vc = satisfiable_vc(kind);
        let run = run_with_interval(&vc, false_interval_proof());
        assert_eq!(run.calls, 1);
        assert_eq!((run.proved, run.failed), (1, 0));
        assert!(matches!(&run.rows[0].1, VerificationResult::Proved { solver, .. }
            if solver.as_str() == "interval-disagreement-test"));
        assert!(run.eligibility[0].is_none(), "an interval result cannot mint an AY receipt");
    }
}

#[test]
fn interval_refutation_is_never_replaced_by_a_later_proof() {
    let mut vc = satisfiable_vc(VcKind::SliceBoundsCheck);
    let atom = Formula::Var("disagreement_guard".into(), Sort::Bool);
    vc.formula = Formula::And(vec![atom.clone(), Formula::Not(Box::new(atom))]);
    let model =
        Counterexample::new(vec![("interval_witness".into(), CounterexampleValue::Int(11))]);
    let run = run_with_interval(
        &vc,
        VerificationResult::Failed {
            solver: "interval-disagreement-test".into(),
            time_ms: 0,
            counterexample: Some(model.clone()),
        },
    );
    assert_eq!(run.calls, 1);
    assert_eq!((run.proved, run.failed), (0, 1));
    assert!(matches!(&run.rows[0].1,
        VerificationResult::Failed { solver, counterexample: Some(retained), .. }
        if solver.as_str() == "interval-disagreement-test" && *retained == model));
    assert!(run.eligibility[0].is_none());
}
