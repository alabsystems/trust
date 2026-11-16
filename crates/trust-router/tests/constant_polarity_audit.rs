// Cross-backend constant-polarity audit harness.
//
// `vc.formula` is the VIOLATION condition (vc.rs: UNSAT => property holds). The
// canonical convention every backend MUST follow (constant_folder.rs:109-116):
//   Bool(false) violation  => UNSAT => property holds  => Proved (never Failed)
//   Bool(true)  violation  => always violated          => Failed (never Proved)
// A backend that does not handle constants may DECLINE (Unknown) — that is fine;
// what must NEVER happen is the INVERSION (Bool(true) => Proved, the vacuous
// false-PROVED; or Bool(false) => Failed, a false refutation). This harness pins
// that invariant across every constant-deciding backend so a future polarity
// regression (like the trust-wp one this gate was built for) fails the build.
use trust_router::VerificationBackend;
use trust_router::constant_folder::ConstantFolderBackend;
use trust_router::interval_backend::IntervalBackend;
use trust_types::*;

fn const_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "audit".to_string().into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Run the convention check on one backend: a `Bool(false)` violation must never
/// be `Failed`, and a `Bool(true)` violation must never be `Proved`.
fn assert_polarity(name: &str, b: &dyn VerificationBackend) {
    let r_false = b.verify(&const_vc(Formula::Bool(false)));
    assert!(
        !matches!(r_false, VerificationResult::Failed { .. }),
        "{name}: Bool(false) violation (UNSAT => property holds) must NOT be Failed; got {r_false:?}"
    );
    let r_true = b.verify(&const_vc(Formula::Bool(true)));
    assert!(
        !matches!(r_true, VerificationResult::Proved { .. }),
        "{name}: Bool(true) violation (always violated) must NEVER be Proved (vacuous false PROVED); got {r_true:?}"
    );
}

#[test]
fn constant_folder_follows_violation_polarity() {
    assert_polarity("constant_folder", &ConstantFolderBackend);
}

#[test]
fn interval_follows_violation_polarity() {
    // Interval declines bare constants (no goal) -> Unknown, which satisfies the
    // invariant; this pins that it never inverts.
    assert_polarity("interval", &IntervalBackend);
}

#[test]
fn shared_constant_folder_covers_contract_and_contractless_literals() {
    for contract_metadata in
        [None, Some(ContractMetadata { has_ensures: true, ..ContractMetadata::default() })]
    {
        let vc = |formula| VerificationCondition {
            contract_metadata: contract_metadata.clone(),
            ..const_vc(formula)
        };
        let result = ConstantFolderBackend.verify(&vc(Formula::Bool(false)));
        assert!(matches!(result, VerificationResult::Proved { strength, .. }
            if strength == ProofStrength::smt_unsat()));
        assert!(matches!(
            ConstantFolderBackend.verify(&vc(Formula::Bool(true))),
            VerificationResult::Failed { .. }
        ));
    }
}

#[test]
fn bare_symbolic_contracts_are_not_wp_proofs() {
    let mut vc = const_vc(Formula::Not(Box::new(Formula::Var("ok".into(), Sort::Bool))));
    vc.contract_metadata =
        Some(ContractMetadata { has_ensures: true, ..ContractMetadata::default() });
    assert!(matches!(ConstantFolderBackend.verify(&vc), VerificationResult::Unknown { .. }));
}

#[test]
fn canonical_formula_route_keeps_every_input_and_refuses_unmodeled_rows() {
    let router = trust_router::Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
    let mut unsupported = const_vc(Formula::Bool(false));
    unsupported.kind =
        VcKind::UnsupportedMir { kind: "opaque".into(), detail: "no operational model".into() };
    let inputs = vec![
        const_vc(Formula::Bool(false)),
        const_vc(Formula::Bool(true)),
        const_vc(Formula::Var("not_proved".into(), Sort::Bool)),
        unsupported,
    ];
    let rows = router.verify_all(&inputs);
    assert_eq!(rows.len(), inputs.len());
    assert!(matches!(&rows[0].1, VerificationResult::Proved { strength, .. }
        if *strength == ProofStrength::smt_unsat()));
    assert!(matches!(&rows[1].1, VerificationResult::Failed { .. }));
    assert!(matches!(&rows[2].1, VerificationResult::Unknown { .. }));
    assert!(matches!(&rows[3].1, VerificationResult::Unknown { .. }));
}

#[test]
fn mixed_portfolio_reaches_constant_fallback_and_keeps_expired_budget_refusal() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct InconclusiveSmt(Arc<AtomicUsize>);
    impl VerificationBackend for InconclusiveSmt {
        fn name(&self) -> &str {
            "inconclusive-smt"
        }
        fn role(&self) -> trust_router::BackendRole {
            trust_router::BackendRole::SmtSolver
        }
        fn can_handle(&self, _: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _: &VerificationCondition) -> VerificationResult {
            self.0.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Timeout { solver: self.name().into(), timeout_ms: 1 }
        }
    }
    let calls = Arc::new(AtomicUsize::new(0));
    let router = trust_router::Router::with_backends(vec![
        Box::new(InconclusiveSmt(calls.clone())),
        Box::new(ConstantFolderBackend),
    ]);
    let inputs = [const_vc(Formula::Bool(false)), const_vc(Formula::Bool(true))];
    let rows = router.verify_all(&inputs);
    assert_eq!(calls.load(Ordering::SeqCst), 2, "SMT ranks before the General fallback");
    assert!(matches!(&rows[0].1, VerificationResult::Proved { strength, .. }
        if *strength == ProofStrength::smt_unsat()));
    assert!(matches!(&rows[1].1, VerificationResult::Failed { .. }));

    calls.store(0, Ordering::SeqCst);
    let rows = router.verify_all_with_deadline(&inputs, Some(std::time::Instant::now()));
    assert_eq!(rows.len(), inputs.len());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(rows.iter().all(|(_, row)| matches!(row, VerificationResult::Unknown { .. })));
}

#[test]
fn constant_folder_is_the_reference_convention() {
    // The explicit reference both directions must match.
    let proved = ConstantFolderBackend.verify(&const_vc(Formula::Bool(false)));
    assert!(
        matches!(proved, VerificationResult::Proved { .. }),
        "Bool(false) violation must be Proved (the reference); got {proved:?}"
    );
    let failed = ConstantFolderBackend.verify(&const_vc(Formula::Bool(true)));
    assert!(
        matches!(failed, VerificationResult::Failed { .. }),
        "Bool(true) violation must be Failed (the reference); got {failed:?}"
    );
}

#[test]
fn compiler_and_cegis_cannot_reintroduce_formula_only_wp_requests() {
    // This source-bound architecture check guards the retired constructor and
    // registration. Native body-WP's semantic/refusal tests remain separate.
    let compiler = include_str!("../../../compiler/rustc_mir_transform/src/trust_verify.rs");
    let router = include_str!("../src/lib.rs");
    let native_body = include_str!("../src/full_verification/engines/native_trust_wp.rs");
    let strengthen_oracle = include_str!("../../trust-strengthen/src/trust_wp_oracle.rs");
    assert!(compiler.contains("constant_folder::ConstantFolderBackend"));
    for removed in
        ["trust_wp_backend", "TrustWpRouterBackend", "verify_vc_via_native_trust_wp_engine"]
    {
        assert!(!compiler.contains(removed), "compiler retains {removed}");
        assert!(!router.contains(removed), "router exports {removed}");
    }
    assert!(
        !std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/trust_wp_backend.rs").exists()
    );
    assert!(native_body.contains("verify_trust_ir_body_contracts"));
    assert!(native_body.contains("replay_trust_ir_body_contracts"));
    assert!(!strengthen_oracle.contains("use trust_wp"));
    for (name, source) in [
        ("compiler", compiler),
        ("native_body", native_body),
        ("trust_wp_oracle", strengthen_oracle),
    ] {
        for forbidden in ["CliBackend::", "verify_with_contracts(", "TrustWpConfig::"] {
            assert!(
                !source.contains(forbidden),
                "{name} must not reach the parsed trust_wp subprocess lane (found `{forbidden}`)"
            );
        }
    }
    assert!(strengthen_oracle.contains("owns no dischargeable obligation kind"));
}
