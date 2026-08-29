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
use trust_router::trust_wp_backend::TrustWpRouterBackend;
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
fn trust_wp_follows_violation_polarity() {
    // The native-backed R4 backend declines contract-less VCs -> Unknown, which
    // satisfies the invariant; this pins that it never inverts (the historical
    // trust-wp inversion is what this gate was built for).
    assert_polarity("trust_wp", &TrustWpRouterBackend::new());
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
fn compiler_and_cegis_do_not_register_parsed_trust_wp_subprocess_authority() {
    // The seal, post-R4-flip: the per-VC backend the compiler registers is
    // NATIVE-BACKED (typed in-process engine). No compiler-reachable path may
    // import the subprocess `CliBackend`, the `verify_with_contracts` text
    // wrapper, or the `TrustWpConfig` that would select a solver path — a
    // compiler verdict must never be minted from parsed subprocess text.
    // (`tests/trust_wp_native_flip_ab.rs` pins TRUST_WP_PATH invariance at
    // runtime; the TrustWP full-verification adapter separately advertises
    // ZERO obligation kinds, so historical records grant no authority.)
    let backend_module = include_str!("../src/trust_wp_backend.rs");
    let strengthen_oracle = include_str!("../../trust-strengthen/src/trust_wp_oracle.rs");

    // The backend's ONLY trust_wp import is the typed in-process engine.
    assert_eq!(backend_module.matches("use trust_wp::").count(), 1);
    assert!(backend_module.contains("use trust_wp::TrustWpVerificationEngine;"));
    // The CEGIS oracle imports no trust_wp surface at all.
    assert!(!strengthen_oracle.contains("use trust_wp"));
    // No fully-qualified reach into the subprocess lane either (the doc
    // comments name these identifiers in backticks only, never callable).
    for (name, source) in
        [("trust_wp_backend", backend_module), ("trust_wp_oracle", strengthen_oracle)]
    {
        for forbidden in ["CliBackend::", "verify_with_contracts(", "TrustWpConfig::"] {
            assert!(
                !source.contains(forbidden),
                "{name} must not reach the parsed trust_wp subprocess lane (found `{forbidden}`)"
            );
        }
    }
    assert!(strengthen_oracle.contains("owns no dischargeable obligation kind"));
}
