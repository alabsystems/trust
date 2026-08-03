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
fn trust_wp_follows_violation_polarity() {
    // The backend this gate was built for: it previously inverted the polarity
    // (Bool(true) => Proved), a vacuous false PROVED, now corrected.
    assert_polarity("trust_wp", &TrustWpRouterBackend::new());
}

#[test]
fn interval_follows_violation_polarity() {
    // Interval declines bare constants (no goal) -> Unknown, which satisfies the
    // invariant; this pins that it never inverts.
    assert_polarity("interval", &IntervalBackend);
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
