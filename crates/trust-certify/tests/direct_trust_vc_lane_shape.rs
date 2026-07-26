// trust-certify: the direct TrustVC MIR-memory lane's obligation shape is
// kernel-certifiable, so the kernel — not the lane — decides that row.
//
// Why this test exists. `docs/TCB.md` records `DirectTrustVcLive` as `Trusted`:
// trust-vc's MIR-memory lane produces an Alethe certificate that trust-vc's own
// checkers accept and that no Clean-kernel reconstruction re-derives. What that
// row does NOT say, and what a reader would otherwise have to reconstruct from
// the mint ordering in `trust_verify.rs`, is that the kernel gets the first
// refusal: `certify_all` runs `trust_certify::certify_vc` over every Proved row
// and `build_result_proof_authorities` mints `KernelCertified` from it, while
// `install_direct_trust_vc_live_authorities` refuses any row that already
// carries an authority ("current row already carries a different private
// authority"). So a direct-TrustVC row reaches `Trusted` only when the kernel
// declined it first.
//
// That makes the kernel's coverage of this lane's obligation shape a load-bearing
// fact about what a green build means, and this test pins it. If `certify_vc`
// ever stops certifying the shape below, obligations that report `Certified`
// today would silently start reporting `Trusted` — a real loss of proof strength
// with no other test to catch it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, Symbol, VcKind, VerificationCondition};

fn span() -> SourceSpan {
    SourceSpan {
        file: "src/lib.rs".to_string(),
        line_start: 11,
        col_start: 9,
        line_end: 11,
        col_end: 20,
    }
}

/// The direct MIR-memory lane's release-admissible obligation shape: a
/// two-atom linear-integer window that closes on itself. trust-vc lowers the
/// negation of this into its proof unit and ay refutes it with the Farkas
/// (`la_generic`) certificate the lane carries; `bound` is the shared constant
/// both atoms compare against.
fn window_violation(lower: i128, upper: i128) -> Formula {
    Formula::And(vec![
        Formula::Lt(
            Box::new(Formula::Var("amount".to_string(), Sort::Int)),
            Box::new(Formula::Int(upper)),
        ),
        Formula::Ge(
            Box::new(Formula::Var("amount".to_string(), Sort::Int)),
            Box::new(Formula::Int(lower)),
        ),
    ])
}

fn ownership_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        // The only VcKinds that map to `ObligationKind::Ownership`, which is
        // what `DirectTrustVcLiveAuthority::authorizes_row` requires.
        kind: VcKind::AliasingViolation { mutable: true },
        function: Symbol::intern("demo::checked_transfer"),
        location: span(),
        formula,
        contract_metadata: None,
    }
}

#[test]
fn direct_trust_vc_release_admissible_shape_is_kernel_certified_before_the_lane_sees_it() {
    let vc = ownership_vc(window_violation(16, 16));
    assert!(
        trust_certify::certify_vc(&vc).is_some(),
        "the direct TrustVC lane's obligation shape must reach the kernel-certified tier; \
         losing it silently demotes those rows from Certified to Trusted",
    );
}

/// The control. One constant apart, the same shape is genuinely satisfiable
/// (`amount = 15`), so a certificate for it would be a false proof. This is what
/// makes the assertion above evidence of certification rather than of a
/// certifier that accepts its input.
#[test]
fn a_satisfiable_window_of_the_same_shape_is_declined() {
    let vc = ownership_vc(window_violation(15, 16));
    assert!(
        trust_certify::certify_vc(&vc).is_none(),
        "amount = 15 satisfies `amount < 16 && amount >= 15`; certifying it would be a false proof",
    );
}
