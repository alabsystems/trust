use rustc_index::IndexVec;
use rustc_middle::mir::trust_proof::{
    ObligationId, TrustDisposition, TrustFunctionSummary, TrustObligationKind, TrustProofResults,
    TrustProofStrength, TrustProofTelemetry, TrustStatus,
};
use trust_types::{Formula, Symbol};

use super::*;

/// The forbidden full-verifier classifier substrings (targo
/// `is_full_verifier_text`); no field of an assumption row may contain one.
const FULL_VERIFIER_MARKERS: &[&str] = &[
    "native full verifier",
    "full verifier",
    "full-verifier",
    "trust-verify-full",
    "fullverification::",
];

fn vc(function: &str, kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: Symbol::intern(function),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

fn unknown() -> VerificationResult {
    VerificationResult::Unknown {
        solver: Symbol::intern("test"),
        time_ms: 0,
        reason: "unproved".to_string(),
    }
}

fn recursion_row(function: &str) -> (VerificationCondition, VerificationResult) {
    (
        vc(
            function,
            VcKind::NonTermination {
                context: trust_vcgen::RECURSION_TERMINATION_CONTEXT.to_string(),
                measure: "n".to_string(),
            },
        ),
        unknown(),
    )
}

fn own() -> [String; 2] {
    ["f".to_string(), "c::f".to_string()]
}

/// One direct-self-call charge row for `func_path`, among `calls` call sites.
fn call_row(func_path: &str, calls: usize) -> TransportObligationResult {
    termination_unmeasured_row(
        None,
        func_path,
        SiteKind::Call,
        SiteCounts { calls, references: 0, dispatches: 0 },
    )
}

fn charge(sites: usize) -> TerminationUnmeasuredCharge {
    TerminationUnmeasuredCharge {
        rows: (0..sites).map(|_| call_row("c::f", sites)).collect(),
        calls: vec![rustc_span::DUMMY_SP; sites],
        references: Vec::new(),
        dispatches: Vec::new(),
    }
}

#[test]
fn a_recursion_row_of_this_function_is_a_statement() {
    // Stamped with the item name (vcgen) or the def path (compiler).
    assert!(vcgen_made_a_recursion_statement(&[recursion_row("f")], &own()));
    assert!(vcgen_made_a_recursion_statement(&[recursion_row("c::f")], &own()));
    // The recursion-SCC lane's unmeasured row (`Bool(true)`) is one too: it is
    // a visible, fatal `[termination]` row.
    let scc = recursion_row("f");
    assert_eq!(scc.0.formula, Formula::Bool(true));
    assert!(vcgen_made_a_recursion_statement(&[scc], &own()));
}

#[test]
fn the_recursion_decreases_marker_is_a_statement() {
    let marker = (
        vc(
            "f",
            VcKind::UnsupportedMir {
                kind: trust_vcgen::RECURSION_DECREASES_UNSUPPORTED_KIND.to_string(),
                detail: "cannot classify non-self call".to_string(),
            },
        ),
        unknown(),
    );
    assert!(vcgen_made_a_recursion_statement(&[marker], &own()));
}

#[test]
fn silence_loop_rows_and_other_functions_rows_are_not_a_statement() {
    assert!(!vcgen_made_a_recursion_statement(&[], &own()));
    let loop_row = (
        vc("f", VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() }),
        unknown(),
    );
    assert!(!vcgen_made_a_recursion_statement(&[loop_row], &own()));
    // Critique H7: a CALLEE's recursion row does not speak for this body.
    assert!(!vcgen_made_a_recursion_statement(&[recursion_row("g")], &own()));
    assert!(!vcgen_made_a_recursion_statement(&[recursion_row("c::g")], &own()));
    // An unrelated unsupported row is not the recursion marker.
    let other = (
        vc(
            "f",
            VcKind::UnsupportedMir {
                kind: "FullVerification::trust.contract::unsupported".to_string(),
                detail: String::new(),
            },
        ),
        unknown(),
    );
    assert!(!vcgen_made_a_recursion_statement(&[other], &own()));
}

#[test]
fn the_level_gate_follows_the_recorded_filter_level() {
    assert!(!termination_claims_in_scope(None));
    assert!(!termination_claims_in_scope(Some(ProofLevel::L0Safety)));
    assert!(termination_claims_in_scope(Some(ProofLevel::L1Functional)));
    assert!(termination_claims_in_scope(Some(ProofLevel::L2Domain)));
}

#[test]
fn the_charge_row_has_the_assumption_shape_and_no_marker_text() {
    let row = call_row("c::f", 2);
    assert_eq!(row.kind, "assumption:termination-unmeasured");
    assert_eq!(row.outcome, Outcome::Skipped);
    assert_eq!(row.solver, TERMINATION_UNMEASURED_ROW_SOLVER);
    assert!(row.typed_kind.is_none());
    assert!(row.native_trust_ir.is_none() && row.proof_evidence.is_none());
    assert!(!row.design_mandate);
    assert!(row.description.starts_with("unverified assumption: termination of `c::f`"));
    let reason = row.reason.clone().expect("the charge carries its reason");
    assert!(reason.contains("2 self call(s) bind no `decreases` measure"));
    // H4: the reason must not claim the function's other rows verified.
    assert!(!reason.contains("reported as verified"));
    for text in [&row.kind, &row.description, &reason, &row.solver] {
        let lower = text.to_ascii_lowercase();
        for marker in FULL_VERIFIER_MARKERS {
            assert!(!lower.contains(marker), "`{text}` contains `{marker}`");
        }
    }
    assert!(transport_row_is_termination_unmeasured_assumption(&row));
    assert!(trust_types::assumption::strict_policy_publishes_assumption_row(
        &row.kind,
        &row.solver,
        &row.description,
    ));
}

/// Review F5: a self REFERENCE row has the same admitted shape as a call row
/// (the gates read kind + solver, never the text), its own detail, and a
/// reason that counts both kinds. With no reference the summary is exactly
/// the pre-F5 wording, so the call-only diagnostics are unchanged.
#[test]
fn a_reference_row_has_the_same_shape_and_says_what_it_charges() {
    let row = termination_unmeasured_row(
        None,
        "c::f",
        SiteKind::Reference,
        SiteCounts { calls: 1, references: 1, dispatches: 0 },
    );
    assert_eq!(row.kind, "assumption:termination-unmeasured");
    assert_eq!(row.outcome, Outcome::Skipped);
    assert!(transport_row_is_termination_unmeasured_assumption(&row));
    assert!(trust_types::assumption::strict_policy_publishes_assumption_row(
        &row.kind,
        &row.solver,
        &row.description,
    ));
    assert!(row.description.starts_with("unverified assumption: termination of `c::f`"));
    assert!(row.description.contains("takes the function as a value"));
    let reason = row.reason.clone().expect("the charge carries its reason");
    assert!(reason.contains("1 self call(s) bind no `decreases` measure, and 1 self reference(s)"));
    for text in [&row.kind, &row.description, &reason, &row.solver] {
        let lower = text.to_ascii_lowercase();
        for marker in FULL_VERIFIER_MARKERS {
            assert!(!lower.contains(marker), "`{text}` contains `{marker}`");
        }
    }

    assert_eq!(
        sites_summary(SiteCounts { calls: 2, references: 0, dispatches: 0 }),
        "2 self call(s) bind no `decreases` measure"
    );
    assert_eq!(
        sites_summary(SiteCounts { calls: 0, references: 1, dispatches: 0 }),
        "1 self reference(s) take this function as a value, which may re-enter it with no \
         `decreases` measure"
    );
    assert_eq!(
        sites_summary(SiteCounts { calls: 1, references: 2, dispatches: 0 }),
        "1 self call(s) bind no `decreases` measure, and 2 self reference(s) take this \
         function as a value, which may re-enter it"
    );
}

/// ARGS-FINGERPRINT-READ-1 round 6: a DISPATCH row (a call leaving the body
/// through trait dispatch and coming back through another body) has the same
/// admitted shape as a call row, its own detail, and a summary clause appended
/// after the earlier wording (which is unchanged when there is no dispatch site).
#[test]
fn a_dispatch_row_has_the_same_shape_and_says_what_it_charges() {
    let row = termination_unmeasured_row(
        None,
        "c::f",
        SiteKind::Dispatch,
        SiteCounts { calls: 0, references: 0, dispatches: 1 },
    );
    assert_eq!(row.kind, "assumption:termination-unmeasured");
    assert_eq!(row.outcome, Outcome::Skipped);
    assert!(transport_row_is_termination_unmeasured_assumption(&row));
    assert!(trust_types::assumption::strict_policy_publishes_assumption_row(
        &row.kind,
        &row.solver,
        &row.description,
    ));
    assert!(row.description.contains("dispatches through a trait method"));
    let reason = row.reason.clone().expect("the charge carries its reason");
    assert!(reason.contains("1 dispatched call(s) reach a trait method"));
    for text in [&row.kind, &row.description, &reason, &row.solver] {
        let lower = text.to_ascii_lowercase();
        for marker in FULL_VERIFIER_MARKERS {
            assert!(!lower.contains(marker), "`{text}` contains `{marker}`");
        }
    }
    assert_eq!(
        sites_summary(SiteCounts { calls: 0, references: 0, dispatches: 2 }),
        "2 dispatched call(s) reach a trait method whose local implementation calls back into \
         this function, with no `decreases` measure"
    );
    assert_eq!(
        sites_summary(SiteCounts { calls: 1, references: 0, dispatches: 1 }),
        "1 self call(s) bind no `decreases` measure; 1 dispatched call(s) reach a trait method \
         whose local implementation calls back into this function"
    );
}

#[test]
fn a_charge_row_in_any_other_shape_is_not_admitted() {
    let row = call_row("c::f", 1);
    let mut proved = row.clone();
    proved.outcome = Outcome::Proved;
    let mut classifier = row.clone();
    classifier.solver = "trust-classifier".to_string();
    let mut typed = row.clone();
    typed.typed_kind = Some(Box::new(VcKind::NonTermination {
        context: "recursion".to_string(),
        measure: "n".to_string(),
    }));
    let mut mandate = row;
    mandate.design_mandate = true;
    for forged in [proved, classifier, typed, mandate] {
        assert!(!transport_row_is_termination_unmeasured_assumption(&forged), "{forged:?}");
    }
}

#[test]
fn the_seam_strips_stale_rows_and_appends_one_row_per_site() {
    let base = vec![super::super::transport_no_obligations_row()];
    assert!(rows_with_termination_unmeasured(&base, None).is_none());

    let stale = call_row("c::stale", 1);
    let with_stale = vec![base[0].clone(), stale];
    let stripped = rows_with_termination_unmeasured(&with_stale, None).expect("stripped");
    assert_eq!(stripped, base);

    let charged =
        rows_with_termination_unmeasured(&with_stale, Some(&charge(2))).expect("charged rows");
    assert_eq!(charged.len(), 3);
    assert_eq!(charged[0], base[0]);
    assert!(charged[1..].iter().all(transport_row_is_termination_unmeasured_assumption));
    assert!(charged[1..].iter().all(|row| row.description.contains("`c::f`")));
}

/// A body with zero data obligations and a clean (absent) native run: the
/// shape `memory_safe_zero_data_obligations_still_rejects_coroutine_protocol_premise`
/// uses, with the D9 field recorded at L1.
fn zero_obligation_artifacts() -> VerificationArtifacts {
    let dispositions: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    VerificationArtifacts {
        proof_results: TrustProofResults {
            dispositions,
            fingerprints: IndexVec::new(),
            summary,
            premises: Vec::new(),
        },
        telemetry: TrustProofTelemetry { details: IndexVec::new() },
        results: super::super::RowResults::default(),
        transport_results: Vec::new(),
        full_verification: None,
        result_bindings: Vec::new(),
        proof_authorities: Vec::new(),
        overflow_check_origins: super::super::OverflowCheckOrigins::default(),
        coroutine_resume_contract: None,
        max_proof_level: Some(ProofLevel::L1Functional),
        expanded_function_identity: None,
        runtime_checked_std_members: Vec::new(),
        calculus_reporting: None,
        ctx: std::sync::Arc::new(trust_types::vc_context::VcContext::new()),
    }
}

/// Critique H1: memory-safe admits the charge in its exact shape (it built rc 0
/// there before D9), refuses a row that merely claims the kind, and the charge
/// never whitewashes a real gap beside it.
#[test]
fn memory_safe_admits_the_charge_and_nothing_that_merely_claims_its_kind() {
    let artifacts = zero_obligation_artifacts();
    let charged = call_row("c::f", 1);
    assert!(!super::super::memory_safe_artifacts_have_non_demotable_failure(
        &artifacts,
        &[charged.clone()],
    ));

    let mut forged = charged.clone();
    forged.solver = "trust-classifier".to_string();
    assert!(super::super::memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[forged],));

    let gap = super::super::transport_native_verification_gap_row();
    assert!(super::super::memory_safe_artifacts_have_non_demotable_failure(
        &artifacts,
        &[gap, charged],
    ));
}

/// Review F2: a body that GENERATED obligations (summary total > 0) but whose
/// effective rows speak for none of them stays fail-closed under memory-safe
/// when the only rows are D9 charge rows — exactly as it was for an empty row
/// set before the charge existed. A real row beside the charge still decides.
#[test]
fn memory_safe_charge_rows_alone_do_not_stand_in_for_generated_obligations() {
    let mut dispositions: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    dispositions.push(TrustDisposition {
        kind: TrustObligationKind::Assertion,
        status: TrustStatus::Trusted,
        strength: TrustProofStrength::None,
        certified: false,
    });
    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    assert_eq!(summary.total, 1);
    let mut artifacts = zero_obligation_artifacts();
    artifacts.proof_results = TrustProofResults {
        dispositions,
        fingerprints: IndexVec::new(),
        summary,
        premises: Vec::new(),
    };

    // Pre-D9 behaviour: no row at all is fatal.
    assert!(super::super::memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[]));
    // The charge alone must not stand in for the missing rows.
    let charged = call_row("c::f", 1);
    assert!(super::super::memory_safe_artifacts_have_non_demotable_failure(
        &artifacts,
        &[charged.clone()],
    ));
    assert!(super::super::memory_safe_artifacts_have_non_demotable_failure(
        &artifacts,
        &[charged.clone(), call_row("c::f", 2)],
    ));
    // A proved row beside the charge is a row that speaks: admitted.
    let proved = super::super::transport_no_obligations_row();
    assert_eq!(proved.outcome, Outcome::Proved);
    assert!(!super::super::memory_safe_artifacts_have_non_demotable_failure(
        &artifacts,
        &[proved, charged],
    ));
}

/// Critique H3: the zero-obligation branch keeps what it published before D9
/// and APPENDS the charge; in particular the honest gap row survives.
#[test]
fn the_zero_obligation_branch_appends_the_charge_to_its_own_rows() {
    let gap = super::super::transport_native_verification_gap_row();
    let clean = super::super::transport_no_obligations_row();
    let transport = vec![call_row("c::stale", 1), gap.clone()];

    // Uncharged: byte-identical to the three pre-D9 outcomes.
    assert_eq!(zero_obligation_rows(true, &[], None), vec![clean.clone()]);
    assert_eq!(zero_obligation_rows(false, &[], None), vec![gap.clone()]);
    assert_eq!(zero_obligation_rows(false, &[gap.clone()], None), vec![gap.clone()]);

    // Charged: the base row is kept and the charge follows it.
    let rows = zero_obligation_rows(false, &[], Some(&charge(1)));
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0], gap, "the Unknown gap row must not be dropped");
    assert!(transport_row_is_termination_unmeasured_assumption(&rows[1]));

    let rows = zero_obligation_rows(true, &[], Some(&charge(1)));
    assert_eq!(rows[0], clean);
    assert_eq!(rows.len(), 2);

    // A stale charge row among the transport rows is replaced, not doubled.
    let rows = zero_obligation_rows(false, &transport, Some(&charge(1)));
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0], gap);
    assert!(rows[1].description.contains("`c::f`"));
}
