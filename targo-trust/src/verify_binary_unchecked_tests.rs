//! TRUST-02: `targo trust verify-binary` must not publish an unvalidated
//! solver `unsat` as `proved`.
//!
//! The command's only solver route (`binary_vc_router`) is the subprocess
//! `trust_router::IncrementalAYSession`. That session never sends
//! `:produce-proofs`, so every bare `unsat` it reads — on the incremental
//! push/pop lane and on its per-process fallback alike — becomes
//! `Proved { strength: ProofStrength::smt_unsat_unvalidated() }`
//! (`AssuranceLevel::Unchecked`: "solver said so, no independent validation").
//! `solver_result_fields` used to read that label as `proved`, so the per-VC
//! item, `solver_results`, `verification status` and the exit code all rested
//! on an unvalidated solver answer — on the push/pop lane where the ay
//! split-loop false `unsat` (fixed by ay bd8c45923) was measured. Every other
//! report chokepoint in the tree applies the named reporting floor
//! (`VerificationResult::require_reporting_floor`: trust-router's
//! `raw_result_to_outcome`, trust-report's `result_to_outcome`). These tests
//! pin that verify-binary applies it too, and that the raw solver answer is
//! still retained as dispatch EVIDENCE (status `Unsat`, the unmodified result),
//! which is what checked-certificate import binds to.

use std::path::Path;

use trust_router::{IncrementalAYSession, Router, VerificationBackend};
use trust_types::{
    AssuranceLevel, Formula, ProofStrength, SolverDispatchStatus, Sort, SourceSpan, VcKind,
    VerificationCondition, VerificationResult,
};

use super::{
    BinarySolverRoute, VerifiedBinaryFunctionSummary, VerifyBinaryReportInput,
    binary_solver_result_report, build_verify_binary_report,
    dispatch_binary_vcs_with_replay_evidence, render_verify_binary_terminal,
    verify_binary_should_fail,
};
use crate::types::{BinarySolverResultReport, BinaryVcKindCount, BinaryVerifyReport};
use crate::verify_binary_evidence::VerifyBinaryEvidence;

/// The exact value `trust_router::incremental_ay::proved_from_bare_unsat`
/// returns for a bare incremental `unsat` (that constructor is private to
/// trust-router; its own test `bare_incremental_unsat_is_unchecked` pins the
/// `Unchecked` stamp on the producer side).
fn bare_incremental_unsat() -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay-incremental".into(),
        time_ms: 4,
        strength: ProofStrength::smt_unsat_unvalidated(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn proved_with(strength: ProofStrength) -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay-in-process".into(),
        time_ms: 4,
        strength,
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// Stands in for the sole production backend: answers every VC exactly as a
/// bare incremental `unsat` does.
struct BareIncrementalUnsatBackend;

impl VerificationBackend for BareIncrementalUnsatBackend {
    fn name(&self) -> &str {
        "ay-incremental"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        bare_incremental_unsat()
    }
}

fn int_var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

/// A binary VC whose violation formula is UNSAT, so a correct solver answers
/// `unsat` for it.
fn unsat_binary_vc(upper: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "main".into(),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(upper))),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

/// The smallest lifted function the production dispatch accepts: one
/// returning block, no annotations (so no replay is attempted).
fn minimal_lifted_function() -> trust_lift::LiftedFunction {
    let mut cfg = trust_lift::cfg::Cfg::new();
    cfg.add_block(trust_lift::cfg::LiftedBlock {
        id: 0,
        start_addr: 0x401000,
        instructions: Vec::new(),
        successors: Vec::new(),
        is_return: true,
    });
    trust_lift::LiftedFunction {
        name: "main".into(),
        entry_point: 0x401000,
        cfg,
        trust_ir_body: trust_types::VerifiableBody {
            locals: Vec::new(),
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 0,
            return_ty: trust_types::Ty::unit_ty(),
            datatype_defs: Default::default(),
        },
        ssa: None,
        annotations: Vec::new(),
        memory_accesses: Vec::new(),
        trust_level: trust_types::TrustLevel::Partial,
        unsupported: trust_types::UnsupportedLedger::default(),
    }
}

fn report_for(
    vcs: usize,
    solver_results: Vec<BinarySolverResultReport>,
    proof_evidence: VerifyBinaryEvidence,
) -> BinaryVerifyReport {
    build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 0,
                vcs,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: vcs }],
            }],
            solver_results,
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    )
}

/// The per-VC chokepoint: a bare incremental `unsat` is reported `unknown`,
/// and the item says why.
#[test]
fn unchecked_incremental_unsat_item_is_unknown_not_proved() {
    let item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &bare_incremental_unsat(),
    );

    assert_eq!(item.solver, "ay-incremental");
    assert_eq!(
        item.status, "unknown",
        "an Unchecked (unvalidated) solver `unsat` is below the reporting floor and must not be \
         reported as proved: {item:?}"
    );
    let detail = item.detail.as_deref().expect("the downgraded item must carry its reason");
    assert!(
        detail.contains("Unchecked") && detail.contains("SmtBacked"),
        "the reason must name the assurance and the floor it fell below: {detail}"
    );
}

/// The verdict axis, through the PRODUCTION dispatch function
/// (`dispatch_binary_vcs_with_replay_evidence`, the one `verify-binary` runs):
/// no count, status, rendered line or exit code may say `proved`, while the
/// dispatch record keeps the raw solver answer as evidence.
#[test]
fn unchecked_unsat_cannot_make_the_verify_binary_verdict_proved() {
    let router = Router::with_backends(vec![Box::new(BareIncrementalUnsatBackend)]);
    let function = minimal_lifted_function();
    let vcs = [unsat_binary_vc(3), unsat_binary_vc(4)];

    let (reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        None,
        &function,
        None,
        &vcs,
    );

    assert_eq!(reports.len(), 2);
    assert_eq!(dispatch_records.len(), 2);
    for record in &dispatch_records {
        assert_eq!(
            record.status,
            SolverDispatchStatus::Unsat,
            "the dispatch record is evidence of what the solver answered and must stay raw"
        );
        assert_eq!(
            record.result.as_ref().and_then(VerificationResult::assurance),
            Some(AssuranceLevel::Unchecked),
            "the raw result must survive unmodified so a checked certificate can still bind it"
        );
    }

    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(vcs.len());
    evidence.extend_solver_dispatch(dispatch_records);
    let report = report_for(vcs.len(), reports, evidence);

    assert_eq!(report.solver_results.total, 2);
    assert_eq!(report.solver_results.proved, 0, "{:?}", report.solver_results);
    assert_eq!(report.solver_results.unknown, 2, "{:?}", report.solver_results);
    assert_eq!(report.solver_results.status, "unknown");
    assert_eq!(report.verification_status, "unknown");
    assert!(
        verify_binary_should_fail(&report),
        "verify-binary must not exit 0 on unvalidated solver answers"
    );

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("verification status: unknown\n"), "{rendered}");
    assert!(!rendered.contains("verification status: proved"), "{rendered}");
    assert!(rendered.contains("proved=0"), "{rendered}");
}

/// Control: the floor is the named reporting policy, not a blanket demotion. A
/// strict-checked (`SmtBacked`) or kernel-`Certified` `unsat` still reports
/// `proved`.
#[test]
fn validated_unsat_still_reports_proved() {
    for strength in
        [ProofStrength::smt_unsat_strict_checked(), ProofStrength::smt_unsat_certified()]
    {
        let item = binary_solver_result_report(
            "main",
            "division_by_zero".into(),
            Some("0x401010".into()),
            &proved_with(strength.clone()),
        );
        assert_eq!(item.status, "proved", "{strength:?}: {item:?}");
    }
}

/// The real producer, end to end: the subprocess session `binary_vc_router`
/// builds, over two VCs of one function that share a conjunct — so the batch
/// hoists the shared prefix to the base scope and decides each obligation as a
/// push/pop delta, the lane the ay split-loop defect lived on.
///
/// Drives the `ay` the real-solver tests resolve
/// (`trust_router::ay_discovery::detect_test_ay`: `TRUST_TEST_AY`, else the
/// `ay` in the Trust compiler under test's sysroot, never PATH); with none the test
/// fails, NOT RUN, rather than skipping.
#[test]
fn real_incremental_ay_unsat_is_unchecked_and_reported_unknown() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let ay = trust_router::ay_discovery::detect_test_ay(&checkout)
        .unwrap_or_else(|not_run| panic!("{not_run}"))
        .path;
    let session = IncrementalAYSession::with_solver_path(ay.to_string_lossy().into_owned());
    let router = Router::with_backends(vec![Box::new(session)]);
    let function = minimal_lifted_function();
    let vcs = [unsat_binary_vc(3), unsat_binary_vc(4)];

    let (reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        None,
        &function,
        None,
        &vcs,
    );

    assert_eq!(reports.len(), vcs.len(), "one report per VC: {reports:?}");
    assert_eq!(dispatch_records.len(), vcs.len(), "one dispatch record per VC");
    for (report, record) in reports.iter().zip(&dispatch_records) {
        let raw = record.result.as_ref().expect("dispatch keeps the raw result");
        assert!(
            matches!(raw, VerificationResult::Proved { .. }),
            "ay must decide `x > 5 /\\ x < k` (k <= 5) unsat: {raw:?}"
        );
        assert_eq!(
            raw.assurance(),
            Some(AssuranceLevel::Unchecked),
            "the incremental subprocess session requests no proof, so its `unsat` is Unchecked"
        );
        assert_eq!(record.status, SolverDispatchStatus::Unsat);
        assert_eq!(report.status, "unknown", "{report:?}");
    }
}
