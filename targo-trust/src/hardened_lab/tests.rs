use super::claims::{CLAIMS, ClaimSpec};
use super::evaluate::{
    claim_failure_message, evaluate_claims, hardened_finding_label, standalone_binding_text,
};
use super::report::{ClaimResult, WalkthroughExecution};
use super::validate::expect_exact_transcript_keys;
use super::*;
use crate::source_analysis::{StandaloneOutcome, StandaloneVc, VcKind};

fn claim_spec(id: &str) -> &'static ClaimSpec {
    CLAIMS.iter().find(|claim| claim.id == id).expect("claim exists")
}

fn claim_result<'a>(results: &'a [ClaimResult], id: &str) -> &'a ClaimResult {
    results.iter().find(|claim| claim.id == id).expect("claim result exists")
}

fn standalone_hardened_vc(kind: VcKind, function: &str, description: &str) -> StandaloneVc {
    StandaloneVc {
        function: function.to_string(),
        file: std::path::PathBuf::from("examples/hardened/src/main.rs"),
        kind,
        description: description.to_string(),
        outcome: StandaloneOutcome::Failed,
    }
}

fn successful_walkthrough(bin: &str, stdout: &str) -> WalkthroughExecution {
    WalkthroughExecution {
        bin: bin.to_string(),
        source: format!("examples/hardened/src/bin/{bin}.rs"),
        command: format!("targo build --bin {bin} && target/debug/{bin}"),
        working_directory: "examples/hardened".to_string(),
        success: true,
        process_success: true,
        transcript_passed: true,
        status: "exit status: 0".to_string(),
        status_code: Some(0),
        stdout: stdout.to_string(),
        stderr: String::new(),
        transcript_errors: Vec::new(),
    }
}

fn failed_walkthrough(bin: &str) -> WalkthroughExecution {
    WalkthroughExecution {
        bin: bin.to_string(),
        source: format!("examples/hardened/src/bin/{bin}.rs"),
        command: format!("targo build --bin {bin}"),
        working_directory: "examples/hardened".to_string(),
        success: false,
        process_success: false,
        transcript_passed: false,
        status: "missing tracked walkthrough bin".to_string(),
        status_code: None,
        stdout: String::new(),
        stderr: String::new(),
        transcript_errors: vec![format!("required walkthrough bin `{bin}` is missing")],
    }
}

#[test]
fn claim_catalog_covers_distinct_hardened_categories() {
    let mut categories = CLAIMS.iter().map(|claim| claim.category).collect::<Vec<_>>();
    categories.sort();
    categories.dedup();
    assert_eq!(categories.len(), CLAIMS.len());
    assert!(categories.contains(&"raw_path_api"));
    assert!(categories.contains(&"unsafe_operation"));
    assert!(categories.contains(&"ffi_boundary"));
    assert!(categories.contains(&"trust_domain_order"));
    assert!(CLAIMS.iter().any(|claim| claim.category == "unsafe_operation"
        && claim.kind == VcKind::HardenedUnsafeOperation));
    assert!(
        CLAIMS
            .iter()
            .any(|claim| claim.category == "ffi_boundary"
                && claim.kind == VcKind::HardenedFfiBoundary)
    );
    assert!(CLAIMS.iter().all(|claim| !claim.walkthrough_evidence.is_empty()));

    let unsafe_claim = claim_spec("unsafe-operation");
    let ffi_claim = claim_spec("ffi-boundary");
    assert_eq!(unsafe_claim.report_label, "unsafe operation inventory");
    assert_eq!(ffi_claim.report_label, "extern FFI declaration inventory");
    assert_ne!(unsafe_claim.report_label, ffi_claim.report_label);
    assert_eq!(unsafe_claim.source_example, "unsafe_ffi_boundary");
    assert_eq!(ffi_claim.source_example, "main");
    assert_eq!(unsafe_claim.required_fragment, Some("trusted-wrapper"));
    assert_eq!(ffi_claim.required_fragment, Some("extern boundary"));
    assert_ne!(standalone_binding_text(unsafe_claim), standalone_binding_text(ffi_claim));
    assert!(
        claim_failure_message(unsafe_claim, false, false)
            .contains("extern FFI declaration evidence alone does not satisfy")
    );
    assert!(
        claim_failure_message(ffi_claim, false, false)
            .contains("unsafe block/trusted-wrapper evidence alone does not satisfy")
    );
}

#[test]
fn unsafe_and_ffi_claims_require_distinct_analyzer_and_walkthrough_evidence() {
    let unsafe_vc = standalone_hardened_vc(
        VcKind::HardenedUnsafeOperation,
        "unsafe_ffi_boundary",
        "unsafe block needs a trusted-wrapper contract and evidence before hardened code can rely on it",
    );
    let ffi_vc = standalone_hardened_vc(
        VcKind::HardenedFfiBoundary,
        "main",
        "extern boundary is inventory until ABI, memory, and trust evidence are attached",
    );
    let walkthrough = successful_walkthrough(
        "additional_walkthroughs",
        "walkthrough=unsafe_ffi_boundary_inventory\nunsafe_pointer_probe=ok\nunsafe_block_count=1\nwalkthrough=ffi_boundary_inventory\nffi_declared=getenv,strlen\nffi_called=getenv,strlen\nffi_call_count=2\n",
    );

    let unsafe_only =
        evaluate_claims(std::slice::from_ref(&unsafe_vc), std::slice::from_ref(&walkthrough));
    assert!(claim_result(&unsafe_only, "unsafe-operation").passed);
    let unsafe_only_ffi = claim_result(&unsafe_only, "ffi-boundary");
    assert!(!unsafe_only_ffi.passed);
    assert!(
        unsafe_only_ffi
            .failure_message
            .as_deref()
            .is_some_and(|message| message.contains("extern FFI declaration evidence"))
    );

    let ffi_only =
        evaluate_claims(std::slice::from_ref(&ffi_vc), std::slice::from_ref(&walkthrough));
    assert!(claim_result(&ffi_only, "ffi-boundary").passed);
    let ffi_only_unsafe = claim_result(&ffi_only, "unsafe-operation");
    assert!(!ffi_only_unsafe.passed);
    assert!(
        ffi_only_unsafe
            .failure_message
            .as_deref()
            .is_some_and(|message| message.contains("unsafe-operation inventory evidence"))
    );

    let both = evaluate_claims(&[unsafe_vc, ffi_vc], std::slice::from_ref(&walkthrough));
    assert!(claim_result(&both, "unsafe-operation").passed);
    assert!(claim_result(&both, "ffi-boundary").passed);
    assert!(claim_result(&both, "unsafe-operation").failure_message.is_none());
    assert!(claim_result(&both, "ffi-boundary").failure_message.is_none());
}

#[test]
fn hardened_unsafe_and_ffi_findings_get_report_labels() {
    assert_eq!(hardened_finding_label(VcKind::HardenedUnsafeOperation), Some("unsafe_operation"));
    assert_eq!(hardened_finding_label(VcKind::HardenedFfiBoundary), Some("ffi_boundary"));
    assert_eq!(hardened_finding_label(VcKind::HardenedPanic), None);
}

#[test]
fn analyzer_match_without_walkthrough_evidence_fails_closed() {
    let unsafe_vc = standalone_hardened_vc(
        VcKind::HardenedUnsafeOperation,
        "unsafe_ffi_boundary",
        "unsafe block needs a trusted-wrapper contract and evidence before hardened code can rely on it",
    );

    let missing = evaluate_claims(std::slice::from_ref(&unsafe_vc), &[]);
    let unsafe_claim = claim_result(&missing, "unsafe-operation");
    assert!(!unsafe_claim.passed);
    assert!(
        unsafe_claim
            .failure_message
            .as_deref()
            .is_some_and(|message| message.contains("runnable walkthrough transcript evidence"))
    );

    let failed = failed_walkthrough("additional_walkthroughs");
    let failed_result = evaluate_claims(&[unsafe_vc], std::slice::from_ref(&failed));
    let failed_claim = claim_result(&failed_result, "unsafe-operation");
    assert!(!failed_claim.passed);
    assert!(failed_claim.walkthrough_evidence.iter().any(|evidence| {
        evidence.bin == "additional_walkthroughs"
            && !evidence.passed
            && evidence
                .failure_message
                .as_deref()
                .is_some_and(|message| message.contains("did not pass"))
    }));
}

#[test]
fn walkthrough_success_without_required_transcript_fails_claim() {
    let ffi_vc = standalone_hardened_vc(
        VcKind::HardenedFfiBoundary,
        "main",
        "extern boundary is inventory until ABI, memory, and trust evidence are attached",
    );
    let walkthrough = successful_walkthrough(
        "additional_walkthroughs",
        "walkthrough=ffi_boundary_inventory\nffi_declared=getenv,strlen\n",
    );

    let results = evaluate_claims(&[ffi_vc], std::slice::from_ref(&walkthrough));
    let ffi_claim = claim_result(&results, "ffi-boundary");
    assert!(!ffi_claim.passed);
    assert!(ffi_claim.walkthrough_evidence.iter().any(|evidence| {
        evidence.bin == "additional_walkthroughs"
            && !evidence.passed
            && evidence
                .failure_message
                .as_deref()
                .is_some_and(|message| message.contains("ffi_called=getenv,strlen"))
    }));
}

#[test]
fn claim_transcript_requirements_are_scoped_to_named_walkthrough() {
    let ffi_vc = standalone_hardened_vc(
        VcKind::HardenedFfiBoundary,
        "main",
        "extern boundary is inventory until ABI, memory, and trust evidence are attached",
    );
    let walkthrough = successful_walkthrough(
        "additional_walkthroughs",
        concat!(
            "walkthrough=unrelated\n",
            "ffi_called=getenv,strlen\n",
            "walkthrough=ffi_boundary_inventory\n",
            "ffi_declared=getenv,strlen\n",
            "ffi_call_count=2\n",
        ),
    );

    let results = evaluate_claims(&[ffi_vc], std::slice::from_ref(&walkthrough));
    let ffi_claim = claim_result(&results, "ffi-boundary");
    assert!(!ffi_claim.passed);
    assert!(ffi_claim.walkthrough_evidence.iter().any(|evidence| {
        evidence.bin == "additional_walkthroughs"
            && !evidence.passed
            && evidence
                .failure_message
                .as_deref()
                .is_some_and(|message| message.contains("ffi_called=getenv,strlen"))
    }));
}

#[test]
fn parse_json_alias() {
    let args = vec!["--json".to_string(), "--show-vcs".to_string()];
    let parsed = parse_args(&args).expect("parse").expect("run args");
    assert_eq!(parsed.format, OutputFormat::Json);
    assert!(parsed.show_vcs);
}

#[test]
fn exact_transcript_keys_accept_valid_inventory() {
    let mut errors = Vec::new();
    expect_exact_transcript_keys(
        "walkthrough=demo\nresult=ok\n",
        &["walkthrough", "result"],
        &mut errors,
    );
    assert!(errors.is_empty(), "valid exact transcript should pass: {errors:?}");
}

#[test]
fn exact_transcript_keys_reject_swapped_inventory() {
    let mut errors = Vec::new();
    expect_exact_transcript_keys(
        "result=ok\nwalkthrough=demo\n",
        &["walkthrough", "result"],
        &mut errors,
    );
    assert!(
        errors.iter().any(|error| error.contains("key order/inventory")),
        "swapped keys should fail exactly: {errors:?}"
    );
}

#[test]
fn exact_transcript_keys_reject_missing_required_key() {
    let mut errors = Vec::new();
    expect_exact_transcript_keys("walkthrough=demo\n", &["walkthrough", "result"], &mut errors);
    assert!(
        errors.iter().any(|error| error.contains("key order/inventory")),
        "missing required key should fail exactly: {errors:?}"
    );
}

#[test]
fn exact_transcript_keys_reject_extra_known_wrong_branch_key() {
    let mut errors = Vec::new();
    expect_exact_transcript_keys(
        "walkthrough=demo\nunsupported=non-unix\nresult=ok\n",
        &["walkthrough", "result"],
        &mut errors,
    );
    assert!(
        errors.iter().any(|error| error.contains("key order/inventory")),
        "extra branch key should fail exactly: {errors:?}"
    );
}
