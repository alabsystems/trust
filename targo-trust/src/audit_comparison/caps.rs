//! The complete historical L4 refusal-site policy. This is measurement policy,
//! never compiler authority. Keep its source census controls beside the reader.

pub(crate) const DELETED_CAPS: &[(&str, &[&str])] = &[
    (
        "C09d",
        &[
            "compiler/rustc_mir_transform/src/trust_verify.rs:FUNCTION_SOURCE_DIGEST_MEMO_BODIES_PER_PATH",
            "compiler/rustc_mir_transform/src/trust_verify.rs:FUNCTION_SOURCE_DIGEST_MEMO_BUDGET_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_RUN_RECORDS",
            "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_RUN_AGGREGATE_RECORDS",
            "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_RUN_DIAGNOSTICS",
            "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_JSON_ENVELOPE_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_COUNTEREXAMPLE_JSON_SCALAR_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_COUNTEREXAMPLE_JSON_NODES",
            "crates/trust-verifier-api/src/lib.rs:MAX_BUNDLE_METADATA_ENTRIES",
            "crates/trust-verifier-api/src/lib.rs:MAX_CONTRACT_PREDICATE_TEXT_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_SUMMARY_FACT_FIELD_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_CONTRACT_PREDICATE_JSON_NODES",
            "crates/trust-verifier-api/src/lib.rs:MAX_CONTRACT_PREDICATE_JSON_DEPTH",
            "crates/trust-verifier-api/src/lib.rs:MAX_CONTRACT_PREDICATE_JSON_SCALAR_BYTES",
        ],
    ),
    (
        "C11e1",
        &[
            "crates/trust-certify/src/clean_island/ensures_evidence.rs:MAX_CONTEXT_FIELD_BYTES",
            "crates/trust-certify/src/clean_island/ensures_evidence/typed.rs:MAX_CONTEXT_BYTES",
            "crates/trust-certify/src/clean_island/exact_admission.rs:MAX_DECLARATION_BYTES",
            "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_TERM_BYTES",
            "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_CLOSURE_BYTES",
            "crates/trust-certify/src/scalar_mir/capture.rs:MAX_SOURCE_PAYLOAD_BYTES",
            "crates/trust-certify/src/scalar_mir/capture.rs:MAX_BODY_PAYLOAD_BYTES",
            "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_TERM_BYTES",
            "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_SCALAR_FAMILY_BUNDLE_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION",
            "crates/trust-verifier-api/src/lib.rs:MAX_EVIDENCE_ARTIFACTS_PER_RUN_MANIFEST",
            "crates/trust-verifier-api/src/lib.rs:LIMIT",
        ],
    ),
    (
        "C11e2",
        &[
            "compiler/rustc_mir_transform/src/trust_verify.rs:MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES",
            "crates/trust-types/src/result.rs:NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES",
            "crates/trust-types/src/result.rs:NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS",
            "crates/trust-types/src/result.rs:MAX_TRANSPORT_EVIDENCE_ARTIFACTS",
            "crates/trust-types/src/result.rs:MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES",
            "crates/trust-types/src/result.rs:MAX_TRANSPORT_ARTIFACT_REFERENCES",
            "crates/trust-verifier-api/src/lib.rs:MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_EVIDENCE_ARTIFACT_REFERENCES",
            "crates/trust-certify/src/clean_island/ensures_evidence.rs:MAX_TERM_BYTES",
        ],
    ),
    (
        "C11e3",
        &[
            "targo-trust/src/report.rs:MAX_REPORT_ARTIFACT_STORE_BYTES",
            "targo-trust/src/report.rs:MAX_INLINE_REPORT_ARTIFACT_BYTES",
        ],
    ),
    (
        "C12",
        &[
            "compiler/rustc_mir_transform/src/trust_verify.rs:MAX_PLANNING_ROW_METADATA_ENTRIES",
            "compiler/rustc_mir_transform/src/trust_verify.rs:MAX_PLANNING_ROW_METADATA_BYTES",
            "compiler/rustc_mir_transform/src/trust_verify.rs:MAX_PLANNING_CONTEXT_BYTES",
            "crates/trust-mir-extract/src/verifier_api.rs:MAX_TRANSPORT_METADATA_VALUE_BYTES",
            "crates/trust-verifier-api/src/lib.rs:MAX_METADATA_VALUE_BYTES",
        ],
    ),
];

pub(crate) const MOVED_CAPS: &[(&str, &[&str])] =
    &[("C09d", &["compiler/rustc_mir_transform/src/trust_verify.rs:typed-chc-contract-decline"])];

pub(crate) const ANSWER_PRESERVING_CAPS: &[&str] = &[
    "compiler/rustc_mir_transform/src/trust_verify.rs:FUNCTION_SOURCE_DIGEST_MEMO_BODIES_PER_PATH",
    "compiler/rustc_mir_transform/src/trust_verify.rs:FUNCTION_SOURCE_DIGEST_MEMO_BUDGET_BYTES",
];

pub(crate) fn site_commit(site: &str) -> Option<&'static str> {
    DELETED_CAPS
        .iter()
        .chain(MOVED_CAPS)
        .find_map(|(group, sites)| sites.contains(&site).then_some(*group))
}

pub(super) fn moved(site: &str) -> bool {
    MOVED_CAPS.iter().any(|(_, sites)| sites.contains(&site))
}

pub(super) fn answer_preserving(site: &str) -> bool {
    ANSWER_PRESERVING_CAPS.contains(&site)
}
