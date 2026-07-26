//! Static catalogs of product-proof requirements (evidence classes and components).
//!
//! Extracted from `product_proof.rs` to keep that file focused on validation
//! logic; this module holds only the data tables that describe the full
//! product-proof matrix.

use super::types::{
    PRODUCT_COMPONENT_TARGO, PRODUCT_COMPONENT_TARGO_TRUST, PRODUCT_COMPONENT_TRUSTC,
    ProductProofComponent, ProductProofEvidenceClass,
};

pub(super) fn product_proof_evidence_class_requirements() -> Vec<ProductProofEvidenceClass> {
    vec![
        ProductProofEvidenceClass {
            class: "no-verification compatibility",
            status: "missing_evidence".to_string(),
            release_claim: "compatibility only",
            gates: &["trust-compat", "launch"],
            required_evidence: &[
                "stage2 no-verification build/test parity",
                "linked/local launch smoke",
                "explicit no proof-grade claim",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "strict Tier-0 proof",
            status: "missing_evidence".to_string(),
            release_claim: "proof",
            gates: &["trust-extra"],
            required_evidence: &[
                "strict verifier corpus",
                "proof-grade rows",
                "zero runtime_checked, unknown, skipped, no-verification, or unattributed proof rows",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "native proof engines",
            status: "missing_evidence".to_string(),
            release_claim: "proof",
            gates: &["native-contracts-pipeline-v2"],
            required_evidence: &[
                "native TrustIr evidence",
                "same-row trust-mc/trust-wp/trust-vc proof evidence",
                "replayable solver/proof artifacts",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "hardened proof",
            status: "missing_evidence".to_string(),
            release_claim: "hardened proof",
            gates: &[],
            required_evidence: &[
                "model assumptions",
                "proof-backed hardened rows",
                "certificate evidence distinguishing inventory from proof",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "trust-cg",
            status: "missing_evidence".to_string(),
            release_claim: "codegen evidence",
            gates: &["trust-extra"],
            required_evidence: &[
                "trust-cg enforce-mode parity",
                "translation-validation evidence",
                "zero report-mode exceptions in claimed rows",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "dependency integrity",
            status: "missing_evidence".to_string(),
            release_claim: "supply-chain integrity",
            gates: &["public-distribution"],
            required_evidence: &[
                "owned dependency release readiness",
                "public source and checksums",
                "offline/public distribution root integrity",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "upstream compatibility",
            status: "missing_evidence".to_string(),
            release_claim: "Rust compatibility",
            gates: &["upstream-rust-porting"],
            required_evidence: &[
                "Rust-vs-Trust scorecard",
                "upstream test port report",
                "owned exception IDs",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "distribution install",
            status: "missing_evidence".to_string(),
            release_claim: "installable Trust distribution",
            gates: &[
                "public-distribution",
                "prepublish",
                "installed",
                "installed-default",
                "stage0-lineage",
            ],
            required_evidence: &[
                "public distribution roots",
                "prepublish artifacts",
                "installed/default Trust-owned toolchain",
                "stage0 lineage",
            ],
            reason: None,
        },
        ProductProofEvidenceClass {
            class: "self-build",
            status: "missing_evidence".to_string(),
            release_claim: "verification-enabled self-build",
            gates: &[],
            required_evidence: &[
                "bounded self-build scope",
                "retained proof rows",
                "performance budgets",
                "same-commit reproduction",
            ],
            reason: None,
        },
    ]
}

pub(super) fn product_proof_component_requirements() -> Vec<ProductProofComponent> {
    vec![
        ProductProofComponent {
            component: PRODUCT_COMPONENT_TRUSTC,
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "trustc -Vv identity",
                "compiler self-host",
                "full verifier run",
                "Trust compiler suite",
            ],
        },
        ProductProofComponent {
            component: PRODUCT_COMPONENT_TARGO,
            status: "missing_evidence".to_string(),
            required_evidence: &["targo identity", "crate-mode TrustVerify dispatch"],
        },
        ProductProofComponent {
            component: PRODUCT_COMPONENT_TARGO_TRUST,
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "version identity",
                "release check transcript",
                "`targo trust` dispatch tests",
            ],
        },
        ProductProofComponent {
            component: "trustdoc",
            status: "missing_evidence".to_string(),
            required_evidence: &["documentation build", "Trust documentation binary identity"],
        },
        ProductProofComponent {
            component: "trustfmt",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "formatting component artifact",
                "Trust formatting binary identity",
            ],
        },
        ProductProofComponent {
            component: "targo-fmt",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "Cargo formatting component artifact",
                "Trust Cargo formatting binary identity",
            ],
        },
        ProductProofComponent {
            component: "tippy",
            status: "missing_evidence".to_string(),
            required_evidence: &["lint component artifact", "Trust lint binary identity"],
        },
        ProductProofComponent {
            component: "targo-tippy",
            status: "missing_evidence".to_string(),
            required_evidence: &["targo tippy dispatch", "Trust lint subcommand identity"],
        },
        ProductProofComponent {
            component: "tippy-driver",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "lint driver component artifact",
                "Trust lint driver binary identity",
            ],
        },
        ProductProofComponent {
            component: "trust-analyzer",
            status: "missing_evidence".to_string(),
            required_evidence: &["Trust analyzer component artifact", "IDE protocol smoke"],
        },
        ProductProofComponent {
            component: "trustd",
            status: "missing_evidence".to_string(),
            // The production protocol-smoke artifact already binds and
            // rechecks the exact canonical trustd path, SHA-256, version,
            // commit, IDENTITY response, and live protocol transition. A
            // second hand-authored "binary identity" document would add no
            // independent observation and, as generic JSON, has no authority.
            required_evidence: &["Trust daemon protocol smoke"],
        },
        ProductProofComponent {
            component: "trust-miri",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "optional component decision",
                "Trust Miri smoke or explicit omission",
            ],
        },
        ProductProofComponent {
            component: "targo-miri",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "optional component decision",
                "Trust Cargo Miri smoke or explicit omission",
            ],
        },
        ProductProofComponent {
            component: "std",
            status: "missing_evidence".to_string(),
            required_evidence: &["standard library artifacts", "host target std tests"],
        },
        ProductProofComponent {
            component: "source/docs",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "trust-src artifact",
                "trust-docs artifact",
                "source archive hashes",
            ],
        },
        ProductProofComponent {
            component: "LLVM/trust-cg",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "LLVM backend identity",
                "trust-cg backend identity",
                "parity gate",
            ],
        },
        ProductProofComponent {
            component: "stage0",
            status: "missing_evidence".to_string(),
            required_evidence: &["stage0 manifest", "manifest checksum", "bootstrap lineage"],
        },
        ProductProofComponent {
            component: "verifier engines",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "ay",
                "trust-mc",
                "trust-wp",
                "trust-vc",
                "model-checking engine locks",
            ],
        },
        ProductProofComponent {
            component: "upstream tests",
            status: "missing_evidence".to_string(),
            required_evidence: &["upstream test port report", "Rust-vs-Trust scorecard"],
        },
        ProductProofComponent {
            component: "binary/decomp gates",
            status: "missing_evidence".to_string(),
            required_evidence: &[
                "binary lift gate",
                "decompile release gate",
                "checked certificate evidence",
                "compile-back-artifact-digests-bound",
                "compile-back-lifted-binary-trust_ir-sha256",
                "compile-back-rust-source-sha256",
                "compile-back-reconstructed-trust_ir-sha256",
                "compile-back-refinement-artifact-sha256",
                "compile-back-root-artifact-sha256",
                "compile-back-selected-image-sha256",
                "compile-back-selected-image-range",
            ],
        },
    ]
}
