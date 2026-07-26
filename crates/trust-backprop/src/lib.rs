// dead_code audit: crate-level suppression removed
//! trust-backprop: Source rewriting engine for the prove-strengthen-backprop loop.
//!
//! Takes proposals from trust-strengthen and applies them to source code:
//! inserting first-class signature clauses (`requires`, `ensures`), replacing unsafe
//! arithmetic with checked variants, and adding runtime assertions.
//! Part of Idea 3 from VISION.md.
//!
//! Caller-precondition proof propagation is intentionally outside this crate.
//! The supported path is
//! `trust_vcgen::generate_callsite_precondition_vcs_attributed` followed by the
//! compiler's R1 harvest and
//! `trust_router::strengthen_whole_program::decide_caller_propagation`. That
//! path carries the exact call-site VC, substituted assumption, admissible
//! guards, source span, and kernel verdict for every obligation, and fails
//! closed unless caller coverage is complete. This crate only applies proposals
//! that have already crossed those proof gates; source rewriting must not
//! independently re-derive or upgrade proof obligations.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod ai_prompt;
pub(crate) mod approval;
pub(crate) mod ast_rewriter;
pub(crate) mod ast_validation;
pub(crate) mod audit_trail;
pub(crate) mod cross_module;
pub(crate) mod dependency;
pub(crate) mod diff_gen;
pub mod file_io;
mod governance;
pub(crate) mod locator;
pub(crate) mod proposal_converter;
mod rewriter;
pub(crate) mod rollback;
pub(crate) mod substitution;
pub(crate) mod type_guided;
pub(crate) mod validation;

use std::path::Path;

pub use ai_prompt::{
    AI_REPAIR_CLI, RepairPromptContext, build_ai_repair_command, build_ai_repair_prompt,
    print_ai_repair_prompt, print_ai_repair_prompts,
};
pub use approval::{
    ApprovalPolicy, ApprovalQueue, PendingRewrite, PolicyRule, RewriteKindFilter, classify_rewrite,
    default_rules,
};
pub use ast_rewriter::{
    AstRewriteError, AstRewriteTarget, NativeContractClauseSpan, SemanticRewrite,
    compute_indentation, detect_indent_unit, native_contract_clause_spans, resolve_target,
};
pub use ast_validation::{
    AstValidationError, AstValidationResult, ParseTarget, validate_rewrite_ast,
};
pub use audit_trail::{
    ApprovalStatus, AuditAction, AuditEntry, AuditEntryBuilder, AuditSummary, AuditTrail,
    ReverificationResult,
};
pub use cross_module::{CrossModulePlan, plan_cross_module_rewrites};
pub use dependency::{CallGraph, build_call_graph, topological_order};
pub use diff_gen::{
    DiffApplyError, DiffGenerator, DiffHunk, UnifiedDiff, apply_diff, format_colored,
    format_github, format_unified, generate_diff, merge_diffs, reverse_diff,
};
pub use file_io::{
    FileRewriteError, FileRewriteResult, apply_plan_to_files, apply_plan_to_source,
    proposals_to_plan, read_source, write_source,
};
pub use governance::{
    GovernancePolicy, GovernanceViolation, RewriteTracker, check_cross_module_invariants,
};
pub use locator::{FunctionLocation, find_function, find_function_first};
pub use proposal_converter::{ConvertError, convert_proposal};
pub use rewriter::{RewriteEngine, RewriteError};
pub use rollback::{
    CheckpointStore, FileSnapshot, RewriteCheckpoint, RollbackError, changed_since_checkpoint,
    create_checkpoint, rollback,
};
use serde::{Deserialize, Serialize};
pub use substitution::{
    SubstitutionError, SubstitutionMap, free_variables, rename_variable, simplify, substitute,
    substitute_with_depth,
};
use trust_strengthen::Proposal;
// Re-exported because it is part of `SourceRewrite`'s public shape: a consumer
// building a rewrite has to be able to name who proposed it.
pub use trust_types::frontend_firewall::ClaimProvenance;
use trust_types::{
    BinaryArtifactDigestIdentity, BinarySourceProvenanceSummary, BinaryVerificationStatus,
    BinaryVerificationSummary, ProofCertificateStatus, ReconstructionSummary,
    ReconstructionValidationStatus, ReplayStatus, TrustLevel,
};
pub use trust_vcgen::{
    BinaryReliftAnalysis, BinaryReliftDiagnostic, BinaryReliftDiagnosticSeverity,
    BinaryReliftError, BinaryReliftOptions, analyze_compiled_binary,
};
pub use type_guided::{
    FormulaHint, SignatureHints, TypeAnalyzer, TypePattern, generate_ensures_from_types,
    generate_requires_from_types, infer_bounds_from_type, infer_lifetime_constraints,
    infer_nullability, match_patterns,
};
pub use validation::{
    AstNode, CheckResult, SemanticDiff, ValidationCheck, ValidationConfig, ValidationResult,
    check_semantic_preservation, parse_simplified_ast, validate_rewrite,
    validate_rewrite_with_config,
};

const SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION: &str =
    "trust-proof-cert.source-backpropagation-gate.v1";

/// A plan describing a set of source rewrites to apply.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewritePlan {
    /// Individual rewrites in this plan, ordered by file then descending offset.
    pub rewrites: Vec<SourceRewrite>,
    /// Summary of what this plan does.
    pub summary: String,
}

impl RewritePlan {
    /// Create a new empty rewrite plan.
    #[must_use]
    pub fn new(summary: impl Into<String>) -> Self {
        Self { rewrites: Vec::new(), summary: summary.into() }
    }

    /// Number of rewrites in this plan.
    #[must_use]
    pub fn len(&self) -> usize {
        self.rewrites.len()
    }

    /// Whether the plan is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rewrites.is_empty()
    }

    /// Sort rewrites so they can be applied bottom-up (descending offset)
    /// within each file, preventing offset invalidation.
    pub fn sort_for_application(&mut self) {
        self.rewrites.sort_by(|a, b| a.file_path.cmp(&b.file_path).then(b.offset.cmp(&a.offset)));
    }
}

/// A single source-level rewrite operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceRewrite {
    /// Path to the source file to modify.
    pub file_path: String,
    /// Byte offset in the file where the rewrite applies.
    pub offset: usize,
    /// What kind of rewrite to perform.
    pub kind: RewriteKind,
    /// The function this rewrite targets.
    pub function_name: String,
    /// Human-readable rationale for this rewrite.
    pub rationale: String,
    /// SHA-256 of the complete source text against which this byte offset and
    /// AST target were resolved. File application rejects absent/mismatched
    /// bindings so a stale plan cannot edit a different source revision.
    #[serde(default)]
    pub expected_source_hash: Option<String>,
    /// Which language proposed this rewrite.
    ///
    /// A contract clause written into Rust source becomes a hypothesis for
    /// every later proof of that function, so who proposed it decides whether
    /// it may be applied without a human seeing it. Defaults to
    /// [`ClaimProvenance::Authoritative`], which is what every Rust-side
    /// proposer is; a frontend-derived rewrite carries its language and can
    /// never reach [`approval::ApprovalPolicy::Auto`].
    #[serde(default)]
    pub provenance: ClaimProvenance,
}

/// The kind of source-level rewrite.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RewriteKind {
    /// Insert a non-contract Rust attribute before a function. Contract
    /// attributes are compatibility input only and are never generated by the
    /// strengthen/backprop pipeline.
    InsertAttribute { attribute: String },
    /// Insert a first-class contract clause between a function's return type
    /// and its `where` clause/body.
    InsertContractClause { clause: ContractClauseKind, expression: String },
    /// Replace an expression with a new one (e.g., `a + b` -> `a.checked_add(b).unwrap()`).
    ReplaceExpression { old_text: String, new_text: String },
    /// Insert an assertion before a statement.
    InsertAssertion { assertion: String },
}

/// First-class function-signature clause kinds that backprop may generate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractClauseKind {
    Requires,
    Ensures,
}

impl ContractClauseKind {
    /// Surface keyword for this clause.
    #[must_use]
    pub const fn keyword(self) -> &'static str {
        match self {
            Self::Requires => "requires",
            Self::Ensures => "ensures",
        }
    }
}

/// Convert a list of proposals from trust-strengthen into a rewrite plan.
///
/// This is the main entry point for trust-backprop. It:
/// 1. Checks each proposal against governance rules
/// 2. Converts accepted proposals into source rewrites
/// 3. Returns a plan that can be applied to the source tree
///
/// # Errors
///
/// Returns `RewriteError::Governance` if a proposal violates governance rules
/// and `strict` mode is enabled in the policy.
pub fn apply_plan(
    proposals: &[Proposal],
    policy: &GovernancePolicy,
) -> Result<RewritePlan, RewriteError> {
    let mut plan = RewritePlan::new(format!("Backprop plan: {} proposals", proposals.len()));

    for proposal in proposals {
        // Check governance rules
        let violations = policy.check(proposal);
        if !violations.is_empty() {
            if policy.strict {
                return Err(RewriteError::Governance {
                    function: proposal.function_name.clone(),
                    violations,
                });
            }
            // In non-strict mode, skip proposals that violate governance
            continue;
        }

        // Convert proposal to source rewrites
        let rewrites = proposal_to_rewrites(proposal)?;
        plan.rewrites.extend(rewrites);
    }

    plan.sort_for_application();
    Ok(plan)
}

/// Binary-derived evidence required before diagnostics may feed source rewrites.
///
/// Binary-origin proposals are fail-closed unless the producer supplies exact
/// accepted source provenance, proof-grade binary verification evidence,
/// accepted reconstruction/target-validation evidence for the same slice, and
/// checked-certificate source-backpropagation gate acceptance.
#[derive(Debug, Clone, Copy)]
pub struct BinaryBackpropEvidence<'a> {
    /// Source provenance summary produced by the binary/decompilation path.
    pub source_provenance: &'a BinarySourceProvenanceSummary,
    /// Binary verification evidence for the same artifact or function slice.
    pub verification: &'a BinaryVerificationSummary,
    /// Reconstruction/target validation evidence for the same binary-derived slice.
    pub reconstruction: Option<&'a ReconstructionSummary>,
    /// Checked-certificate audit gate for source backpropagation.
    ///
    /// Stored as optional so legacy callers can be diagnosed explicitly; absence
    /// is rejected before planning non-empty binary-derived source rewrites.
    pub certificate_source_backpropagation_gate: Option<&'a BinarySourceBackpropagationGateDetails>,
}

impl<'a> BinaryBackpropEvidence<'a> {
    /// Create a binary backpropagation evidence bundle.
    #[must_use]
    pub fn new(
        source_provenance: &'a BinarySourceProvenanceSummary,
        verification: &'a BinaryVerificationSummary,
    ) -> Self {
        Self {
            source_provenance,
            verification,
            reconstruction: None,
            certificate_source_backpropagation_gate: None,
        }
    }

    /// Attach reconstruction evidence accepted by the binary/decompilation gate.
    #[must_use]
    pub fn with_reconstruction(mut self, reconstruction: &'a ReconstructionSummary) -> Self {
        self.reconstruction = Some(reconstruction);
        self
    }

    /// Attach mandatory checked-certificate source-backpropagation gate details.
    #[must_use]
    pub fn with_certificate_source_backpropagation_gate(
        mut self,
        gate: &'a BinarySourceBackpropagationGateDetails,
    ) -> Self {
        self.certificate_source_backpropagation_gate = Some(gate);
        self
    }

    /// Whether this evidence is strong enough to permit source rewrite planning.
    #[must_use]
    pub fn allows_source_rewrite_planning(self) -> bool {
        self.rejection_diagnostics().is_empty()
    }

    /// Structured fail-closed diagnostics for hostile review and callers.
    #[must_use]
    pub fn rejection_reasons(self) -> Vec<&'static str> {
        self.rejection_diagnostics().into_iter().map(|diagnostic| diagnostic.summary).collect()
    }

    /// Detailed fail-closed diagnostics that preserve upstream gate context.
    #[must_use]
    pub fn rejection_diagnostics(self) -> Vec<BinaryBackpropRejectionDiagnostic> {
        let mut reasons = Vec::new();
        if !self.source_provenance.effective_source_backpropagation_allowed() {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "exact-source-provenance-missing",
                category: "source_provenance",
                summary:
                "binary-derived proposals require accepted exact source provenance before source rewrite planning",
                detail: source_provenance_rejection_detail(
                    self.source_provenance,
                    self.certificate_source_backpropagation_gate,
                ),
                evidence_required: vec!["exact_binary_source_provenance"],
            });
        }
        if !binary_verification_has_proof_grade_evidence(self.verification) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "proof-grade-binary-verification-missing",
                category: "binary_verification",
                summary:
                "binary-derived proposals require proof-grade binary verification evidence before source rewrite planning",
                detail: binary_verification_rejection_detail(self.verification),
                evidence_required: vec![
                    "proof_grade_binary_verification",
                    "checked_certificate_identity",
                    "exact_replay_identity",
                    "replay_grade_binary_artifact_identity",
                    "unsupported_ledger_elimination",
                ],
            });
        }
        if !binary_verification_has_replay_grade_artifact_identity(self.verification) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "replay-grade-artifact-identity-missing",
                category: "replay_identity",
                summary:
                "binary-derived proposals require replay-grade binary artifact identity before source rewrite planning",
                detail: replay_identity_rejection_detail(
                    self.verification,
                    self.certificate_source_backpropagation_gate,
                ),
                evidence_required: vec![
                    "replay_grade_binary_artifact_identity",
                    "exact_replay_identity",
                ],
            });
        }
        if !binary_verification_has_checked_certificate_identity(self.verification) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "checked-certificate-identity-missing",
                category: "checked_certificate",
                summary:
                "binary-derived proposals require checked certificate identity before source rewrite planning",
                detail: checked_certificate_rejection_detail(
                    self.verification,
                    self.certificate_source_backpropagation_gate,
                ),
                evidence_required: vec![
                    "checked_certificate_identity",
                    "production_checker_evidence",
                ],
            });
        }
        if !certificate_source_backpropagation_gate_allows_source_rewrites(
            self.certificate_source_backpropagation_gate,
            self.source_provenance,
        ) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "certificate-source-backpropagation-gate-rejected",
                category: "checked_certificate_source_backpropagation_gate",
                summary:
                "binary-derived proposals require checked certificate source_backpropagation_gate acceptance before source rewrite planning",
                detail: certificate_source_backpropagation_gate_rejection_detail(
                    self.certificate_source_backpropagation_gate,
                    self.source_provenance,
                ),
                evidence_required: vec![
                    "checked_certificate_source_backpropagation_gate",
                    "source_backpropagation_allowed",
                    "checked_binary_source_provenance_identity",
                ],
            });
        }
        if let Some(detail) = checked_source_provenance_handoff_rejection_detail(
            self.source_provenance,
            self.verification,
            self.certificate_source_backpropagation_gate,
        ) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "checked-source-provenance-handoff-rejected",
                category: "checked_binary_source_provenance",
                summary:
                "binary-derived proposals require checked source provenance bound to the same binary before source rewrite planning",
                detail,
                evidence_required: vec![
                    "checked_binary_source_provenance_import",
                    "matching_binary_artifact_digest_identity",
                ],
            });
        }
        if !self.reconstruction.is_some_and(reconstruction_allows_source_backpropagation) {
            reasons.push(BinaryBackpropRejectionDiagnostic {
                code: "accepted-reconstruction-target-validation-missing",
                category: "reconstruction_target_validation",
                summary:
                "binary-derived proposals require accepted reconstruction and target validation before source rewrite planning",
                detail: reconstruction_rejection_detail(self.reconstruction),
                evidence_required: vec![
                    "accepted_reconstruction",
                    "target_semantic_validation",
                ],
            });
        }
        reasons
    }

    fn rejection_reason(self) -> Option<String> {
        let diagnostics = self.rejection_diagnostics();
        if diagnostics.is_empty() {
            None
        } else {
            Some(
                diagnostics
                    .iter()
                    .map(BinaryBackpropRejectionDiagnostic::message)
                    .collect::<Vec<_>>()
                    .join("; "),
            )
        }
    }
}

/// Structured source-backpropagation rejection emitted by binary evidence gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryBackpropRejectionDiagnostic {
    /// Stable machine-readable blocker code.
    pub code: &'static str,
    /// Evidence class rejected by this diagnostic.
    pub category: &'static str,
    /// Stable compatibility summary used by legacy callers.
    pub summary: &'static str,
    /// Detailed diagnostic preserving upstream gate state.
    pub detail: String,
    /// Evidence fields required to clear this blocker.
    pub evidence_required: Vec<&'static str>,
}

/// Serializable subset of checked-certificate `source_backpropagation_gate` details.
///
/// The fields intentionally mirror proof-cert audit gate JSON so callers can
/// pass audited gate details into backprop without coupling rewrite planning to
/// a certificate-checking crate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceBackpropagationGateDetails {
    /// Source-backpropagation gate schema version from the producer.
    pub schema_version: String,
    /// Whether replay-grade artifact identity was accepted.
    pub replay_grade_artifact_identity: bool,
    /// Whether checked certificate identity was accepted.
    pub checked_certificate_identity: bool,
    /// Whether exact replay identity was accepted.
    pub exact_replay_identity: bool,
    /// Whether reconstruction validation was accepted.
    pub accepted_reconstruction_validation: bool,
    /// Whether target validation was accepted.
    pub accepted_target_validation: bool,
    /// Whether exact source provenance was accepted.
    pub exact_source_provenance: bool,
    /// Source provenance summary carried by the gate.
    pub source_provenance: BinarySourceProvenanceSummary,
    /// Binary identity covered by the imported checked source-provenance artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checked_source_provenance_binary_identity: Option<BinaryArtifactDigestIdentity>,
    /// Producer decision for source backpropagation.
    pub source_backpropagation_allowed: bool,
    /// Producer blockers when source backpropagation was rejected.
    pub blockers: Vec<String>,
}

impl BinarySourceBackpropagationGateDetails {
    /// Build evaluated gate details from producer acceptance booleans.
    #[must_use]
    pub fn evaluated(
        source_provenance: BinarySourceProvenanceSummary,
        replay_grade_artifact_identity: bool,
        checked_certificate_identity: bool,
        exact_replay_identity: bool,
        accepted_reconstruction_validation: bool,
        accepted_target_validation: bool,
        exact_source_provenance: bool,
    ) -> Self {
        let mut gate = Self {
            schema_version: SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION.to_string(),
            replay_grade_artifact_identity,
            checked_certificate_identity,
            exact_replay_identity,
            accepted_reconstruction_validation,
            accepted_target_validation,
            exact_source_provenance,
            source_provenance,
            checked_source_provenance_binary_identity: None,
            source_backpropagation_allowed: false,
            blockers: Vec::new(),
        };
        gate.blockers = gate.prerequisite_blockers();
        gate.source_backpropagation_allowed = gate.blockers.is_empty();
        gate
    }

    /// Attach the exact binary identity accepted by the checked source-provenance import.
    #[must_use]
    pub fn with_checked_source_provenance_binary_identity(
        mut self,
        identity: BinaryArtifactDigestIdentity,
    ) -> Self {
        self.checked_source_provenance_binary_identity = Some(identity);
        self.blockers = self.prerequisite_blockers();
        self.source_backpropagation_allowed = self.blockers.is_empty();
        self
    }

    /// Build closed gate details with producer-supplied blockers.
    #[must_use]
    pub fn closed_with_blockers<I, S>(
        source_provenance: BinarySourceProvenanceSummary,
        blockers: I,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            source_provenance,
            blockers: blockers.into_iter().map(Into::into).collect(),
            ..Self::default()
        }
    }

    fn prerequisite_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.schema_version != SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION {
            blockers.push("source_backpropagation_gate_schema_version_unsupported".to_string());
        }
        if !self.replay_grade_artifact_identity {
            blockers.push("replay_grade_artifact_identity_missing".to_string());
        }
        if !self.checked_certificate_identity {
            blockers.push("checked_certificate_identity_missing".to_string());
        }
        if !self.exact_replay_identity {
            blockers.push("exact_replay_identity_missing".to_string());
        }
        if !self.accepted_reconstruction_validation {
            blockers.push("accepted_reconstruction_validation_missing".to_string());
        }
        if !self.accepted_target_validation {
            blockers.push("accepted_target_validation_missing".to_string());
        }
        if !self.exact_source_provenance {
            blockers.push("exact_source_provenance_missing".to_string());
        }
        if !self.source_provenance.effective_source_backpropagation_allowed() {
            blockers.push("source_provenance_not_effective".to_string());
        }
        match &self.checked_source_provenance_binary_identity {
            Some(identity) if identity.digest_identity_allows_replay() => {}
            Some(identity) => blockers.push(format!(
                "checked_source_provenance_binary_identity_not_replay_grade:{}",
                identity.digest_identity_blockers().join("|")
            )),
            None => blockers.push("checked_source_provenance_binary_identity_missing".to_string()),
        }
        blockers
    }
}

impl Default for BinarySourceBackpropagationGateDetails {
    fn default() -> Self {
        Self {
            schema_version: SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION.to_string(),
            replay_grade_artifact_identity: false,
            checked_certificate_identity: false,
            exact_replay_identity: false,
            accepted_reconstruction_validation: false,
            accepted_target_validation: false,
            exact_source_provenance: false,
            source_provenance: BinarySourceProvenanceSummary::default(),
            checked_source_provenance_binary_identity: None,
            source_backpropagation_allowed: false,
            blockers: vec!["source_backpropagation_gate_not_evaluated".to_string()],
        }
    }
}

impl BinaryBackpropRejectionDiagnostic {
    /// Human-readable diagnostic with code, summary, and structured detail.
    #[must_use]
    pub fn message(&self) -> String {
        format!("{}: {}; {}", self.code, self.summary, self.detail)
    }
}

fn source_provenance_rejection_detail(
    provenance: &BinarySourceProvenanceSummary,
    gate: Option<&BinarySourceBackpropagationGateDetails>,
) -> String {
    let mut parts = vec![
        format!("source_provenance.status={}", provenance.status),
        format!("source_provenance.exact_mapping_count={}", provenance.exact_mapping_count),
        format!("source_provenance.ambiguous_mapping_count={}", provenance.ambiguous_mapping_count),
        format!(
            "source_provenance.source_backpropagation_allowed={}",
            provenance.source_backpropagation_allowed
        ),
        format!(
            "source_provenance.effective_source_backpropagation_allowed={}",
            provenance.effective_source_backpropagation_allowed()
        ),
    ];
    if !provenance.diagnostics.is_empty() {
        parts.push(format!("source_provenance.diagnostics={}", provenance.diagnostics.join(" | ")));
    }
    if let Some(gate) = gate {
        parts.push(format!(
            "source_backpropagation_gate.exact_source_provenance={}",
            gate.exact_source_provenance
        ));
        parts.push(format!(
            "source_backpropagation_gate.source_backpropagation_allowed={}",
            gate.source_backpropagation_allowed
        ));
        if !gate.blockers.is_empty() {
            parts.push(format!("source_backpropagation_gate.blockers={}", gate.blockers.join(",")));
        }
    }
    parts.join("; ")
}

fn binary_verification_rejection_detail(verification: &BinaryVerificationSummary) -> String {
    format!(
        "verification.status={:?}; verification.trust_level={:?}; total_vcs={}; proved={}; failed={}; unknown={}; timeout={}; unsupported={}; rejected={}; replay={:?}; unsupported_ledger_empty={}; unsupported_ledger_records={}; assumptions={}; claims={}; witnesses={}; proof_certificate={}",
        verification.status,
        verification.trust_level,
        verification.total_vcs,
        verification.proved,
        verification.failed,
        verification.unknown,
        verification.timeout,
        verification.unsupported,
        verification.rejected,
        verification.replay,
        verification.unsupported_ledger.is_empty(),
        verification.unsupported_ledger.records.len(),
        verification.assumptions.len(),
        verification.claims.len(),
        verification.witnesses.len(),
        proof_certificate_backprop_label(&verification.proof_certificate),
    )
}

fn replay_identity_rejection_detail(
    verification: &BinaryVerificationSummary,
    gate: Option<&BinarySourceBackpropagationGateDetails>,
) -> String {
    let missing_dispatches = verification
        .solver_dispatch
        .iter()
        .filter(|dispatch| !dispatch.replay_digest_identity_allows_proof_grade())
        .map(|dispatch| dispatch.id.as_str())
        .collect::<Vec<_>>();
    let mut parts = vec![
        format!("verification.replay={:?}", verification.replay),
        format!("dispatch_count={}", verification.solver_dispatch.len()),
        format!("total_vcs={}", verification.total_vcs),
    ];
    if !missing_dispatches.is_empty() {
        parts.push(format!(
            "dispatches_missing_replay_grade_identity={}",
            missing_dispatches.join(",")
        ));
    }
    if let Some(gate) = gate {
        parts.push(format!(
            "source_backpropagation_gate.replay_grade_artifact_identity={}",
            gate.replay_grade_artifact_identity
        ));
        parts.push(format!(
            "source_backpropagation_gate.exact_replay_identity={}",
            gate.exact_replay_identity
        ));
        if !gate.blockers.is_empty() {
            parts.push(format!("source_backpropagation_gate.blockers={}", gate.blockers.join(",")));
        }
    }
    parts.join("; ")
}

fn checked_certificate_rejection_detail(
    verification: &BinaryVerificationSummary,
    gate: Option<&BinarySourceBackpropagationGateDetails>,
) -> String {
    let invalid_dispatches = verification
        .solver_dispatch
        .iter()
        .filter(|dispatch| !proof_certificate_is_checked_for_backprop(&dispatch.certificate))
        .map(|dispatch| {
            format!("{}:{}", dispatch.id, proof_certificate_backprop_label(&dispatch.certificate))
        })
        .collect::<Vec<_>>();
    let mut parts = vec![
        format!(
            "summary_proof_certificate={}",
            proof_certificate_backprop_label(&verification.proof_certificate)
        ),
        format!("dispatch_count={}", verification.solver_dispatch.len()),
        format!("total_vcs={}", verification.total_vcs),
    ];
    if !invalid_dispatches.is_empty() {
        parts.push(format!(
            "dispatches_missing_checked_certificate_identity={}",
            invalid_dispatches.join(",")
        ));
    }
    if let Some(gate) = gate {
        parts.push(format!(
            "source_backpropagation_gate.checked_certificate_identity={}",
            gate.checked_certificate_identity
        ));
        if !gate.blockers.is_empty() {
            parts.push(format!("source_backpropagation_gate.blockers={}", gate.blockers.join(",")));
        }
    }
    parts.join("; ")
}

fn certificate_source_backpropagation_gate_rejection_detail(
    gate: Option<&BinarySourceBackpropagationGateDetails>,
    expected_source_provenance: &BinarySourceProvenanceSummary,
) -> String {
    let Some(gate) = gate else {
        return "source_backpropagation_gate=missing".to_string();
    };
    let source_provenance_matches_runtime = gate.source_provenance == *expected_source_provenance;
    format!(
        "source_backpropagation_gate.schema_version={}; expected_schema_version={}; replay_grade_artifact_identity={}; checked_certificate_identity={}; exact_replay_identity={}; accepted_reconstruction_validation={}; accepted_target_validation={}; exact_source_provenance={}; source_provenance_matches_runtime={}; gate_source_provenance_status={}; gate_source_provenance_exact_mappings={}; runtime_source_provenance_status={}; runtime_source_provenance_exact_mappings={}; checked_source_provenance_binary_identity={}; source_backpropagation_allowed={}; blockers={}",
        gate.schema_version,
        SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION,
        gate.replay_grade_artifact_identity,
        gate.checked_certificate_identity,
        gate.exact_replay_identity,
        gate.accepted_reconstruction_validation,
        gate.accepted_target_validation,
        gate.exact_source_provenance,
        source_provenance_matches_runtime,
        gate.source_provenance.status,
        gate.source_provenance.exact_mapping_count,
        expected_source_provenance.status,
        expected_source_provenance.exact_mapping_count,
        binary_artifact_digest_identity_summary(
            gate.checked_source_provenance_binary_identity.as_ref()
        ),
        gate.source_backpropagation_allowed,
        if gate.blockers.is_empty() { "<none>".to_string() } else { gate.blockers.join(",") },
    )
}

fn checked_source_provenance_handoff_rejection_detail(
    source_provenance: &BinarySourceProvenanceSummary,
    verification: &BinaryVerificationSummary,
    gate: Option<&BinarySourceBackpropagationGateDetails>,
) -> Option<String> {
    let gate = gate?;
    if !gate.source_backpropagation_allowed {
        return None;
    }

    let mut blockers = Vec::new();

    if gate.source_provenance != *source_provenance {
        blockers.push(format!(
            "checked_source_provenance_summary_mismatch: runtime_status={}, checked_status={}, runtime_exact_mapping_count={}, checked_exact_mapping_count={}",
            source_provenance.status,
            gate.source_provenance.status,
            source_provenance.exact_mapping_count,
            gate.source_provenance.exact_mapping_count
        ));
    }

    let checked_identity = gate.checked_source_provenance_binary_identity.as_ref();
    match checked_identity {
        Some(identity) if identity.digest_identity_allows_replay() => {}
        Some(identity) => blockers.push(format!(
            "checked_source_provenance_binary_identity_not_replay_grade:{}",
            identity.digest_identity_blockers().join("|")
        )),
        None => blockers.push("checked_source_provenance_binary_identity_missing".to_string()),
    }

    if verification.total_vcs == 0 {
        blockers.push("checked_source_provenance_requires_required_vc_identity".to_string());
    }
    if verification.solver_dispatch.len() != verification.total_vcs {
        blockers.push(format!(
            "checked_source_provenance_dispatch_count_mismatch: dispatch_count={}, total_vcs={}",
            verification.solver_dispatch.len(),
            verification.total_vcs
        ));
    }

    if let Some(checked_identity) = checked_identity {
        for dispatch in &verification.solver_dispatch {
            match dispatch.binary_artifact_digest_identity.as_ref() {
                Some(dispatch_identity) if dispatch_identity == checked_identity => {}
                Some(dispatch_identity) => blockers.push(format!(
                    "checked_source_provenance_wrong_binary: dispatch_id={}, checked_identity={}, dispatch_identity={}",
                    dispatch.id,
                    binary_artifact_digest_identity_summary(Some(checked_identity)),
                    binary_artifact_digest_identity_summary(Some(dispatch_identity))
                )),
                None => blockers.push(format!(
                    "checked_source_provenance_dispatch_identity_missing: dispatch_id={}",
                    dispatch.id
                )),
            }
        }
    }

    (!blockers.is_empty()).then(|| {
        format!(
            "checked_source_provenance_binary_identity={}; runtime_source_provenance_status={}; checked_source_provenance_status={}; blockers={}",
            binary_artifact_digest_identity_summary(checked_identity),
            source_provenance.status,
            gate.source_provenance.status,
            blockers.join("; ")
        )
    })
}

fn binary_artifact_digest_identity_summary(
    identity: Option<&BinaryArtifactDigestIdentity>,
) -> String {
    let Some(identity) = identity else {
        return "missing".to_string();
    };

    let root = identity
        .root_artifact_digest
        .as_ref()
        .map(|digest| format!("{}:{}", digest.algorithm, digest.value))
        .unwrap_or_else(|| "missing".to_string());
    let selected = identity
        .selected_image
        .as_ref()
        .map(|selected| {
            format!(
                "offset={},size={},sha256={}",
                selected.file_offset, selected.file_size, selected.sha256
            )
        })
        .unwrap_or_else(|| "missing".to_string());

    format!("root={root},selected_image={selected}")
}

fn reconstruction_rejection_detail(reconstruction: Option<&ReconstructionSummary>) -> String {
    let Some(reconstruction) = reconstruction else {
        return "reconstruction=missing".to_string();
    };
    let output_blockers = reconstruction
        .outputs
        .iter()
        .flat_map(|output| {
            output.target_validation_blockers.iter().map(move |blocker| {
                format!("{:?}:{}:{}", output.target, blocker.stage, blocker.feature)
            })
        })
        .collect::<Vec<_>>();
    let output_assumptions =
        reconstruction.outputs.iter().map(|output| output.assumptions.len()).sum::<usize>();
    format!(
        "reconstruction.target={:?}; reconstruction.validation={:?}; reconstruction.trust_level={:?}; reconstruction.outputs={}; reconstruction.assumptions={}; output_assumptions={}; target_validation_blockers={}",
        reconstruction.target,
        reconstruction.validation,
        reconstruction.trust_level,
        reconstruction.outputs.len(),
        reconstruction.assumptions.len(),
        output_assumptions,
        if output_blockers.is_empty() { "<none>".to_string() } else { output_blockers.join(",") },
    )
}

fn proof_certificate_backprop_label(certificate: &ProofCertificateStatus) -> String {
    match certificate {
        ProofCertificateStatus::Checked { checker, format, sha256 } => format!(
            "checked(checker={}, format={}, sha256={}, production={})",
            checker,
            format,
            sha256.as_deref().unwrap_or("<missing>"),
            certificate.is_production_checked()
        ),
        ProofCertificateStatus::Present { format, sha256, .. } => format!(
            "present(format={}, sha256={})",
            format,
            sha256.as_deref().unwrap_or("<missing>")
        ),
        ProofCertificateStatus::Unavailable { reason } => {
            format!("unavailable(reason={})", reason.as_deref().unwrap_or("<missing>"))
        }
        ProofCertificateStatus::Rejected { reason, .. } => format!("rejected(reason={reason})"),
        ProofCertificateStatus::NotRequested => "not_requested".to_string(),
        _ => "unknown".to_string(),
    }
}

/// Compatibility helper for legacy callers that cannot provide reconstruction
/// or checked-certificate source-backpropagation gate evidence yet. Because
/// both are mandatory, this intentionally fails closed even when source
/// provenance and binary verification look proof-grade.
#[must_use]
pub fn binary_backprop_evidence_allows_source_rewrites(
    source_provenance: &BinarySourceProvenanceSummary,
    verification: &BinaryVerificationSummary,
) -> bool {
    BinaryBackpropEvidence::new(source_provenance, verification).allows_source_rewrite_planning()
}

/// Compatibility helper for legacy callers that cannot provide checked-certificate
/// source-backpropagation gate evidence yet. Because that gate is mandatory,
/// this intentionally fails closed even when reconstruction and binary
/// verification look proof-grade.
#[must_use]
pub fn binary_backprop_evidence_allows_source_rewrites_with_reconstruction(
    source_provenance: &BinarySourceProvenanceSummary,
    verification: &BinaryVerificationSummary,
    reconstruction: &ReconstructionSummary,
) -> bool {
    BinaryBackpropEvidence::new(source_provenance, verification)
        .with_reconstruction(reconstruction)
        .allows_source_rewrite_planning()
}

/// Return true only when binary evidence, reconstruction validation, and an
/// accepted checked-certificate source-backpropagation gate are all present.
#[must_use]
pub fn binary_backprop_evidence_allows_source_rewrites_with_reconstruction_and_source_gate(
    source_provenance: &BinarySourceProvenanceSummary,
    verification: &BinaryVerificationSummary,
    reconstruction: &ReconstructionSummary,
    source_gate: &BinarySourceBackpropagationGateDetails,
) -> bool {
    BinaryBackpropEvidence::new(source_provenance, verification)
        .with_reconstruction(reconstruction)
        .with_certificate_source_backpropagation_gate(source_gate)
        .allows_source_rewrite_planning()
}

fn binary_verification_has_proof_grade_evidence(verification: &BinaryVerificationSummary) -> bool {
    verification.trust_level == TrustLevel::ProofGrade
        && verification.status == BinaryVerificationStatus::Proved
        && verification.total_vcs > 0
        && verification.proved == verification.total_vcs
        && verification.failed == 0
        && verification.unknown == 0
        && verification.timeout == 0
        && verification.unsupported == 0
        && verification.rejected == 0
        && verification.replay == ReplayStatus::Replayed
        && verification.unsupported_ledger.is_empty()
        && verification.assumptions.is_empty()
        && verification.claims.is_empty()
        && verification.witnesses.is_empty()
        && proof_certificate_is_checked_for_backprop(&verification.proof_certificate)
}

fn binary_verification_has_replay_grade_artifact_identity(
    verification: &BinaryVerificationSummary,
) -> bool {
    verification.total_vcs > 0
        && verification.solver_dispatch.len() == verification.total_vcs
        && verification
            .solver_dispatch
            .iter()
            .all(trust_types::SolverDispatchRecord::replay_digest_identity_allows_proof_grade)
}

fn binary_verification_has_checked_certificate_identity(
    verification: &BinaryVerificationSummary,
) -> bool {
    proof_certificate_is_checked_for_backprop(&verification.proof_certificate)
        && verification.total_vcs > 0
        && verification.solver_dispatch.len() == verification.total_vcs
        && verification
            .solver_dispatch
            .iter()
            .all(|dispatch| proof_certificate_is_checked_for_backprop(&dispatch.certificate))
}

fn certificate_source_backpropagation_gate_allows_source_rewrites(
    gate: Option<&BinarySourceBackpropagationGateDetails>,
    expected_source_provenance: &BinarySourceProvenanceSummary,
) -> bool {
    gate.is_some_and(|gate| {
        gate.schema_version == SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION
            && gate.source_backpropagation_allowed
            && gate.replay_grade_artifact_identity
            && gate.checked_certificate_identity
            && gate.exact_replay_identity
            && gate.accepted_reconstruction_validation
            && gate.accepted_target_validation
            && gate.exact_source_provenance
            && gate.source_provenance.effective_source_backpropagation_allowed()
            && gate.source_provenance == *expected_source_provenance
            && gate
                .checked_source_provenance_binary_identity
                .as_ref()
                .is_some_and(BinaryArtifactDigestIdentity::digest_identity_allows_replay)
            && gate.blockers.is_empty()
    })
}

fn proof_certificate_is_checked_for_backprop(certificate: &ProofCertificateStatus) -> bool {
    let ProofCertificateStatus::Checked { checker, format, sha256: Some(sha256) } = certificate
    else {
        return false;
    };

    !checker.trim().is_empty()
        && !format.trim().is_empty()
        && is_canonical_lowercase_sha256(sha256)
        && certificate.is_production_checked()
}

fn is_canonical_lowercase_sha256(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn reconstruction_allows_source_backpropagation(reconstruction: &ReconstructionSummary) -> bool {
    reconstruction.validation == ReconstructionValidationStatus::Validated
        && reconstruction.trust_level == TrustLevel::ProofGrade
        && !reconstruction.outputs.is_empty()
        && reconstruction.assumptions.is_empty()
        && reconstruction.outputs.iter().all(|output| {
            output.validation == ReconstructionValidationStatus::Validated
                && output.trust_level == TrustLevel::ProofGrade
                && output.target_validation_blockers.is_empty()
                && output.assumptions.is_empty()
        })
}

/// Plan source rewrites for binary-derived proposals after provenance gating.
///
/// The gate is fail-closed: proposals are rejected before planning unless
/// evidence has exact accepted source provenance, proof-grade binary
/// verification, accepted reconstruction/target-validation evidence, and
/// checked-certificate source-backpropagation gate acceptance. Binary address-only
/// or symbolic pseudo-path proposals still remain report-only and produce no
/// source rewrites.
pub fn apply_binary_derived_plan(
    proposals: &[Proposal],
    policy: &GovernancePolicy,
    evidence: BinaryBackpropEvidence<'_>,
) -> Result<RewritePlan, RewriteError> {
    if !proposals.is_empty()
        && let Some(reason) = evidence.rejection_reason()
    {
        return Err(RewriteError::UnsafeProvenance {
            function: first_proposal_function(proposals),
            reason,
        });
    }

    apply_plan(proposals, policy)
}

/// Result of the reusable compiled-binary relift/backprop entrypoint.
#[derive(Debug, Clone)]
pub struct BinaryReliftBackpropResult {
    /// TrustIr relift, generated binary VCs, and binary diagnostics.
    pub analysis: BinaryReliftAnalysis,
    /// Source rewrite plan accepted by the binary evidence gate.
    pub plan: RewritePlan,
}

/// Error from relifting a compiled binary and attempting source backpropagation.
#[derive(Debug, thiserror::Error)]
pub enum BinaryReliftBackpropError {
    /// Binary parsing/lifting or VC analysis failed.
    #[error(transparent)]
    Relift(#[from] BinaryReliftError),
    /// Supplied proof/gate evidence did not match the current relifted binary.
    #[error(
        "binary backpropagation evidence does not match relifted binary for `{function}`: {reason}"
    )]
    EvidenceMismatch { function: String, reason: String },
    /// Existing source rewrite governance/provenance gate rejected the plan.
    #[error(transparent)]
    Rewrite(#[from] RewriteError),
}

/// Re-lift a compiled binary, generate binary verification diagnostics, and
/// plan source rewrites only when exact provenance and checked gate evidence
/// match the relifted artifact.
///
/// Relift analysis itself never grants rewrite permission. Non-empty proposal
/// sets must pass both the current relift consistency checks and
/// [`apply_binary_derived_plan`]'s exact source/gate evidence checks.
///
/// # Errors
///
/// Returns [`BinaryReliftBackpropError`] if relifting fails, supplied evidence
/// does not match the relifted binary summaries, or source rewrite planning is
/// rejected by governance/provenance gates.
pub fn apply_binary_derived_plan_from_compiled_binary(
    binary_bytes: &[u8],
    relift_options: BinaryReliftOptions,
    proposals: &[Proposal],
    policy: &GovernancePolicy,
    evidence: BinaryBackpropEvidence<'_>,
) -> Result<BinaryReliftBackpropResult, BinaryReliftBackpropError> {
    let analysis = analyze_compiled_binary(binary_bytes, relift_options)?;
    if !proposals.is_empty() {
        validate_binary_backprop_evidence_matches_relift(
            &analysis.source_provenance,
            &analysis.verification,
            evidence,
            first_proposal_function(proposals),
        )?;
    }

    let plan = apply_binary_derived_plan(proposals, policy, evidence)?;
    Ok(BinaryReliftBackpropResult { analysis, plan })
}

/// Fail-closed consistency check between fresh relift output and supplied
/// source-backpropagation evidence.
///
/// This check is intentionally separate from certificate/evidence acceptance:
/// `BinaryBackpropEvidence` may be proof-grade in isolation, but source rewrites
/// from this API also require that the proof/gate evidence matches the binary
/// relift performed in the same call.
pub fn validate_binary_backprop_evidence_matches_relift(
    relift_source_provenance: &BinarySourceProvenanceSummary,
    relift_verification: &BinaryVerificationSummary,
    evidence: BinaryBackpropEvidence<'_>,
    function: impl Into<String>,
) -> Result<(), BinaryReliftBackpropError> {
    let function = function.into();
    if evidence.source_provenance != relift_source_provenance {
        return Err(BinaryReliftBackpropError::EvidenceMismatch {
            function,
            reason: format!(
                "source provenance summary mismatch: relift_status={}, evidence_status={}, relift_exact_mappings={}, evidence_exact_mappings={}",
                relift_source_provenance.status,
                evidence.source_provenance.status,
                relift_source_provenance.exact_mapping_count,
                evidence.source_provenance.exact_mapping_count
            ),
        });
    }

    if evidence.verification.total_vcs != relift_verification.total_vcs {
        return Err(BinaryReliftBackpropError::EvidenceMismatch {
            function,
            reason: format!(
                "binary VC count mismatch: relift_total_vcs={}, evidence_total_vcs={}",
                relift_verification.total_vcs, evidence.verification.total_vcs
            ),
        });
    }

    if evidence.verification.unsupported_ledger != relift_verification.unsupported_ledger {
        return Err(BinaryReliftBackpropError::EvidenceMismatch {
            function,
            reason: format!(
                "unsupported ledger mismatch: relift_records={}, evidence_records={}",
                relift_verification.unsupported_ledger.records.len(),
                evidence.verification.unsupported_ledger.records.len()
            ),
        });
    }

    let relift_kinds = relift_verification
        .solver_dispatch
        .iter()
        .map(|dispatch| dispatch.vc_kind.as_ref().map(|kind| format!("{kind:?}")))
        .collect::<Vec<_>>();
    let evidence_kinds = evidence
        .verification
        .solver_dispatch
        .iter()
        .map(|dispatch| dispatch.vc_kind.as_ref().map(|kind| format!("{kind:?}")))
        .collect::<Vec<_>>();
    if relift_kinds.iter().any(|kind| kind.is_none())
        || evidence_kinds.iter().any(|kind| kind.is_none())
    {
        return Err(BinaryReliftBackpropError::EvidenceMismatch {
            function,
            reason: "binary VC kind identity is missing; exact relift/proof handoff is required"
                .to_string(),
        });
    }
    if relift_kinds != evidence_kinds {
        return Err(BinaryReliftBackpropError::EvidenceMismatch {
            function,
            reason: "binary VC kind identity mismatch between relift and evidence".to_string(),
        });
    }

    Ok(())
}

fn first_proposal_function(proposals: &[Proposal]) -> String {
    proposals
        .first()
        .map(|proposal| proposal.function_name.clone())
        .unwrap_or_else(|| "<binary>".into())
}

/// Convert a single proposal into zero or more source rewrites.
///
/// Computes the byte offset from the proposal's `function_path` (source file) by
/// reading the file and delegating to the single AST-bounded proposal converter.
/// Report-only/non-source provenance is the only intentional empty-plan case;
/// unreadable source, missing targets, invalid specs, and stale expressions are
/// explicit errors.
fn proposal_to_rewrites(proposal: &Proposal) -> Result<Vec<SourceRewrite>, RewriteError> {
    if report_only_provenance_path_reason(&proposal.function_path).is_some()
        || !is_rust_source_path(&proposal.function_path)
    {
        return Ok(Vec::new());
    }

    let source = std::fs::read_to_string(&proposal.function_path).map_err(|error| {
        RewriteError::InvalidSource {
            file_path: proposal.function_path.clone(),
            reason: error.to_string(),
        }
    })?;
    convert_proposal(proposal, &source, &proposal.function_path).map_err(Into::into)
}

pub(crate) fn is_binary_pseudo_path(path: &str) -> bool {
    let path = path.trim();
    path == "binary" || path.strip_prefix("binary").is_some_and(|suffix| suffix.starts_with(':'))
}

pub(crate) fn report_only_provenance_path_reason(path: &str) -> Option<&'static str> {
    let path = path.trim();
    if is_binary_pseudo_path(path) {
        return Some("binary pseudo-paths are report-only and cannot be rewritten");
    }
    if is_non_source_pseudo_path(path) {
        return Some("pseudo provenance paths are report-only and cannot be rewritten");
    }
    None
}

fn is_non_source_pseudo_path(path: &str) -> bool {
    path.starts_with('<')
        || path.contains("://")
        || path.contains("::")
        || leading_component_looks_like_scheme(path)
}

fn leading_component_looks_like_scheme(path: &str) -> bool {
    let leading = path.split(['/', '\\']).next().unwrap_or(path);
    if leading.len() == 2 && leading.ends_with(':') && leading.as_bytes()[0].is_ascii_alphabetic() {
        return false;
    }
    leading.contains(':')
}

fn is_rust_source_path(path: &str) -> bool {
    Path::new(path).extension().and_then(|ext| ext.to_str()) == Some("rs")
}

#[cfg(test)]
mod tests {
    use trust_strengthen::{Proposal, ProposalKind};
    use trust_types::{
        BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinarySelectedImageIdentity,
        BinarySourceProvenanceSummary, BinaryVerificationStatus, BinaryVerificationSummary,
        DecompileTarget, DecompiledOutput, ModelAssumption,
        ProofCertificateProductionCheckerEvidenceRef, ProofCertificateStatus,
        ReconstructionSummary, ReconstructionValidationStatus, ReplayStatus, SolverDispatchRecord,
        SolverDispatchStatus, TargetValidationBlocker, TrustLevel, UnsupportedRecord, VcKind,
    };

    use super::*;

    fn temp_source_file(source: &str) -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().expect("create temp source dir");
        let path = dir.path().join("lib.rs");
        std::fs::write(&path, source).expect("write temp source");
        (dir, path.display().to_string())
    }

    fn make_precondition_proposal(func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: format!("test::{func}"),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition { spec_body: spec.into() },
            confidence: 0.9,
            rationale: "test proposal".into(),
        }
    }

    fn make_precondition_proposal_at(path: &str, func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: path.into(),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition { spec_body: spec.into() },
            confidence: 0.9,
            rationale: "test proposal".into(),
        }
    }

    fn make_safe_arithmetic_proposal_at(path: &str, func: &str) -> Proposal {
        Proposal {
            function_path: path.into(),
            function_name: func.into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "Replace raw addition with checked_add".into(),
        }
    }

    fn exact_source_provenance() -> BinarySourceProvenanceSummary {
        BinarySourceProvenanceSummary {
            status: "exact".into(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        }
    }

    fn checked_certificate() -> ProofCertificateStatus {
        let checker_evidence = ProofCertificateProductionCheckerEvidenceRef::new(
            "test-checker",
            "1.0.0",
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        )
        .expect("production checker evidence should be valid");
        ProofCertificateStatus::Checked {
            checker: checker_evidence.legacy_checker_status(),
            format: "test-cert".into(),
            sha256: Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()),
        }
    }

    fn replay_grade_artifact_identity() -> BinaryArtifactDigestIdentity {
        BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(
                "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            )),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 16,
                sha256: "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".into(),
            }),
        }
    }

    fn proof_grade_binary_verification() -> BinaryVerificationSummary {
        let certificate = checked_certificate();
        BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            solver_dispatch: vec![SolverDispatchRecord {
                id: "test-vc".into(),
                solver: "test-solver".into(),
                status: SolverDispatchStatus::Unsat,
                binary_artifact_digest_identity: Some(replay_grade_artifact_identity()),
                replay: ReplayStatus::Replayed,
                certificate: certificate.clone(),
                ..Default::default()
            }],
            proof_certificate: certificate,
            replay: ReplayStatus::Replayed,
            ..Default::default()
        }
    }

    fn validated_reconstruction() -> ReconstructionSummary {
        ReconstructionSummary {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            outputs: vec![DecompiledOutput {
                target: DecompileTarget::TrustIr,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    fn accepted_source_backpropagation_gate() -> BinarySourceBackpropagationGateDetails {
        BinarySourceBackpropagationGateDetails::evaluated(
            exact_source_provenance(),
            true,
            true,
            true,
            true,
            true,
            true,
        )
        .with_checked_source_provenance_binary_identity(replay_grade_artifact_identity())
    }

    fn wrong_binary_source_backpropagation_gate() -> BinarySourceBackpropagationGateDetails {
        let mut wrong_identity = replay_grade_artifact_identity();
        wrong_identity.selected_image.as_mut().expect("fixture has selected image").sha256 =
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".into();

        BinarySourceBackpropagationGateDetails::evaluated(
            exact_source_provenance(),
            true,
            true,
            true,
            true,
            true,
            true,
        )
        .with_checked_source_provenance_binary_identity(wrong_identity)
    }

    fn reconstruction_gate_reason() -> &'static str {
        "accepted reconstruction and target validation"
    }

    fn relift_verification_with_kind(kind: VcKind) -> BinaryVerificationSummary {
        BinaryVerificationSummary {
            total_vcs: 1,
            solver_dispatch: vec![SolverDispatchRecord {
                id: "relift-vc-000000".into(),
                solver: "trust_vcgen::relift".into(),
                vc_kind: Some(kind),
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    #[test]
    fn test_relift_backprop_evidence_match_accepts_same_source_and_vc_identity() {
        let source_provenance = exact_source_provenance();
        let mut verification = proof_grade_binary_verification();
        verification.solver_dispatch[0].vc_kind = Some(VcKind::DivisionByZero);
        let relift_verification = relift_verification_with_kind(VcKind::DivisionByZero);
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        validate_binary_backprop_evidence_matches_relift(
            &source_provenance,
            &relift_verification,
            evidence,
            "checked_from_binary",
        )
        .expect("matching relift evidence should pass the consistency check");
    }

    #[test]
    fn test_relift_backprop_evidence_match_rejects_source_provenance_mismatch() {
        let source_provenance = exact_source_provenance();
        let relift_source_provenance =
            BinarySourceProvenanceSummary { exact_mapping_count: 2, ..source_provenance.clone() };
        let mut verification = proof_grade_binary_verification();
        verification.solver_dispatch[0].vc_kind = Some(VcKind::DivisionByZero);
        let relift_verification = relift_verification_with_kind(VcKind::DivisionByZero);
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = validate_binary_backprop_evidence_matches_relift(
            &relift_source_provenance,
            &relift_verification,
            evidence,
            "checked_from_binary",
        )
        .expect_err("source provenance evidence must match the current relift");

        assert!(format!("{err}").contains("source provenance summary mismatch"));
    }

    #[test]
    fn test_relift_backprop_evidence_match_requires_vc_kind_identity() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let relift_verification = relift_verification_with_kind(VcKind::DivisionByZero);
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = validate_binary_backprop_evidence_matches_relift(
            &source_provenance,
            &relift_verification,
            evidence,
            "checked_from_binary",
        )
        .expect_err("missing VC kind identity must fail closed");

        assert!(format!("{err}").contains("VC kind identity is missing"));
    }

    #[test]
    fn test_apply_plan_empty_proposals() {
        let policy = GovernancePolicy::default();
        let plan = apply_plan(&[], &policy).expect("should succeed with empty proposals");
        assert!(plan.is_empty());
        assert_eq!(plan.len(), 0);
    }

    #[test]
    fn test_apply_plan_single_precondition() {
        let (_dir, path) = temp_source_file("fn get_midpoint(a: u64, b: u64) -> u64 { a + b }\n");
        let policy = GovernancePolicy::default();
        let proposals = vec![make_precondition_proposal_at(
            &path,
            "get_midpoint",
            "a + b < 18446744073709551615",
        )];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::InsertContractClause { clause: ContractClauseKind::Requires, .. }
        ));
    }

    #[test]
    fn test_apply_plan_safe_arithmetic() {
        let (_dir, path) = temp_source_file("fn get_midpoint(a: u64, b: u64) -> u64 { a + b }\n");
        let policy = GovernancePolicy::default();
        let proposals = vec![make_safe_arithmetic_proposal_at(&path, "get_midpoint")];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::ReplaceExpression { old_text, new_text }
                if old_text == "a + b" && new_text.contains("checked_add")
        ));
    }

    #[test]
    fn test_apply_plan_governance_blocks_pub_fn_strict() {
        let policy = GovernancePolicy {
            immutable_pub_signatures: true,
            immutable_tests: true,
            strict: true,
            protected_functions: vec!["get_midpoint".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposals = vec![make_precondition_proposal("get_midpoint", "x > 0")];
        let result = apply_plan(&proposals, &policy);
        assert!(result.is_err());
    }

    #[test]
    fn test_apply_plan_governance_skips_in_nonstrict() {
        let policy = GovernancePolicy {
            immutable_pub_signatures: true,
            immutable_tests: true,
            strict: false,
            protected_functions: vec!["get_midpoint".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposals = vec![make_precondition_proposal("get_midpoint", "x > 0")];
        let plan = apply_plan(&proposals, &policy).expect("should succeed in non-strict");
        assert!(plan.is_empty());
    }

    #[test]
    fn test_apply_plan_multiple_proposals() {
        let (_dir, path) = temp_source_file(
            "fn fn_a(x: u64) -> u64 { x }\n\
             fn fn_b(a: u64, b: u64) -> u64 { a + b }\n\
             fn fn_c(d: u64) -> u64 { 10 / d }\n",
        );
        let policy = GovernancePolicy::default();
        let proposals = vec![
            make_precondition_proposal_at(&path, "fn_a", "x > 0"),
            make_safe_arithmetic_proposal_at(&path, "fn_b"),
            Proposal {
                function_path: path.clone(),
                function_name: "fn_c".into(),
                kind: ProposalKind::AddBoundsCheck { check_expr: "assert!(i < v.len())".into() },
                confidence: 0.8,
                rationale: "bounds check".into(),
            },
        ];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 3);
    }

    #[test]
    fn test_apply_binary_derived_plan_requires_exact_source_provenance() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = BinarySourceProvenanceSummary::default();
        let verification = proof_grade_binary_verification();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err(
                "binary-derived proposals must fail closed without exact source provenance",
            );

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("accepted exact source provenance")
        ));
    }

    #[test]
    fn test_apply_binary_plan_rejects_address_only_path_without_source_gate() {
        let proposal =
            make_precondition_proposal_at("binary:0x401000", "recovered_entry", "arg0 != 0");
        let source_provenance = BinarySourceProvenanceSummary::default();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err(
                "address-only binary proposals must not become accepted rewrites from proof evidence alone",
            );

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { function, reason }
                if function == "recovered_entry"
                    && reason.contains("accepted exact source provenance")
                    && reason.contains("source_backpropagation_gate=missing")
        ));
    }

    #[test]
    fn test_binary_backprop_diagnostics_include_source_gate_provenance_details() {
        let source_provenance = BinarySourceProvenanceSummary {
            status: "exact".into(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["debug/source row is ambiguous".into()],
            source_backpropagation_allowed: true,
        };
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = BinarySourceBackpropagationGateDetails::closed_with_blockers(
            source_provenance.clone(),
            ["exact_source_provenance_missing", "source_provenance_not_effective"],
        );
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        let diagnostics = evidence.rejection_diagnostics();
        let provenance = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == "exact-source-provenance-missing")
            .expect("source provenance diagnostic");
        assert_eq!(provenance.category, "source_provenance");
        assert!(provenance.detail.contains("source_provenance.status=exact"));
        assert!(provenance.detail.contains("exact_mapping_count=0"));
        assert!(provenance.detail.contains("ambiguous_mapping_count=1"));
        assert!(provenance.detail.contains("debug/source row is ambiguous"));
        assert!(provenance.detail.contains("source_backpropagation_gate.blockers=exact_source_provenance_missing,source_provenance_not_effective"));

        let gate = diagnostics
            .iter()
            .find(|diagnostic| {
                diagnostic.code == "certificate-source-backpropagation-gate-rejected"
            })
            .expect("certificate source-backprop gate diagnostic");
        assert!(gate.detail.contains("source_backpropagation_allowed=false"));
        assert!(gate.detail.contains("exact_source_provenance_missing"));
    }

    #[test]
    fn test_apply_binary_derived_plan_rejects_partial_source_provenance() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = BinarySourceProvenanceSummary {
            status: "exact".into(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["ambiguous debug/source row withheld".into()],
            source_backpropagation_allowed: true,
        };
        let verification = proof_grade_binary_verification();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("partial provenance must fail closed");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("accepted exact source provenance")
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_requires_proof_grade_binary_evidence() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = BinaryVerificationSummary {
            trust_level: TrustLevel::Partial,
            ..proof_grade_binary_verification()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("binary-derived proposals must fail closed without proof-grade evidence");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("proof-grade binary verification evidence")
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_rejects_partial_binary_verification_counts() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = BinaryVerificationSummary {
            total_vcs: 2,
            proved: 1,
            unknown: 1,
            ..proof_grade_binary_verification()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("partial VC verification must fail closed");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("proof-grade binary verification evidence")
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_rejects_missing_replay() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = BinaryVerificationSummary {
            replay: ReplayStatus::NotAttempted,
            ..proof_grade_binary_verification()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("missing replay must fail closed");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("proof-grade binary verification evidence")
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_rejects_missing_checked_certificate() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = BinaryVerificationSummary {
            proof_certificate: ProofCertificateStatus::Present {
                format: "test-cert".into(),
                sha256: Some(
                    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
                ),
                artifact_path: Some("proof.lrat".into()),
            },
            ..proof_grade_binary_verification()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("present but unchecked certificate must fail closed");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("proof-grade binary verification evidence")
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_rejects_checked_certificate_without_production_evidence() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = BinaryVerificationSummary {
            proof_certificate: ProofCertificateStatus::Checked {
                checker: "test-checker".into(),
                format: "test-cert".into(),
                sha256: Some(
                    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
                ),
            },
            ..proof_grade_binary_verification()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("checked certificate without production evidence must fail closed");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("proof-grade binary verification evidence")
        ));
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_missing_reconstruction_validation() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains(reconstruction_gate_reason()) })
        );
        assert!(!binary_backprop_evidence_allows_source_rewrites(
            &source_provenance,
            &verification
        ));
    }

    #[test]
    fn test_binary_backprop_with_reconstruction_rejects_missing_source_backpropagation_gate() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let gate = &diagnostics[0];
        assert_eq!(gate.code, "certificate-source-backpropagation-gate-rejected");
        assert_eq!(gate.category, "checked_certificate_source_backpropagation_gate");
        assert!(gate.detail.contains("source_backpropagation_gate=missing"));
        assert!(
            gate.evidence_required.contains(&"checked_certificate_source_backpropagation_gate")
        );
        assert!(!binary_backprop_evidence_allows_source_rewrites_with_reconstruction(
            &source_provenance,
            &verification,
            &reconstruction
        ));
    }

    #[test]
    fn test_apply_binary_derived_plan_requires_with_reconstruction_even_when_binary_is_proof_grade()
    {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification);

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("with_reconstruction must be mandatory for binary-derived source rewrites");

        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains(reconstruction_gate_reason())
        ));
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_unvalidated_reconstruction() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = ReconstructionSummary {
            validation: ReconstructionValidationStatus::NotAttempted,
            ..validated_reconstruction()
        };
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains(reconstruction_gate_reason()) })
        );
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_target_validation_blockers() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let mut reconstruction = validated_reconstruction();
        reconstruction.outputs[0].target_validation_blockers.push(TargetValidationBlocker {
            target: DecompileTarget::TrustIr,
            function: Some("recovered".into()),
            code: "missing-target-semantic-validation".into(),
            stage: "trust-ir-bridge::target-validation".into(),
            feature: "missing-target-semantic-validation".into(),
            reason: "target validation did not consume reconstruction evidence".into(),
            origin: None,
            diagnostics: vec!["target_semantics_consumed=false".into()],
        });
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains(reconstruction_gate_reason()) })
        );
        let diagnostics = evidence.rejection_diagnostics();
        let reconstruction = diagnostics
            .iter()
            .find(|diagnostic| {
                diagnostic.code == "accepted-reconstruction-target-validation-missing"
            })
            .expect("reconstruction diagnostic");
        assert!(reconstruction.detail.contains("reconstruction.validation=Validated"));
        assert!(reconstruction.detail.contains("reconstruction.trust_level=ProofGrade"));
        assert!(reconstruction.detail.contains(
            "TrustIr:trust-ir-bridge::target-validation:missing-target-semantic-validation"
        ));
    }

    #[test]
    fn test_binary_backprop_with_reconstruction_rejects_partial_output_assumptions() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let mut reconstruction = validated_reconstruction();
        reconstruction.outputs[0].assumptions.push(ModelAssumption {
            stage: "hostile-review-fixture".into(),
            description: "partial reconstructed-output assumption".into(),
        });
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains(reconstruction_gate_reason()) })
        );
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_missing_replay_digest_identity() {
        let source_provenance = exact_source_provenance();
        let mut verification = proof_grade_binary_verification();
        verification.solver_dispatch[0].binary_artifact_digest_identity = None;
        let reconstruction = validated_reconstruction();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains("replay-grade binary artifact identity") })
        );
        let diagnostics = evidence.rejection_diagnostics();
        let replay = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == "replay-grade-artifact-identity-missing")
            .expect("replay identity diagnostic");
        assert!(replay.detail.contains("verification.replay=Replayed"));
        assert!(replay.detail.contains("dispatch_count=1"));
        assert!(replay.detail.contains("dispatches_missing_replay_grade_identity=test-vc"));
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_non_replay_grade_digest_identity() {
        let source_provenance = exact_source_provenance();
        let mut verification = proof_grade_binary_verification();
        verification.solver_dispatch[0]
            .binary_artifact_digest_identity
            .as_mut()
            .and_then(|identity| identity.selected_image.as_mut())
            .expect("selected image identity")
            .file_size = 0;
        let reconstruction = validated_reconstruction();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains("replay-grade binary artifact identity") })
        );
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_missing_dispatch_checked_certificate_identity() {
        let source_provenance = exact_source_provenance();
        let mut verification = proof_grade_binary_verification();
        verification.solver_dispatch[0].certificate = ProofCertificateStatus::Present {
            format: "test-cert".into(),
            sha256: Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()),
            artifact_path: Some("proof.lrat".into()),
        };
        let reconstruction = validated_reconstruction();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction);

        assert!(!evidence.allows_source_rewrite_planning());
        assert!(
            evidence
                .rejection_reasons()
                .iter()
                .any(|reason| { reason.contains("checked certificate identity") })
        );
        let diagnostics = evidence.rejection_diagnostics();
        let certificate = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == "checked-certificate-identity-missing")
            .expect("checked certificate diagnostic");
        assert!(certificate.detail.contains("summary_proof_certificate=checked"));
        assert!(
            certificate
                .detail
                .contains("dispatches_missing_checked_certificate_identity=test-vc:present")
        );
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_unconsumed_unsupported_ledger_with_source_gate() {
        let source_provenance = exact_source_provenance();
        let mut verification = proof_grade_binary_verification();
        verification.unsupported_ledger.records.push(UnsupportedRecord {
            stage: "lift".into(),
            architecture: Some("aarch64".into()),
            origin: None,
            opcode: Some("LDAXR".into()),
            operand: Some("w0, [x1]".into()),
            feature: "exclusive-monitor-boundary".into(),
        });
        let reconstruction = validated_reconstruction();
        let source_gate = accepted_source_backpropagation_gate();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        let verification = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == "proof-grade-binary-verification-missing")
            .expect("binary verification diagnostic");
        assert!(verification.detail.contains("unsupported_ledger_empty=false"));
        assert!(verification.detail.contains("unsupported_ledger_records=1"));
        assert!(verification.evidence_required.contains(&"unsupported_ledger_elimination"));
    }

    #[test]
    fn test_binary_backprop_evidence_consumes_certificate_source_backpropagation_gate_details() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = BinarySourceBackpropagationGateDetails::evaluated(
            source_provenance.clone(),
            true,
            true,
            true,
            true,
            false,
            true,
        );
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let gate = &diagnostics[0];
        assert_eq!(gate.code, "certificate-source-backpropagation-gate-rejected");
        assert!(gate.detail.contains("accepted_target_validation=false"));
        assert!(gate.detail.contains("accepted_target_validation_missing"));

        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("source_backpropagation_gate rejection must fail closed");
        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("certificate-source-backpropagation-gate-rejected")
                    && reason.contains("accepted_target_validation_missing")
        ));
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_source_gate_wrong_provenance_identity() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let mut source_gate = accepted_source_backpropagation_gate();
        source_gate.source_provenance.exact_mapping_count = 2;

        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        let gate = diagnostics
            .iter()
            .find(|diagnostic| {
                diagnostic.code == "certificate-source-backpropagation-gate-rejected"
            })
            .expect("certificate source-backprop gate diagnostic");
        assert!(gate.evidence_required.contains(&"checked_binary_source_provenance_identity"));
        assert!(gate.detail.contains("source_provenance_matches_runtime=false"));
        assert!(gate.detail.contains("gate_source_provenance_exact_mappings=2"));
        assert!(gate.detail.contains("runtime_source_provenance_exact_mappings=1"));
    }

    #[test]
    fn test_binary_backprop_evidence_rejects_source_gate_wrong_schema_version() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let mut source_gate = accepted_source_backpropagation_gate();
        source_gate.schema_version = "trust-proof-cert.source-backpropagation-gate.v0".into();

        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let gate = &diagnostics[0];
        assert_eq!(gate.code, "certificate-source-backpropagation-gate-rejected");
        assert!(
            gate.detail.contains(
                "source_backpropagation_gate.schema_version=trust-proof-cert.source-backpropagation-gate.v0"
            )
        );
        assert!(
            gate.detail.contains(
                "expected_schema_version=trust-proof-cert.source-backpropagation-gate.v1"
            )
        );
    }

    #[test]
    fn test_binary_backprop_rejects_missing_checked_source_provenance_import() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = BinarySourceBackpropagationGateDetails::evaluated(
            source_provenance.clone(),
            true,
            true,
            true,
            true,
            true,
            true,
        );
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        let gate = diagnostics
            .iter()
            .find(|diagnostic| {
                diagnostic.code == "certificate-source-backpropagation-gate-rejected"
            })
            .expect("certificate source-backprop gate diagnostic");
        assert!(gate.detail.contains("checked_source_provenance_binary_identity=missing"));
        assert!(gate.detail.contains("checked_source_provenance_binary_identity_missing"));

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("missing checked provenance import must block rewrite authority");
        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("certificate-source-backpropagation-gate-rejected")
                    && reason.contains("checked_source_provenance_binary_identity_missing")
        ));
    }

    #[test]
    fn test_binary_backprop_rejects_checked_source_provenance_for_wrong_binary() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = wrong_binary_source_backpropagation_gate();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(!evidence.allows_source_rewrite_planning());
        let diagnostics = evidence.rejection_diagnostics();
        let handoff = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == "checked-source-provenance-handoff-rejected")
            .expect("checked source provenance handoff diagnostic");
        assert_eq!(handoff.category, "checked_binary_source_provenance");
        assert!(handoff.detail.contains("checked_source_provenance_wrong_binary"));
        assert!(handoff.detail.contains("dispatch_id=test-vc"));
        assert!(handoff.evidence_required.contains(&"matching_binary_artifact_digest_identity"));

        let err = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect_err("checked source provenance imported for another binary must fail closed");
        assert!(matches!(
            err,
            RewriteError::UnsafeProvenance { reason, .. }
                if reason.contains("checked-source-provenance-handoff-rejected")
                    && reason.contains("checked_source_provenance_wrong_binary")
        ));
    }

    #[test]
    fn test_binary_backprop_evidence_accepts_certificate_source_backpropagation_gate() {
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = accepted_source_backpropagation_gate();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(evidence.allows_source_rewrite_planning());
        assert!(evidence.rejection_diagnostics().is_empty());
        assert_eq!(
            source_gate.checked_source_provenance_binary_identity.as_ref(),
            verification.solver_dispatch[0].binary_artifact_digest_identity.as_ref()
        );
        assert!(
            binary_backprop_evidence_allows_source_rewrites_with_reconstruction_and_source_gate(
                &source_provenance,
                &verification,
                &reconstruction,
                &source_gate
            )
        );
    }

    #[test]
    fn test_apply_binary_derived_plan_accepts_exact_source_with_full_source_gate_evidence() {
        let (_dir, path) = temp_source_file("fn recovered(x: u64) -> u64 { x }\n");
        let proposal = make_precondition_proposal_at(&path, "recovered", "x > 0");
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = accepted_source_backpropagation_gate();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        assert!(
            binary_backprop_evidence_allows_source_rewrites_with_reconstruction_and_source_gate(
                &source_provenance,
                &verification,
                &reconstruction,
                &source_gate
            )
        );
        let plan = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect("full binary source-backprop evidence should allow planning");

        assert_eq!(plan.len(), 1);
    }

    #[test]
    fn test_apply_binary_derived_plan_keeps_binary_pseudo_path_report_only() {
        let proposal =
            make_precondition_proposal_at("binary:0x401000", "recovered_entry", "arg0 != 0");
        let source_provenance = exact_source_provenance();
        let verification = proof_grade_binary_verification();
        let reconstruction = validated_reconstruction();
        let source_gate = accepted_source_backpropagation_gate();
        let evidence = BinaryBackpropEvidence::new(&source_provenance, &verification)
            .with_reconstruction(&reconstruction)
            .with_certificate_source_backpropagation_gate(&source_gate);

        let plan = apply_binary_derived_plan(&[proposal], &GovernancePolicy::default(), evidence)
            .expect("proof-grade evidence should not rewrite binary pseudo-paths");

        assert!(plan.is_empty());
    }

    #[test]
    fn test_rewrite_plan_sort_descending_offset() {
        let mut plan = RewritePlan::new("test");
        plan.rewrites = vec![
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 10,
                kind: RewriteKind::InsertAssertion { assertion: "first".into() },
                function_name: "f".into(),
                rationale: String::new(),
                expected_source_hash: None,
                provenance: ClaimProvenance::Authoritative,
            },
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 50,
                kind: RewriteKind::InsertAssertion { assertion: "second".into() },
                function_name: "f".into(),
                rationale: String::new(),
                expected_source_hash: None,
                provenance: ClaimProvenance::Authoritative,
            },
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 30,
                kind: RewriteKind::InsertAssertion { assertion: "third".into() },
                function_name: "f".into(),
                rationale: String::new(),
                expected_source_hash: None,
                provenance: ClaimProvenance::Authoritative,
            },
        ];
        plan.sort_for_application();

        // Should be sorted descending by offset within same file
        assert_eq!(plan.rewrites[0].offset, 50);
        assert_eq!(plan.rewrites[1].offset, 30);
        assert_eq!(plan.rewrites[2].offset, 10);
    }

    #[test]
    fn test_proposal_to_rewrites_postcondition() {
        let (_dir, path) = temp_source_file("fn f() -> i32 { 0 }\n");
        let proposal = Proposal {
            function_path: path,
            function_name: "f".into(),
            kind: ProposalKind::AddPostcondition { spec_body: "result >= 0".into() },
            confidence: 0.7,
            rationale: "test".into(),
        };
        let rewrites = proposal_to_rewrites(&proposal).unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertContractClause { clause: ContractClauseKind::Ensures, .. }
        ));
    }

    #[test]
    fn test_apply_plan_rejects_ambiguous_function_in_source_file() {
        let (_dir, path) =
            temp_source_file("mod left { fn helper() {} }\nmod right { fn helper() {} }\n");
        let proposal = make_precondition_proposal_at(&path, "helper", "true");

        let error = apply_plan(&[proposal], &GovernancePolicy::default()).unwrap_err();

        assert!(matches!(
            error,
            RewriteError::AmbiguousFunction { name, matches: 2, .. } if name == "helper"
        ));
    }

    #[test]
    fn test_proposal_to_rewrites_invariant() {
        let (_dir, path) = temp_source_file("fn f(n: usize) { for _i in 0..n {} }\n");
        let proposal = Proposal {
            function_path: path,
            function_name: "f".into(),
            kind: ProposalKind::AddInvariant { spec_body: "n <= 10".into() },
            confidence: 0.6,
            rationale: "test".into(),
        };
        assert!(matches!(
            proposal_to_rewrites(&proposal),
            Err(RewriteError::InvalidRewrite { reason, .. })
                if reason.contains("exact loop target")
        ));
    }

    #[test]
    fn test_proposal_to_rewrites_non_zero_check() {
        let (_dir, path) = temp_source_file("fn f(d: u64) -> u64 { 10 / d }\n");
        let proposal = Proposal {
            function_path: path,
            function_name: "f".into(),
            kind: ProposalKind::AddNonZeroCheck { check_expr: "assert!(d != 0)".into() },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let rewrites = proposal_to_rewrites(&proposal).unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("!= 0")
        ));
    }

    #[test]
    fn test_proposal_to_rewrites_skips_binary_function_path() {
        let proposal = Proposal {
            function_path: "binary::test_add".into(),
            function_name: "test_add".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "binary provenance is report-only".into(),
        };

        assert!(proposal_to_rewrites(&proposal).unwrap().is_empty());
    }

    #[test]
    fn test_proposal_to_rewrites_skips_binary_location_file_path() {
        let proposal = Proposal {
            function_path: "binary:0x1000".into(),
            function_name: "test_add".into(),
            kind: ProposalKind::AddPostcondition { spec_body: "result >= 0".into() },
            confidence: 0.9,
            rationale: "binary location is report-only".into(),
        };

        assert!(proposal_to_rewrites(&proposal).unwrap().is_empty());
    }

    #[test]
    fn test_proposal_to_rewrites_skips_binary_pseudo_path_without_address() {
        let proposal = Proposal {
            function_path: "binary:unmapped:test_add".into(),
            function_name: "test_add".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "binary provenance is report-only".into(),
        };

        assert!(proposal_to_rewrites(&proposal).unwrap().is_empty());
    }

    #[test]
    fn test_proposal_to_rewrites_skips_symbolic_pseudo_path_even_if_readable() {
        let dir = tempfile::tempdir().expect("create temp source dir");
        let pseudo_path = dir.path().join("crate::recovered.rs");
        std::fs::write(&pseudo_path, "fn recovered(x: u64) -> u64 { x }\n")
            .expect("write pseudo source path");
        let proposal = Proposal {
            function_path: pseudo_path.display().to_string(),
            function_name: "recovered".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "symbolic def-path provenance is report-only".into(),
        };

        assert!(proposal_to_rewrites(&proposal).unwrap().is_empty());
    }

    #[test]
    fn test_report_only_path_gate_does_not_reject_binary_search_source_file() {
        assert!(report_only_provenance_path_reason("src/binary_search.rs").is_none());
        assert!(report_only_provenance_path_reason("crate::module.rs").is_some());
        assert!(report_only_provenance_path_reason("decompiled://module.rs").is_some());
    }

    #[test]
    fn test_proposal_to_rewrites_rejects_unreadable_source_path() {
        let proposal = Proposal {
            function_path: "does/not/exist.rs".into(),
            function_name: "f".into(),
            kind: ProposalKind::AddNonZeroCheck { check_expr: "assert!(d != 0)".into() },
            confidence: 0.8,
            rationale: "unreadable source is report-only".into(),
        };

        assert!(matches!(proposal_to_rewrites(&proposal), Err(RewriteError::InvalidSource { .. })));
    }

    #[test]
    fn apply_plan_rejects_missing_function_in_readable_source() {
        let (_dir, path) = temp_source_file("fn present() {}\n");
        let proposal = make_precondition_proposal_at(&path, "missing", "true");
        assert!(matches!(
            apply_plan(&[proposal], &GovernancePolicy::default()),
            Err(RewriteError::SourceMismatch { .. })
        ));
    }

    #[test]
    fn apply_plan_rejects_english_contract_before_interpolation() {
        let (_dir, path) = temp_source_file("fn f(x: i32) {}\n");
        let proposal = make_precondition_proposal_at(&path, "f", "caller must ensure: x > 0");
        assert!(matches!(
            apply_plan(&[proposal], &GovernancePolicy::default()),
            Err(RewriteError::InvalidSpec { .. })
        ));
    }
}
