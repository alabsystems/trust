// trust-proof-cert chain verification
//
// CertificateChain: ordered list of steps from VC generation through solver proof.
// ChainValidator: validates hash linkage, ordering, gap detection.
// ChainSummary: aggregated statistics over a set of chains.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::CertError;

/// A single step in the certificate chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainStep {
    /// What this step represents (e.g. "vc_generation", "solver_proof", "clean_certification").
    pub step_type: ChainStepType,
    /// Tool/component that performed this step.
    pub tool: String,
    /// Tool version.
    pub tool_version: String,
    /// Input hash (SHA-256 of the input to this step).
    pub input_hash: String,
    /// Output hash (SHA-256 of the output of this step).
    pub output_hash: String,
    /// Time spent on this step in milliseconds.
    pub time_ms: u64,
    /// ISO 8601 timestamp.
    pub timestamp: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ChainStepType {
    /// Verification condition was generated from MIR.
    VcGeneration,
    /// Solver produced a proof/counterexample.
    SolverProof,
    /// clean kernel type-checked the proof term.
    CleanCertification,
    // Codegen lowering step — translation validation from MIR to machine code.
    /// trust_cg backend lowered MIR to machine code with translation validation.
    CodegenLowering,
}

impl ChainStepType {
    /// Expected ordering index for well-formed chains.
    /// Lower values must appear before higher values.
    fn ordering_rank(self) -> u8 {
        match self {
            ChainStepType::VcGeneration => 0,
            ChainStepType::SolverProof => 1,
            ChainStepType::CleanCertification => 2,
            // Codegen lowering comes after solver proof in the pipeline.
            ChainStepType::CodegenLowering => 3,
        }
    }
}

/// A certificate chain records each step from VC generation through
/// solver proof to optional clean certification. Each step's output_hash
/// must match the next step's input_hash.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateChain {
    /// Ordered steps in the chain.
    pub steps: Vec<ChainStep>,
}

impl CertificateChain {
    /// Create a new empty chain.
    pub fn new() -> Self {
        CertificateChain { steps: Vec::new() }
    }

    /// Add a step to the chain.
    pub fn push(&mut self, step: ChainStep) {
        self.steps.push(step);
    }

    /// Verify the chain integrity: each step's output_hash matches the next
    /// step's input_hash.
    pub fn verify_integrity(&self) -> Result<(), CertError> {
        if self.steps.is_empty() {
            return Err(CertError::ChainIntegrityFailure {
                step: 0,
                reason: "empty chain has no provenance record".to_string(),
            });
        }

        for i in 0..self.steps.len().saturating_sub(1) {
            if self.steps[i].output_hash != self.steps[i + 1].input_hash {
                return Err(CertError::ChainIntegrityFailure {
                    step: i,
                    reason: format!(
                        "step {} output hash ({}) != step {} input hash ({})",
                        i,
                        self.steps[i].output_hash,
                        i + 1,
                        self.steps[i + 1].input_hash,
                    ),
                });
            }
        }
        Ok(())
    }

    /// Returns true if the chain contains a clean certification step.
    pub fn is_clean_certified(&self) -> bool {
        self.steps.iter().any(|s| s.step_type == ChainStepType::CleanCertification)
    }

    /// Returns the number of steps.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Returns true if the chain has no steps.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Total time across all steps in milliseconds.
    pub fn total_time_ms(&self) -> u64 {
        self.steps.iter().map(|s| s.time_ms).sum()
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }
}

impl Default for CertificateChain {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// ChainValidator: full validation with detailed diagnostics
// ---------------------------------------------------------------------------

/// A single finding from chain validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainFinding {
    /// Which step (or gap between steps) caused this finding.
    pub step_index: usize,
    /// What category of problem was found.
    pub kind: ChainFindingKind,
    /// Human-readable description.
    pub detail: String,
}

/// Categories of chain validation findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChainFindingKind {
    /// output_hash of step N does not match input_hash of step N+1.
    HashMismatch,
    /// Steps are in wrong order (e.g. SolverProof before VcGeneration).
    OutOfOrder,
    /// A required step type is missing (e.g. no VcGeneration).
    MissingStep,
    /// The chain is completely empty.
    EmptyChain,
    /// Duplicate step type in chain.
    DuplicateStep,
}

/// Result of validating a certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainValidationResult {
    /// Whether the chain passed all validation checks.
    pub valid: bool,
    /// Individual findings (empty if valid).
    pub findings: Vec<ChainFinding>,
}

impl ChainValidationResult {
    fn new() -> Self {
        ChainValidationResult { valid: true, findings: Vec::new() }
    }

    fn add_finding(&mut self, step_index: usize, kind: ChainFindingKind, detail: String) {
        self.valid = false;
        self.findings.push(ChainFinding { step_index, kind, detail });
    }
}

/// Validates certificate chains with detailed diagnostics.
///
/// Performs the following checks:
/// 1. Chain is non-empty
/// 2. Hash linkage: each step's output_hash matches the next step's input_hash
/// 3. Ordering: step types appear in valid order (VcGeneration < SolverProof < CleanCertification)
/// 4. Gap detection: required VcGeneration step is present
/// 5. No duplicate step types
pub struct ChainValidator;

impl ChainValidator {
    /// Validate a certificate chain with detailed findings.
    pub fn validate(chain: &CertificateChain) -> ChainValidationResult {
        let mut result = ChainValidationResult::new();

        // Check 1: non-empty
        if chain.is_empty() {
            result.add_finding(0, ChainFindingKind::EmptyChain, "chain has no steps".to_string());
            return result;
        }

        // Check 2: hash linkage
        for i in 0..chain.steps.len().saturating_sub(1) {
            if chain.steps[i].output_hash != chain.steps[i + 1].input_hash {
                result.add_finding(
                    i,
                    ChainFindingKind::HashMismatch,
                    format!(
                        "step {} output hash ({}) != step {} input hash ({})",
                        i,
                        chain.steps[i].output_hash,
                        i + 1,
                        chain.steps[i + 1].input_hash,
                    ),
                );
            }
        }

        // Check 3: ordering — each step type must have a rank >= the previous
        for i in 1..chain.steps.len() {
            let prev_rank = chain.steps[i - 1].step_type.ordering_rank();
            let curr_rank = chain.steps[i].step_type.ordering_rank();
            if curr_rank < prev_rank {
                result.add_finding(
                    i,
                    ChainFindingKind::OutOfOrder,
                    format!(
                        "step {} ({:?}, rank {}) appears after step {} ({:?}, rank {})",
                        i,
                        chain.steps[i].step_type,
                        curr_rank,
                        i - 1,
                        chain.steps[i - 1].step_type,
                        prev_rank,
                    ),
                );
            }
        }

        // Check 4: gap detection — VcGeneration should be present as the first step
        let has_vc_gen = chain.steps.iter().any(|s| s.step_type == ChainStepType::VcGeneration);
        if !has_vc_gen {
            result.add_finding(
                0,
                ChainFindingKind::MissingStep,
                "chain is missing VcGeneration step".to_string(),
            );
        }

        // Check 5: no duplicate step types
        // 4 step types now (VcGeneration, SolverProof, CleanCertification, CodegenLowering).
        let mut seen = [false; 4];
        for (i, step) in chain.steps.iter().enumerate() {
            let rank = step.step_type.ordering_rank() as usize;
            if seen[rank] {
                result.add_finding(
                    i,
                    ChainFindingKind::DuplicateStep,
                    format!("duplicate step type {:?} at index {i}", step.step_type),
                );
            }
            seen[rank] = true;
        }

        result
    }

    /// Convenience: validate and return a Result for simple pass/fail usage.
    pub fn validate_chain(chain: &CertificateChain) -> Result<ChainValidationResult, CertError> {
        let result = Self::validate(chain);
        if !result.valid {
            let reasons: Vec<String> = result.findings.iter().map(|f| f.detail.clone()).collect();
            return Err(CertError::ChainValidationFailed { reason: reasons.join("; ") });
        }
        Ok(result)
    }
}

// ---------------------------------------------------------------------------
// ChainSummary: aggregate statistics over multiple chains
// ---------------------------------------------------------------------------

/// Aggregated statistics over a set of certificate chains for a function or crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainSummary {
    /// Total number of VCs (one per chain).
    pub total_vcs: usize,
    /// Number of VCs that have a solver proof step.
    pub proved: usize,
    /// Number of VCs that have a clean certification step.
    pub certified: usize,
    /// Number of chains that passed full validation.
    pub valid_chains: usize,
    /// Number of chains that failed validation.
    pub invalid_chains: usize,
}

impl ChainSummary {
    /// Build a summary from a slice of chains.
    pub fn from_chains(chains: &[&CertificateChain]) -> Self {
        let total_vcs = chains.len();
        let mut proved = 0;
        let mut certified = 0;
        let mut valid_chains = 0;
        let mut invalid_chains = 0;

        for chain in chains {
            let has_solver = chain.steps.iter().any(|s| s.step_type == ChainStepType::SolverProof);
            let has_clean = chain.is_clean_certified();

            if has_solver {
                proved += 1;
            }
            if has_clean {
                certified += 1;
            }

            let validation = ChainValidator::validate(chain);
            if validation.valid {
                valid_chains += 1;
            } else {
                invalid_chains += 1;
            }
        }

        ChainSummary { total_vcs, proved, certified, valid_chains, invalid_chains }
    }

    /// Coverage percentage: what fraction of VCs have been proved (0.0 - 100.0).
    pub fn coverage_percent(&self) -> f64 {
        if self.total_vcs == 0 {
            return 0.0;
        }
        (self.proved as f64 / self.total_vcs as f64) * 100.0
    }

    /// Certification percentage: what fraction of VCs are clean-certified (0.0 - 100.0).
    pub fn certification_percent(&self) -> f64 {
        if self.total_vcs == 0 {
            return 0.0;
        }
        (self.certified as f64 / self.total_vcs as f64) * 100.0
    }
}

// ---------------------------------------------------------------------------
// Tests: ChainValidator, CertificateChain, ChainSummary
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a ChainStep with the given type and matching hashes.
    fn step(step_type: ChainStepType, input: &str, output: &str) -> ChainStep {
        ChainStep {
            step_type,
            tool: "test-tool".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: input.to_string(),
            output_hash: output.to_string(),
            time_ms: 10,
            timestamp: "2026-04-13T00:00:00Z".to_string(),
        }
    }

    /// Build a valid 3-step chain: VcGeneration -> SolverProof -> CleanCertification.
    fn valid_full_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "bbb", "ccc"));
        chain.push(step(ChainStepType::CleanCertification, "ccc", "ddd"));
        chain
    }

    /// Build a valid 2-step chain: VcGeneration -> SolverProof.
    fn valid_two_step_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "bbb", "ccc"));
        chain
    }

    // -----------------------------------------------------------------------
    // CertificateChain basic operations
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_new_is_empty() {
        let chain = CertificateChain::new();
        assert!(chain.is_empty());
        assert_eq!(chain.len(), 0);
        assert_eq!(chain.total_time_ms(), 0);
        assert!(!chain.is_clean_certified());
    }

    #[test]
    fn test_chain_default_is_empty() {
        let chain = CertificateChain::default();
        assert!(chain.is_empty());
    }

    #[test]
    fn test_chain_push_increments_len() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "a", "b"));
        assert_eq!(chain.len(), 1);
        assert!(!chain.is_empty());
    }

    #[test]
    fn test_chain_total_time_ms() {
        let chain = valid_full_chain();
        assert_eq!(chain.total_time_ms(), 30); // 3 steps x 10ms each
    }

    #[test]
    fn test_chain_is_clean_certified_true() {
        let chain = valid_full_chain();
        assert!(chain.is_clean_certified());
    }

    #[test]
    fn test_chain_is_clean_certified_false() {
        let chain = valid_two_step_chain();
        assert!(!chain.is_clean_certified());
    }

    // -----------------------------------------------------------------------
    // CertificateChain::verify_integrity
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_integrity_valid_chain_passes() {
        let chain = valid_full_chain();
        chain.verify_integrity().expect("valid chain should pass integrity check");
    }

    #[test]
    fn test_verify_integrity_valid_two_step_passes() {
        let chain = valid_two_step_chain();
        chain.verify_integrity().expect("valid 2-step chain should pass");
    }

    #[test]
    fn test_verify_integrity_single_step_passes() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.verify_integrity().expect("single-step chain should pass");
    }

    #[test]
    fn test_verify_integrity_empty_chain_fails() {
        let chain = CertificateChain::new();
        let err = chain.verify_integrity().expect_err("empty chain should fail integrity check");
        match err {
            CertError::ChainIntegrityFailure { step, reason } => {
                assert_eq!(step, 0);
                assert!(reason.contains("empty"));
            }
            other => panic!("expected ChainIntegrityFailure, got: {other:?}"),
        }
    }

    #[test]
    fn test_verify_integrity_mismatched_hashes_fails() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "WRONG", "ccc"));

        let err = chain.verify_integrity().expect_err("mismatched hashes should fail");
        match err {
            CertError::ChainIntegrityFailure { step, reason } => {
                assert_eq!(step, 0);
                assert!(reason.contains("bbb"), "reason should mention expected hash: {reason}");
                assert!(reason.contains("WRONG"), "reason should mention actual hash: {reason}");
            }
            other => panic!("expected ChainIntegrityFailure, got: {other:?}"),
        }
    }

    #[test]
    fn test_verify_integrity_second_link_mismatched() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "bbb", "ccc"));
        chain.push(step(ChainStepType::CleanCertification, "WRONG", "ddd"));

        let err = chain.verify_integrity().expect_err("second link mismatch should fail");
        match err {
            CertError::ChainIntegrityFailure { step, .. } => {
                assert_eq!(step, 1, "failure should be at step 1 (the link between step 1 and 2)");
            }
            other => panic!("expected ChainIntegrityFailure, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — valid chains
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_valid_full_chain_passes() {
        let chain = valid_full_chain();
        let result = ChainValidator::validate(&chain);
        assert!(result.valid, "valid full chain should pass: {result:?}");
        assert!(result.findings.is_empty());
    }

    #[test]
    fn test_validator_valid_two_step_chain_passes() {
        let chain = valid_two_step_chain();
        let result = ChainValidator::validate(&chain);
        assert!(result.valid, "valid 2-step chain should pass: {result:?}");
    }

    #[test]
    fn test_validator_single_vc_gen_step_passes() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        let result = ChainValidator::validate(&chain);
        assert!(result.valid, "single VcGeneration step should pass: {result:?}");
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — empty chain
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_empty_chain_fails() {
        let chain = CertificateChain::new();
        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert_eq!(result.findings.len(), 1);
        assert_eq!(result.findings[0].kind, ChainFindingKind::EmptyChain);
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — hash mismatch
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_hash_mismatch_detected() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "WRONG", "ccc"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let hash_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::HashMismatch).collect();
        assert_eq!(hash_findings.len(), 1, "should have exactly one hash mismatch finding");
        assert_eq!(hash_findings[0].step_index, 0);
    }

    #[test]
    fn test_validator_multiple_hash_mismatches() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "WRONG1", "ccc"));
        chain.push(step(ChainStepType::CleanCertification, "WRONG2", "ddd"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let hash_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::HashMismatch).collect();
        assert_eq!(hash_findings.len(), 2, "should detect both hash mismatches");
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — wrong step ordering
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_out_of_order_detected() {
        let mut chain = CertificateChain::new();
        // SolverProof before VcGeneration — wrong order
        chain.push(step(ChainStepType::SolverProof, "aaa", "bbb"));
        chain.push(step(ChainStepType::VcGeneration, "bbb", "ccc"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let order_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::OutOfOrder).collect();
        assert!(!order_findings.is_empty(), "should detect out-of-order steps");
    }

    #[test]
    fn test_validator_clean_before_solver_out_of_order() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::CleanCertification, "bbb", "ccc"));
        chain.push(step(ChainStepType::SolverProof, "ccc", "ddd"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let order_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::OutOfOrder).collect();
        assert!(!order_findings.is_empty(), "Clean before Solver should be out of order");
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — missing VcGeneration step
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_missing_vc_generation_detected() {
        let mut chain = CertificateChain::new();
        // Only solver proof, no VcGeneration
        chain.push(step(ChainStepType::SolverProof, "aaa", "bbb"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let missing_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::MissingStep).collect();
        assert!(!missing_findings.is_empty(), "should detect missing VcGeneration");
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — duplicate step types
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_duplicate_step_type_detected() {
        let mut chain = CertificateChain::new();
        chain.push(step(ChainStepType::VcGeneration, "aaa", "bbb"));
        chain.push(step(ChainStepType::VcGeneration, "bbb", "ccc"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        let dup_findings: Vec<_> =
            result.findings.iter().filter(|f| f.kind == ChainFindingKind::DuplicateStep).collect();
        assert!(!dup_findings.is_empty(), "should detect duplicate VcGeneration");
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate — combined findings
    // -----------------------------------------------------------------------

    #[test]
    fn test_validator_multiple_findings_combined() {
        let mut chain = CertificateChain::new();
        // Out of order + hash mismatch + missing VcGeneration
        chain.push(step(ChainStepType::CleanCertification, "aaa", "bbb"));
        chain.push(step(ChainStepType::SolverProof, "WRONG", "ccc"));

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        // Should have: hash mismatch, out of order, and missing VcGeneration
        assert!(
            result.findings.len() >= 3,
            "should have at least 3 findings, got: {:?}",
            result.findings
        );
    }

    // -----------------------------------------------------------------------
    // ChainValidator::validate_chain (Result-returning convenience)
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_chain_ok_for_valid() {
        let chain = valid_full_chain();
        let result = ChainValidator::validate_chain(&chain).expect("valid chain should return Ok");
        assert!(result.valid);
    }

    #[test]
    fn test_validate_chain_err_for_invalid() {
        let chain = CertificateChain::new();
        let err =
            ChainValidator::validate_chain(&chain).expect_err("empty chain should return Err");
        match err {
            CertError::ChainValidationFailed { reason } => {
                assert!(reason.contains("no steps"), "reason should mention empty chain: {reason}");
            }
            other => panic!("expected ChainValidationFailed, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // ChainStepType::ordering_rank
    // -----------------------------------------------------------------------

    #[test]
    fn test_ordering_rank_monotonic() {
        assert!(
            ChainStepType::VcGeneration.ordering_rank()
                < ChainStepType::SolverProof.ordering_rank()
        );
        assert!(
            ChainStepType::SolverProof.ordering_rank()
                < ChainStepType::CleanCertification.ordering_rank()
        );
    }

    // -----------------------------------------------------------------------
    // CertificateChain JSON roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_json_roundtrip() {
        let chain = valid_full_chain();
        let json = chain.to_json().expect("should serialize to JSON");
        let recovered = CertificateChain::from_json(&json).expect("should deserialize from JSON");
        assert_eq!(chain, recovered);
    }

    #[test]
    fn test_chain_json_roundtrip_empty() {
        let chain = CertificateChain::new();
        let json = chain.to_json().expect("empty chain should serialize");
        let recovered = CertificateChain::from_json(&json).expect("should deserialize");
        assert_eq!(chain, recovered);
    }

    // -----------------------------------------------------------------------
    // ChainSummary
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_summary_from_valid_chains() {
        let c1 = valid_full_chain();
        let c2 = valid_two_step_chain();
        let chains: Vec<&CertificateChain> = vec![&c1, &c2];
        let summary = ChainSummary::from_chains(&chains);

        assert_eq!(summary.total_vcs, 2);
        assert_eq!(summary.proved, 2); // both have SolverProof
        assert_eq!(summary.certified, 1); // only c1 has CleanCertification
        assert_eq!(summary.valid_chains, 2); // both pass validation
        assert_eq!(summary.invalid_chains, 0);
    }

    #[test]
    fn test_chain_summary_coverage_percent() {
        let c1 = valid_full_chain();
        let chains: Vec<&CertificateChain> = vec![&c1];
        let summary = ChainSummary::from_chains(&chains);
        assert!((summary.coverage_percent() - 100.0).abs() < f64::EPSILON);
        assert!((summary.certification_percent() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_chain_summary_empty() {
        let chains: Vec<&CertificateChain> = vec![];
        let summary = ChainSummary::from_chains(&chains);
        assert_eq!(summary.total_vcs, 0);
        assert!((summary.coverage_percent() - 0.0).abs() < f64::EPSILON);
        assert!((summary.certification_percent() - 0.0).abs() < f64::EPSILON);
    }
}
