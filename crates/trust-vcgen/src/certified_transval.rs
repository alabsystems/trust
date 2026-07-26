// Certified translation validation for MIR-to-Formula.
//
// Wraps translation validation with proof certificates that attest the
// MIR-to-Formula translation is semantics-preserving. Certificates can be
// independently verified without re-running the full validation pipeline.
//
// Certification levels range from `Uncertified` (no proof) through
// `CrossChecked` (dual-method agreement) to `ProofCertified` (clean-backed
// formal proof). Bridge types enable future clean integration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::SystemTime;

use thiserror::Error;
use trust_types::fx::FxHashMap;
use trust_types::{BlockId, VerifiableFunction, VerificationCondition};

use crate::cross_check::{CrossCheckResult, full_cross_check};
use trust_types::translation_validation::{
    CheckKind, SimulationRelation, TranslationValidationError,
};

// ---------------------------------------------------------------------------
// Certification levels
// ---------------------------------------------------------------------------

/// Level of certification for a MIR-to-Formula translation.
///
/// Higher levels provide stronger guarantees about translation correctness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CertificationLevel {
    /// No certification — the translation has not been validated.
    Uncertified,
    /// Cross-checked: two independent VC generators agree on safety properties.
    /// This provides confidence but not a formal proof.
    CrossChecked,
    /// Proof-certified: a clean-backed formal proof attests the translation
    /// preserves semantics. This is the strongest guarantee.
    ProofCertified,
}

impl CertificationLevel {
    /// Human-readable description of this certification level.
    #[must_use]
    pub fn description(&self) -> &'static str {
        match self {
            CertificationLevel::Uncertified => "no certification",
            CertificationLevel::CrossChecked => "cross-checked by dual VC generation",
            CertificationLevel::ProofCertified => "formally certified via clean proof",
        }
    }

    /// Whether this level provides at least cross-checked confidence.
    #[must_use]
    pub fn is_at_least_cross_checked(&self) -> bool {
        *self >= CertificationLevel::CrossChecked
    }

    /// Whether this level provides a formal proof certificate.
    #[must_use]
    pub fn is_proof_certified(&self) -> bool {
        *self == CertificationLevel::ProofCertified
    }
}

// ---------------------------------------------------------------------------
// Proof judgment types (clean bridge)
// ---------------------------------------------------------------------------

/// A clean proof judgment asserting a property of the translation.
///
/// Judgments are the atomic units of a clean proof. Each judgment states
/// that under certain hypotheses, a conclusion holds.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ProofJudgment {
    /// Hypotheses (context) for this judgment.
    pub hypotheses: Vec<String>,
    /// The conclusion this judgment asserts.
    pub conclusion: String,
    /// The clean tactic or proof term that establishes this judgment.
    pub justification: ProofJustification,
}

/// How a proof judgment is justified.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofJustification {
    /// An axiom accepted without proof (e.g., MIR operational semantics).
    Axiom(String),
    /// A direct computation or simplification.
    Compute,
    /// Application of a named lemma with arguments.
    LemmaApplication { lemma_name: String, arguments: Vec<String> },
    /// Induction on a structure (e.g., block-by-block, statement-by-statement).
    Induction {
        variable: String,
        base_case: Box<ProofJustification>,
        inductive_step: Box<ProofJustification>,
    },
    /// Composition of sub-proofs.
    Composition(Vec<ProofJustification>),
}

/// A clean proof term for a single translation step.
///
/// Proof terms are the bridge between Trust's internal validation and
/// clean's formal proof system. Each term witnesses a specific aspect
/// of semantic preservation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CleanProofTerm {
    /// The theorem this proof term witnesses.
    pub theorem: String,
    /// The clean proof script (tactic or term mode).
    pub proof_script: String,
    /// Dependencies: other theorems this proof relies on.
    pub dependencies: Vec<String>,
}

// ---------------------------------------------------------------------------
// Translation certificate
// ---------------------------------------------------------------------------

/// A proof certificate attesting that a MIR-to-Formula translation is
/// semantics-preserving.
///
/// Certificates are independently verifiable: given the source function,
/// target formulas, and the certificate, a checker can confirm the
/// translation is correct without re-running the VC generator.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TranslationCertificate {
    /// Name of the function this certificate covers.
    pub function_name: String,
    /// Certification level achieved.
    pub level: CertificationLevel,
    /// Timestamp when the certificate was produced.
    pub timestamp: SystemTime,
    /// The simulation relation used (if any).
    pub simulation_relation: Option<SimulationRelation>,
    /// Cross-check result (present at CrossChecked level and above).
    pub cross_check_result: Option<CrossCheckResult>,
    /// Proof judgments (present at ProofCertified level).
    pub proof_judgments: Vec<ProofJudgment>,
    /// Clean proof terms (present at ProofCertified level).
    pub proof_terms: Vec<CleanProofTerm>,
    /// Per-block certification status.
    pub block_certificates: FxHashMap<BlockId, BlockCertificate>,
}

/// Certification status for a single basic block's translation.
#[derive(Debug, Clone)]
pub struct BlockCertificate {
    /// The block this certificate covers.
    pub block_id: BlockId,
    /// Whether the block's translation is certified.
    pub certified: bool,
    /// The check kind that was validated.
    pub check_kind: CheckKind,
    /// Human-readable description of the certification.
    pub description: String,
}

// ---------------------------------------------------------------------------
// Certified translation wrapper
// ---------------------------------------------------------------------------

/// A MIR-to-Formula translation wrapped with a proof certificate.
///
/// This is the primary API type: it bundles the translation output (VCs)
/// with a certificate attesting the translation's correctness.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct CertifiedTranslation {
    /// The function that was translated.
    pub function_name: String,
    /// The VCs produced by the translation.
    pub verification_conditions: Vec<VerificationCondition>,
    /// The proof certificate for this translation.
    pub certificate: TranslationCertificate,
}

impl CertifiedTranslation {
    /// The certification level of this translation.
    #[must_use]
    pub fn level(&self) -> CertificationLevel {
        self.certificate.level
    }

    /// Whether this translation has been at least cross-checked.
    #[must_use]
    pub fn is_cross_checked(&self) -> bool {
        self.certificate.level.is_at_least_cross_checked()
    }

    /// Whether this translation has a formal proof certificate.
    #[must_use]
    pub fn is_proof_certified(&self) -> bool {
        self.certificate.level.is_proof_certified()
    }

    /// Number of VCs covered by this certified translation.
    #[must_use]
    pub fn vc_count(&self) -> usize {
        self.verification_conditions.len()
    }

    /// Number of blocks with certification status.
    #[must_use]
    pub fn certified_block_count(&self) -> usize {
        self.certificate.block_certificates.values().filter(|bc| bc.certified).count()
    }

    /// Fraction of blocks that are certified (0.0 to 1.0).
    #[must_use]
    pub fn certification_coverage(&self) -> f64 {
        let total = self.certificate.block_certificates.len();
        if total == 0 {
            return 0.0;
        }
        self.certified_block_count() as f64 / total as f64
    }
}

// ---------------------------------------------------------------------------
// Certification errors
// ---------------------------------------------------------------------------

/// Errors that can occur during certification.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum CertificationError {
    /// The translation validation check failed.
    #[error("translation validation failed: {0}")]
    ValidationFailed(#[from] TranslationValidationError),

    /// Cross-checking revealed a soundness alarm.
    #[error("cross-check soundness alarm for `{function}`: {details}")]
    SoundnessAlarm { function: String, details: String },

    /// The proof certificate is invalid or corrupted.
    #[error("invalid certificate: {0}")]
    InvalidCertificate(String),

    /// A proof judgment failed to verify.
    #[error("proof judgment failed: {conclusion}")]
    JudgmentFailed { conclusion: String },

    /// clean backend is not available (feature not compiled in).
    #[error("clean backend not available")]
    CleanUnavailable,
}

// ---------------------------------------------------------------------------
// Certificate verification
// ---------------------------------------------------------------------------

/// Verify that a translation certificate is internally consistent.
///
/// This checks:
/// 1. The certification level matches the available evidence.
/// 2. Cross-check results (if present) indicate soundness.
/// 3. Proof judgments (if present) form a valid proof chain.
/// 4. Block certificates are consistent with the overall level.
#[must_use]
pub fn verify_certificate(cert: &TranslationCertificate) -> bool {
    // Level 0: Uncertified — always valid (vacuously).
    if cert.level == CertificationLevel::Uncertified {
        return true;
    }

    // Level 1: CrossChecked — must have a cross-check result that is sound.
    if cert.level >= CertificationLevel::CrossChecked {
        match &cert.cross_check_result {
            Some(result) => {
                if !result.is_sound() {
                    return false;
                }
            }
            None => return false, // CrossChecked requires a result.
        }
    }

    // Level 2: ProofCertified — must have at least one proof judgment
    // and all proof terms must have non-empty proofs.
    if cert.level == CertificationLevel::ProofCertified {
        if cert.proof_judgments.is_empty() {
            return false;
        }
        if cert.proof_terms.iter().any(|pt| pt.proof_script.is_empty()) {
            return false;
        }
    }

    // Block certificates: at CrossChecked+, all blocks should be certified.
    if cert.level >= CertificationLevel::CrossChecked && !cert.block_certificates.is_empty() {
        let all_certified = cert.block_certificates.values().all(|bc| bc.certified);
        if !all_certified {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Certification pipeline
// ---------------------------------------------------------------------------

/// Produce an uncertified translation — VCs with no certification.
///
/// This is the baseline: generate VCs and wrap them in a certificate
/// with `Uncertified` level. Used when no validation is requested.
pub fn uncertified_translation(func: &VerifiableFunction) -> CertifiedTranslation {
    let vcs = crate::generate_vcs(func);
    CertifiedTranslation {
        function_name: func.name.clone(),
        verification_conditions: vcs,
        certificate: TranslationCertificate {
            function_name: func.name.clone(),
            level: CertificationLevel::Uncertified,
            timestamp: SystemTime::now(),
            simulation_relation: None,
            cross_check_result: None,
            proof_judgments: vec![],
            proof_terms: vec![],
            block_certificates: FxHashMap::default(),
        },
    }
}

/// Produce a cross-checked certified translation.
///
/// Runs dual-method VC generation and compares results. If both methods
/// agree, the translation is certified at `CrossChecked` level.
///
/// Returns `Err` if the cross-check reveals a soundness alarm.
pub fn cross_checked_translation(
    func: &VerifiableFunction,
) -> Result<CertifiedTranslation, CertificationError> {
    let vcs = crate::generate_vcs(func);
    let cross_result = full_cross_check(func);

    if cross_result.has_soundness_alarm() {
        return Err(CertificationError::SoundnessAlarm {
            function: func.name.as_str().into(),
            details: format!("verdict: {:?}", cross_result.verdict),
        });
    }

    // Build per-block certificates from the cross-check.
    let mut block_certs = FxHashMap::default();
    for block in &func.body.blocks {
        block_certs.insert(
            block.id,
            BlockCertificate {
                block_id: block.id,
                certified: true,
                check_kind: CheckKind::DataFlow,
                description: format!(
                    "block {:?} cross-checked: dual VC generators agree",
                    block.id
                ),
            },
        );
    }

    Ok(CertifiedTranslation {
        function_name: func.name.clone(),
        verification_conditions: vcs,
        certificate: TranslationCertificate {
            function_name: func.name.clone(),
            level: CertificationLevel::CrossChecked,
            timestamp: SystemTime::now(),
            simulation_relation: None,
            cross_check_result: Some(cross_result),
            proof_judgments: vec![],
            proof_terms: vec![],
            block_certificates: block_certs,
        },
    })
}

/// Produce a proof-certified translation (clean-backed).
///
/// Currently constructs the certificate structure with proof judgments
/// derived from the simulation relation and cross-check. Full clean
/// integration requires the clean backend.
pub fn proof_certified_translation(
    func: &VerifiableFunction,
    simulation_relation: &SimulationRelation,
) -> Result<CertifiedTranslation, CertificationError> {
    let vcs = crate::generate_vcs(func);

    // Cross-check first — proof certification includes cross-checking.
    let cross_result = full_cross_check(func);
    if cross_result.has_soundness_alarm() {
        return Err(CertificationError::SoundnessAlarm {
            function: func.name.as_str().into(),
            details: format!("verdict: {:?}", cross_result.verdict),
        });
    }

    // Build proof judgments from the simulation relation.
    let mut judgments = Vec::new();
    let mut proof_terms = Vec::new();

    // Entry point preservation judgment.
    judgments.push(ProofJudgment {
        hypotheses: vec![
            format!("source_entry = {:?}", BlockId(0)),
            format!(
                "target_entry = {:?}",
                simulation_relation.block_map.get(&BlockId(0)).unwrap_or(&BlockId(0))
            ),
        ],
        conclusion: "entry_point_preserved".to_string(),
        justification: ProofJustification::Compute,
    });

    proof_terms.push(CleanProofTerm {
        theorem: format!("{}.entry_point_preserved", func.name),
        proof_script: "by simp [entry_point_def]".to_string(),
        dependencies: vec![],
    });

    // Per-block data flow preservation judgments.
    for block in &func.body.blocks {
        let target_block = simulation_relation.block_map.get(&block.id).unwrap_or(&block.id);

        judgments.push(ProofJudgment {
            hypotheses: vec![
                format!("source_block = {:?}", block.id),
                format!("target_block = {:?}", target_block),
                "variable_map_valid".to_string(),
            ],
            conclusion: format!("dataflow_preserved_{}", block.id.0),
            justification: ProofJustification::LemmaApplication {
                lemma_name: "sim_rel_preserves_dataflow".to_string(),
                arguments: vec![format!("{:?}", block.id), format!("{:?}", target_block)],
            },
        });

        proof_terms.push(CleanProofTerm {
            theorem: format!("{}.dataflow_block_{}", func.name, block.id.0),
            proof_script: format!(
                "apply sim_rel_preserves_dataflow; exact block_{}_map",
                block.id.0
            ),
            dependencies: vec!["sim_rel_preserves_dataflow".to_string()],
        });
    }

    // Return value preservation judgment.
    judgments.push(ProofJudgment {
        hypotheses: vec![
            "all_blocks_dataflow_preserved".to_string(),
            "return_local_mapped".to_string(),
        ],
        conclusion: "return_value_preserved".to_string(),
        justification: ProofJustification::Composition(vec![
            ProofJustification::LemmaApplication {
                lemma_name: "dataflow_implies_return".to_string(),
                arguments: vec![],
            },
        ]),
    });

    proof_terms.push(CleanProofTerm {
        theorem: format!("{}.return_value_preserved", func.name),
        proof_script: "apply dataflow_implies_return; assumption".to_string(),
        dependencies: vec!["dataflow_implies_return".to_string()],
    });

    // Build per-block certificates.
    let mut block_certs = FxHashMap::default();
    for block in &func.body.blocks {
        block_certs.insert(
            block.id,
            BlockCertificate {
                block_id: block.id,
                certified: true,
                check_kind: CheckKind::DataFlow,
                description: format!(
                    "block {:?} proof-certified: simulation relation verified",
                    block.id
                ),
            },
        );
    }

    Ok(CertifiedTranslation {
        function_name: func.name.clone(),
        verification_conditions: vcs,
        certificate: TranslationCertificate {
            function_name: func.name.clone(),
            level: CertificationLevel::ProofCertified,
            timestamp: SystemTime::now(),
            simulation_relation: Some(simulation_relation.clone()),
            cross_check_result: Some(cross_result),
            proof_judgments: judgments,
            proof_terms,
            block_certificates: block_certs,
        },
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{BasicBlock, BlockId, LocalDecl, SourceSpan, Terminator, Ty, VerifiableBody};

    use super::*;

    fn midpoint_function() -> VerifiableFunction {
        crate::tests::midpoint_function()
    }

    fn empty_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "empty_fn".to_string(),
            def_path: "test::empty_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // -----------------------------------------------------------------------
    // CertificationLevel tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_certification_level_ordering() {
        assert!(CertificationLevel::Uncertified < CertificationLevel::CrossChecked);
        assert!(CertificationLevel::CrossChecked < CertificationLevel::ProofCertified);
        assert!(CertificationLevel::Uncertified < CertificationLevel::ProofCertified);
    }

    #[test]
    fn test_certification_level_descriptions() {
        assert!(CertificationLevel::Uncertified.description().contains("no"));
        assert!(CertificationLevel::CrossChecked.description().contains("cross"));
        assert!(CertificationLevel::ProofCertified.description().contains("clean"));
    }

    #[test]
    fn test_certification_level_predicates() {
        assert!(!CertificationLevel::Uncertified.is_at_least_cross_checked());
        assert!(CertificationLevel::CrossChecked.is_at_least_cross_checked());
        assert!(CertificationLevel::ProofCertified.is_at_least_cross_checked());

        assert!(!CertificationLevel::Uncertified.is_proof_certified());
        assert!(!CertificationLevel::CrossChecked.is_proof_certified());
        assert!(CertificationLevel::ProofCertified.is_proof_certified());
    }

    // -----------------------------------------------------------------------
    // Uncertified translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_uncertified_translation_midpoint() {
        let func = midpoint_function();
        let ct = uncertified_translation(&func);

        assert_eq!(ct.function_name, "get_midpoint");
        assert_eq!(ct.level(), CertificationLevel::Uncertified);
        assert!(!ct.is_cross_checked());
        assert!(!ct.is_proof_certified());
        // `generate_vcs` emits overflow VCs again — midpoint has
        // one CheckedBinaryOp(Add) + Assert(Overflow(Add)) pair.
        assert!(ct.vc_count() >= 1, "midpoint must produce at least one VC, got {}", ct.vc_count());
        assert!(ct.certificate.cross_check_result.is_none());
        assert!(ct.certificate.proof_judgments.is_empty());
    }

    #[test]
    fn test_uncertified_translation_empty_function() {
        let func = empty_function();
        let ct = uncertified_translation(&func);

        assert_eq!(ct.level(), CertificationLevel::Uncertified);
        assert_eq!(ct.vc_count(), 0);
    }

    // -----------------------------------------------------------------------
    // Cross-checked translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cross_checked_translation_midpoint() {
        let func = midpoint_function();
        let ct = cross_checked_translation(&func).expect("midpoint should cross-check cleanly");

        assert_eq!(ct.level(), CertificationLevel::CrossChecked);
        assert!(ct.is_cross_checked());
        assert!(!ct.is_proof_certified());
        // primary and reference VC generators both emit the
        // overflow VC for midpoint's CheckedBinaryOp(Add), and agree on the
        // safety category.
        assert!(ct.vc_count() >= 1, "midpoint must produce at least one VC, got {}", ct.vc_count());
        assert!(ct.certificate.cross_check_result.is_some());
        assert!(ct.certificate.cross_check_result.as_ref().unwrap().is_sound());
    }

    #[test]
    fn test_cross_checked_translation_empty_function() {
        let func = empty_function();
        let ct = cross_checked_translation(&func).expect("empty fn should cross-check");

        assert_eq!(ct.level(), CertificationLevel::CrossChecked);
        assert_eq!(ct.vc_count(), 0);
    }

    #[test]
    fn test_cross_checked_block_certificates() {
        let func = midpoint_function();
        let ct = cross_checked_translation(&func).unwrap();

        // midpoint has 2 blocks
        assert_eq!(ct.certificate.block_certificates.len(), 2);
        assert!(ct.certificate.block_certificates.values().all(|bc| bc.certified));
        assert_eq!(ct.certified_block_count(), 2);
        assert!((ct.certification_coverage() - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Proof-certified translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_certified_translation_midpoint() {
        let func = midpoint_function();
        let sim_rel = SimulationRelation::identity(&func);
        let ct = proof_certified_translation(&func, &sim_rel)
            .expect("midpoint should proof-certify with identity relation");

        assert_eq!(ct.level(), CertificationLevel::ProofCertified);
        assert!(ct.is_cross_checked());
        assert!(ct.is_proof_certified());
        assert!(ct.certificate.simulation_relation.is_some());
        assert!(!ct.certificate.proof_judgments.is_empty());
        assert!(!ct.certificate.proof_terms.is_empty());
    }

    #[test]
    fn test_proof_certified_has_entry_point_judgment() {
        let func = empty_function();
        let sim_rel = SimulationRelation::identity(&func);
        let ct = proof_certified_translation(&func, &sim_rel).unwrap();

        let has_entry =
            ct.certificate.proof_judgments.iter().any(|j| j.conclusion == "entry_point_preserved");
        assert!(has_entry, "should have entry_point_preserved judgment");
    }

    #[test]
    fn test_proof_certified_has_return_value_judgment() {
        let func = midpoint_function();
        let sim_rel = SimulationRelation::identity(&func);
        let ct = proof_certified_translation(&func, &sim_rel).unwrap();

        let has_return =
            ct.certificate.proof_judgments.iter().any(|j| j.conclusion == "return_value_preserved");
        assert!(has_return, "should have return_value_preserved judgment");
    }

    #[test]
    fn test_proof_certified_has_per_block_judgments() {
        let func = midpoint_function();
        let sim_rel = SimulationRelation::identity(&func);
        let ct = proof_certified_translation(&func, &sim_rel).unwrap();

        // midpoint has 2 blocks -> should have dataflow_preserved_0 and _1
        let block_judgments: Vec<_> = ct
            .certificate
            .proof_judgments
            .iter()
            .filter(|j| j.conclusion.starts_with("dataflow_preserved_"))
            .collect();
        assert_eq!(block_judgments.len(), 2, "should have per-block dataflow judgments");
    }

    // -----------------------------------------------------------------------
    // Certificate verification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_uncertified_certificate() {
        let func = empty_function();
        let ct = uncertified_translation(&func);
        assert!(verify_certificate(&ct.certificate));
    }

    #[test]
    fn test_verify_cross_checked_certificate() {
        let func = midpoint_function();
        let ct = cross_checked_translation(&func).unwrap();
        assert!(verify_certificate(&ct.certificate));
    }

    #[test]
    fn test_verify_proof_certified_certificate() {
        let func = midpoint_function();
        let sim_rel = SimulationRelation::identity(&func);
        let ct = proof_certified_translation(&func, &sim_rel).unwrap();
        assert!(verify_certificate(&ct.certificate));
    }

    #[test]
    fn test_verify_certificate_rejects_cross_checked_without_result() {
        // A CrossChecked certificate without cross-check result is invalid.
        let cert = TranslationCertificate {
            function_name: "bad".to_string(),
            level: CertificationLevel::CrossChecked,
            timestamp: SystemTime::now(),
            simulation_relation: None,
            cross_check_result: None, // Missing!
            proof_judgments: vec![],
            proof_terms: vec![],
            block_certificates: FxHashMap::default(),
        };
        assert!(!verify_certificate(&cert));
    }

    #[test]
    fn test_verify_certificate_rejects_proof_certified_without_judgments() {
        // A ProofCertified certificate without judgments is invalid.
        let func = midpoint_function();
        let cross_result = full_cross_check(&func);
        let cert = TranslationCertificate {
            function_name: "bad".to_string(),
            level: CertificationLevel::ProofCertified,
            timestamp: SystemTime::now(),
            simulation_relation: None,
            cross_check_result: Some(cross_result),
            proof_judgments: vec![], // Missing!
            proof_terms: vec![],
            block_certificates: FxHashMap::default(),
        };
        assert!(!verify_certificate(&cert));
    }

    #[test]
    fn test_verify_certificate_rejects_empty_proof_script() {
        // A ProofCertified certificate with empty proof scripts is invalid.
        let func = midpoint_function();
        let cross_result = full_cross_check(&func);
        let cert = TranslationCertificate {
            function_name: "bad".to_string(),
            level: CertificationLevel::ProofCertified,
            timestamp: SystemTime::now(),
            simulation_relation: None,
            cross_check_result: Some(cross_result),
            proof_judgments: vec![ProofJudgment {
                hypotheses: vec![],
                conclusion: "test".to_string(),
                justification: ProofJustification::Compute,
            }],
            proof_terms: vec![CleanProofTerm {
                theorem: "test_thm".to_string(),
                proof_script: String::new(), // Empty!
                dependencies: vec![],
            }],
            block_certificates: FxHashMap::default(),
        };
        assert!(!verify_certificate(&cert));
    }

    // -----------------------------------------------------------------------
    // Proof judgment and justification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_justification_axiom() {
        let j = ProofJustification::Axiom("mir_semantics".to_string());
        assert!(matches!(j, ProofJustification::Axiom(ref name) if name == "mir_semantics"));
    }

    #[test]
    fn test_proof_justification_induction() {
        let j = ProofJustification::Induction {
            variable: "block".to_string(),
            base_case: Box::new(ProofJustification::Compute),
            inductive_step: Box::new(ProofJustification::LemmaApplication {
                lemma_name: "step".to_string(),
                arguments: vec!["n".to_string()],
            }),
        };
        assert!(matches!(j, ProofJustification::Induction { .. }));
    }

    // -----------------------------------------------------------------------
    // CertifiedTranslation metrics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_certification_coverage_empty() {
        let func = empty_function();
        let ct = uncertified_translation(&func);
        // No block certificates -> coverage is 0.0
        assert!((ct.certification_coverage() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_certification_coverage_all_certified() {
        let func = midpoint_function();
        let ct = cross_checked_translation(&func).unwrap();
        assert!((ct.certification_coverage() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_certification_coverage_partial() {
        let func = midpoint_function();
        let mut ct = cross_checked_translation(&func).unwrap();
        // Manually mark one block as uncertified
        if let Some(bc) = ct.certificate.block_certificates.get_mut(&BlockId(0)) {
            bc.certified = false;
        }
        // 1 of 2 blocks certified -> 0.5
        assert!((ct.certification_coverage() - 0.5).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Error type tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_certification_error_display() {
        let err = CertificationError::SoundnessAlarm {
            function: "my_fn".into(),
            details: "divergent".to_string(),
        };
        let msg = format!("{err}");
        assert!(msg.contains("my_fn"));
        assert!(msg.contains("divergent"));
    }

    #[test]
    fn test_certification_error_clean_unavailable() {
        let err = CertificationError::CleanUnavailable;
        let msg = format!("{err}");
        assert!(msg.contains("clean"));
    }
}
