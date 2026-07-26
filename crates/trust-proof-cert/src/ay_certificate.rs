// trust-proof-cert ay certificate: proof certificate export and CHC portfolio
//
// Parses ay's proof output, extracts unsat cores, and provides structural
// verification of proof steps. Integrates with CertificateStore for
// persistence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::{ReasoningKind, SmtTheory};

use crate::{CertError, CertificateId, CertificateStore};

// ---------------------------------------------------------------------------
// Typed ay proof rules
// ---------------------------------------------------------------------------

/// Typed ay proof rule -- replaces stringly-typed `rule_name`.
///
/// Each variant corresponds to a ay proof inference rule. The `Unknown` variant
/// is an escape hatch for new ay versions that introduce rules we do not yet map.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AYRule {
    // Axiom/leaf rules
    Asserted,
    Hypothesis,
    Refl,
    TrueAxiom,
    Intro,

    // Propositional rules
    ModusPonens,
    UnitResolution,
    Lemma,

    // Theory rules
    ThLemma { theory: Option<SmtTheory> },

    // Equality and congruence
    Trans,
    Monotonicity,
    Commutativity,
    Congruence,

    // Rewriting
    Rewrite,
    DefIntro,
    IffTrue,
    IffFalse,

    // Quantifier rules
    QuantIntro,
    QuantInst,
    PullQuant,
    ElimUnusedVars,
    Skolemize,

    // Normal form transformations
    NnfPos,
    NnfNeg,
    Der,

    // Escape hatch for new ay versions
    Unknown(String),
}

impl AYRule {
    /// Parse from ay proof output string.
    #[must_use]
    pub fn parse(s: &str) -> Self {
        match s {
            "asserted" => Self::Asserted,
            "hypothesis" => Self::Hypothesis,
            "refl" => Self::Refl,
            "true-axiom" => Self::TrueAxiom,
            "intro" => Self::Intro,
            "mp" => Self::ModusPonens,
            "unit-resolution" => Self::UnitResolution,
            "lemma" => Self::Lemma,
            "th-lemma" => Self::ThLemma { theory: None },
            "trans" => Self::Trans,
            "monotonicity" => Self::Monotonicity,
            "commutativity" => Self::Commutativity,
            "rewrite" => Self::Rewrite,
            "def-intro" => Self::DefIntro,
            "iff-true" => Self::IffTrue,
            "iff-false" => Self::IffFalse,
            "quant-intro" => Self::QuantIntro,
            "quant-inst" => Self::QuantInst,
            "pull-quant" => Self::PullQuant,
            "elim-unused-vars" => Self::ElimUnusedVars,
            "der" => Self::Der,
            "nnf-pos" => Self::NnfPos,
            "nnf-neg" => Self::NnfNeg,
            "sk" => Self::Skolemize,
            other => Self::Unknown(other.to_string()),
        }
    }

    /// Map to the `ReasoningKind` this rule belongs to.
    #[must_use]
    pub fn reasoning_kind(&self) -> ReasoningKind {
        match self {
            Self::UnitResolution | Self::Lemma | Self::ModusPonens => ReasoningKind::CdclResolution,
            Self::ThLemma { theory } => ReasoningKind::TheoryLemma {
                theory: theory.clone().unwrap_or(SmtTheory::UninterpretedFunctions),
            },
            // Everything else is generic SMT infrastructure
            _ => ReasoningKind::Smt,
        }
    }
}

/// A single step in ay's proof trace.
///
/// Each step applies a proof rule to zero or more premises (referenced by
/// index) to derive a conclusion formula represented as an SMT-LIB string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AYProofStep {
    /// Proof rule name (e.g. "unit-resolution", "mp", "asserted", "refl").
    pub rule_name: String,
    /// Typed proof rule (dual-write alongside `rule_name` for backward compat).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rule: Option<AYRule>,
    /// The conclusion of this step as an SMT-LIB2 formula string.
    pub conclusion: String,
    /// Indices of premise steps this step depends on.
    pub premises: Vec<usize>,
    // Trust: BTreeMap for deterministic certificate output
    /// Optional annotations from the solver (e.g. ":pattern", ":qid").
    pub annotations: BTreeMap<String, String>,
}

/// A complete proof certificate exported from ay.
///
/// Contains the full proof trace, unsat core, timing information, and
/// a hash linking back to the verification condition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AYProofCertificate {
    /// SHA-256 hash of the VC this proof corresponds to.
    pub vc_hash: [u8; 32],
    /// Ordered sequence of proof steps from ay.
    pub proof_steps: Vec<AYProofStep>,
    /// Named assertions that form the unsat core (subset sufficient for unsat).
    pub unsat_core: Vec<String>,
    /// Wall-clock time in milliseconds for the solver run.
    pub time_ms: u64,
    /// ay version string.
    pub solver_version: String,
    /// Additional metadata (logic, options, etc.).
    pub metadata: BTreeMap<String, String>,
}

impl AYProofCertificate {
    /// Create a new empty certificate with the given VC hash and timing.
    pub fn new(vc_hash: [u8; 32], time_ms: u64, solver_version: impl Into<String>) -> Self {
        AYProofCertificate {
            vc_hash,
            proof_steps: Vec::new(),
            unsat_core: Vec::new(),
            time_ms,
            solver_version: solver_version.into(),
            metadata: BTreeMap::new(),
        }
    }

    /// Number of proof steps.
    pub fn step_count(&self) -> usize {
        self.proof_steps.len()
    }

    /// Set of unique proof rules used in this certificate.
    pub fn rules_used(&self) -> Vec<String> {
        let mut rules: Vec<String> = self.proof_steps.iter().map(|s| s.rule_name.clone()).collect();
        rules.sort();
        rules.dedup();
        rules
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

/// Parse ay's proof output into a `AYProofCertificate`.
///
/// ay proof output format (invoked with `(set-option :produce-proofs true)` and
/// `(get-proof)`) consists of nested s-expressions. Each proof step has the form:
///
/// ```text
/// (mp (asserted p) (asserted (=> p q)) q)
/// ```
///
/// or with let-bindings:
///
/// ```text
/// (let ((@x0 (asserted p)))
///   (mp @x0 (asserted (=> p q)) q))
/// ```
///
/// This parser handles the flat and let-bound forms, extracting rule names,
/// premises, and conclusions.
pub fn parse_ay_proof(
    output: &str,
    vc_hash: [u8; 32],
    time_ms: u64,
) -> Result<AYProofCertificate, CertError> {
    let mut cert = AYProofCertificate::new(vc_hash, time_ms, "ay");
    let trimmed = output.trim();

    if trimmed.is_empty() {
        return Ok(cert);
    }

    // Parse let-bindings first, collecting named subproofs
    let mut named_steps: BTreeMap<String, usize> = BTreeMap::new();
    let lines: Vec<&str> = trimmed.lines().collect();

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with(';') {
            i += 1;
            continue;
        }

        // Parse let-bindings: (let ((@name <proof>)) ...)
        if line.starts_with("(let") {
            i += 1;
            continue;
        }

        // Parse named step: (@name (rule ...))
        if let Some(rest) = line.strip_prefix("((@") {
            if let Some(name_end) = rest.find(|c: char| c.is_whitespace()) {
                let name = format!("@{}", &rest[..name_end]);
                let step_body = rest[name_end..].trim().trim_end_matches(')');
                if let Some(step) = parse_proof_step(step_body, &named_steps) {
                    let idx = cert.proof_steps.len();
                    named_steps.insert(name, idx);
                    cert.proof_steps.push(step);
                }
            }
            i += 1;
            continue;
        }

        // Parse inline proof step: (rule premise1 premise2 ... conclusion)
        let step_line = line.trim_start_matches('(').trim_end_matches(')');
        if !step_line.is_empty()
            && let Some(step) = parse_proof_step(step_line, &named_steps)
        {
            cert.proof_steps.push(step);
        }

        i += 1;
    }

    Ok(cert)
}

/// Parse a single proof step from its s-expression body.
///
/// Format: `rule_name arg1 arg2 ... conclusion`
/// Arguments that are `@name` references are resolved to premise indices.
fn parse_proof_step(body: &str, named_steps: &BTreeMap<String, usize>) -> Option<AYProofStep> {
    let body = body.trim();
    if body.is_empty() {
        return None;
    }

    // The rule name is the first token
    let (rule_name, rest) = split_first_token(body)?;

    // Parse remaining tokens: named refs become premises, last non-ref is conclusion
    let mut premises = Vec::new();
    let mut annotations = BTreeMap::new();
    let mut conclusion = String::new();
    let tokens = tokenize_sexpr(rest);

    // Check for annotations (keys starting with ':')
    let mut i = 0;
    while i < tokens.len() {
        if tokens[i].starts_with(':') {
            let key = tokens[i].clone();
            let value = if i + 1 < tokens.len() && !tokens[i + 1].starts_with(':') {
                i += 1;
                tokens[i].clone()
            } else {
                String::new()
            };
            annotations.insert(key, value);
            i += 1;
            continue;
        }

        if tokens[i].starts_with('@') {
            if let Some(&idx) = named_steps.get(&tokens[i]) {
                premises.push(idx);
            }
        } else {
            // Last non-annotation, non-reference token is the conclusion
            conclusion = tokens[i].clone();
        }
        i += 1;
    }

    let rule = Some(AYRule::parse(&rule_name));
    Some(AYProofStep { rule_name, rule, conclusion, premises, annotations })
}

/// Split the first whitespace-delimited token from a string.
fn split_first_token(s: &str) -> Option<(String, &str)> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    // Handle parenthesized first token
    if s.starts_with('(') {
        let end = find_matching_paren(s)?;
        let token = s[..=end].to_string();
        let rest = s[end + 1..].trim();
        return Some((token, rest));
    }

    if let Some(pos) = s.find(|c: char| c.is_whitespace()) {
        Some((s[..pos].to_string(), s[pos..].trim()))
    } else {
        Some((s.to_string(), ""))
    }
}

/// Find the index of the matching closing paren for an opening paren at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Tokenize an s-expression into top-level tokens, respecting parenthesized groups.
fn tokenize_sexpr(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let s = s.trim();
    if s.is_empty() {
        return tokens;
    }

    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        // Skip whitespace
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }

        if chars[i] == '(' {
            // Collect entire parenthesized group
            let mut depth = 0;
            let start = i;
            loop {
                if i >= chars.len() {
                    break;
                }
                if chars[i] == '(' {
                    depth += 1;
                } else if chars[i] == ')' {
                    depth -= 1;
                    if depth == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        } else {
            // Collect non-whitespace token
            let start = i;
            while i < chars.len() && !chars[i].is_whitespace() && chars[i] != '(' && chars[i] != ')'
            {
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        }
    }

    tokens
}

/// Check that AY proof-step records form a plausible refutation-shaped DAG.
///
/// Checks:
/// 1. All premise indices reference earlier steps (no forward/self references).
/// 2. No orphan steps (every non-axiom step has at least one premise).
/// 3. The final step should derive `false` (for refutation proofs).
///
/// This does not check rule semantics, formula equivalence, theory lemmas, or
/// solver replay. Success is structural metadata only, never an UNSAT verdict.
pub fn check_proof_step_structure(cert: &AYProofCertificate) -> Result<(), CertError> {
    if cert.proof_steps.is_empty() {
        return Err(CertError::VerificationFailed {
            reason: "AY proof-step record is empty; no refutation structure is present".to_string(),
        });
    }

    for (i, step) in cert.proof_steps.iter().enumerate() {
        // Check 1: all premises reference earlier steps
        for &premise_idx in &step.premises {
            if premise_idx >= i {
                return Err(CertError::VerificationFailed {
                    reason: format!(
                        "proof step {i} (rule: {}) references non-earlier premise {premise_idx}",
                        step.rule_name
                    ),
                });
            }
        }
    }

    // Check 2: non-axiom steps should have premises
    // Axiom rules: "asserted", "refl", "true-axiom", "hypothesis"
    let axiom_rules = ["asserted", "refl", "true-axiom", "hypothesis", "intro"];
    let mut orphan_count = 0;
    for step in &cert.proof_steps {
        if step.premises.is_empty() && !axiom_rules.contains(&step.rule_name.as_str()) {
            orphan_count += 1;
        }
    }

    if orphan_count > 0 {
        return Err(CertError::VerificationFailed {
            reason: format!(
                "orphan proof-step records ({orphan_count}/{} total); non-axiom records require premises",
                cert.proof_steps.len()
            ),
        });
    }

    // Check 3: final step MUST conclude `false` (refutation proof).
    // A proof that never derives the contradiction hasn't proved anything.
    // This was previously advisory (warning only) — now a hard error.
    if let Some(last) = cert.proof_steps.last() {
        let conclusion = last.conclusion.trim();
        if conclusion != "false" && conclusion != "#false" && conclusion != "(not true)" {
            return Err(CertError::VerificationFailed {
                reason: format!(
                    "final proof step concludes '{}', expected 'false' (refutation incomplete)",
                    conclusion
                ),
            });
        }
    }

    Ok(())
}

/// Extract named assertions from ay's unsat core output.
///
/// ay unsat core output format (after `(get-unsat-core)`):
///
/// ```text
/// (a0 a1 a3 a7)
/// ```
///
/// Each name corresponds to a `(assert (! formula :named <name>))` in the input.
pub fn extract_unsat_core(output: &str) -> Vec<String> {
    let trimmed = output.trim();
    if trimmed.is_empty() {
        return Vec::new();
    }

    // Handle parenthesized form: (name1 name2 ...)
    let inner = trimmed.trim_start_matches('(').trim_end_matches(')').trim();
    if inner.is_empty() {
        return Vec::new();
    }

    inner.split_whitespace().map(|s| s.to_string()).collect()
}

/// Extension trait for `CertificateStore` to store and retrieve ay certificates.
///
/// AY certificates are stored as JSON in the metadata of the corresponding
/// `ProofCertificate`'s proof_trace field.
pub trait AYCertificateStoreExt {
    /// Store a ay proof certificate alongside the corresponding proof certificate.
    fn store_ay_certificate(
        &mut self,
        cert_id: &CertificateId,
        ay_cert: &AYProofCertificate,
    ) -> Result<(), CertError>;

    /// Retrieve a ay proof certificate for a given proof certificate ID.
    fn get_ay_certificate(
        &self,
        cert_id: &CertificateId,
    ) -> Result<Option<AYProofCertificate>, CertError>;
}

impl AYCertificateStoreExt for CertificateStore {
    fn store_ay_certificate(
        &mut self,
        cert_id: &CertificateId,
        ay_cert: &AYProofCertificate,
    ) -> Result<(), CertError> {
        let proof_cert = self.certificates.get_mut(&cert_id.0).ok_or_else(|| {
            CertError::StoreError { reason: format!("certificate not found: {}", cert_id.0) }
        })?;

        let json = serde_json::to_vec(ay_cert)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

        proof_cert.proof_trace = json;
        Ok(())
    }

    fn get_ay_certificate(
        &self,
        cert_id: &CertificateId,
    ) -> Result<Option<AYProofCertificate>, CertError> {
        let proof_cert = match self.certificates.get(&cert_id.0) {
            Some(c) => c,
            None => return Ok(None),
        };

        if proof_cert.proof_trace.is_empty() {
            return Ok(None);
        }

        let ay_cert: AYProofCertificate = serde_json::from_slice(&proof_cert.proof_trace)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

        Ok(Some(ay_cert))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    // -----------------------------------------------------------------------
    // AYProofStep and AYProofCertificate basics
    // -----------------------------------------------------------------------

    fn sample_ay_certificate() -> AYProofCertificate {
        let vc_hash = [0u8; 32];
        let mut cert = AYProofCertificate::new(vc_hash, 42, "ay 4.13.0");

        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "p".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "(=> p q)".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(),
            premises: vec![0, 1],
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "unit-resolution".to_string(),
            rule: None,
            conclusion: "false".to_string(),
            premises: vec![2],
            annotations: BTreeMap::new(),
        });

        cert
    }

    #[test]
    fn test_ay_certificate_new() {
        let vc_hash = [1u8; 32];
        let cert = AYProofCertificate::new(vc_hash, 100, "ay 4.13.0");
        assert_eq!(cert.vc_hash, vc_hash);
        assert_eq!(cert.time_ms, 100);
        assert_eq!(cert.solver_version, "ay 4.13.0");
        assert!(cert.proof_steps.is_empty());
        assert!(cert.unsat_core.is_empty());
    }

    #[test]
    fn test_ay_certificate_step_count() {
        let cert = sample_ay_certificate();
        assert_eq!(cert.step_count(), 4);
    }

    #[test]
    fn test_ay_certificate_rules_used() {
        let cert = sample_ay_certificate();
        let rules = cert.rules_used();
        assert_eq!(rules, vec!["asserted", "mp", "unit-resolution"]);
    }

    #[test]
    fn test_ay_certificate_json_roundtrip() {
        let cert = sample_ay_certificate();
        let json = cert.to_json().expect("should serialize");
        let restored = AYProofCertificate::from_json(&json).expect("should deserialize");
        assert_eq!(restored, cert);
    }

    // -----------------------------------------------------------------------
    // Proof parsing
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_ay_proof_empty() {
        let cert = parse_ay_proof("", [0u8; 32], 0).expect("should parse empty");
        assert!(cert.proof_steps.is_empty());
    }

    #[test]
    fn test_parse_ay_proof_simple_steps() {
        let output = "\
asserted p
asserted (=> p q)
mp @0 @1 q
unit-resolution @2 false";

        let cert = parse_ay_proof(output, [0u8; 32], 10).expect("should parse");
        assert!(!cert.proof_steps.is_empty());
        // First step should be "asserted"
        assert_eq!(cert.proof_steps[0].rule_name, "asserted");
        assert_eq!(cert.proof_steps[0].conclusion, "p");
    }

    #[test]
    fn test_parse_ay_proof_with_comments() {
        let output = "\
; This is a comment
asserted p
; Another comment

asserted q";

        let cert = parse_ay_proof(output, [0u8; 32], 5).expect("should parse");
        assert_eq!(cert.proof_steps.len(), 2);
    }

    #[test]
    fn test_parse_ay_proof_named_steps() {
        let output = "\
((@x0 asserted p))
((@x1 asserted (=> p q)))
((@x2 mp @x0 @x1 q))";

        let cert = parse_ay_proof(output, [0u8; 32], 15).expect("should parse");
        assert!(cert.proof_steps.len() >= 2);
    }

    // -----------------------------------------------------------------------
    // Proof-step structural inspection
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_proof_step_structure_valid() {
        let cert = sample_ay_certificate();
        check_proof_step_structure(&cert).expect("structure should be valid");
    }

    #[test]
    fn test_check_proof_step_structure_empty_fails_closed() {
        let cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        assert!(check_proof_step_structure(&cert).is_err());
    }

    #[test]
    fn test_check_proof_step_structure_forward_reference_fails() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(),
            premises: vec![1], // forward reference
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "p".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });

        let err = check_proof_step_structure(&cert).expect_err("should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("non-earlier premise"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_check_proof_step_structure_self_reference_fails() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(),
            premises: vec![0], // self reference
            annotations: BTreeMap::new(),
        });

        let err = check_proof_step_structure(&cert).expect_err("should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("non-earlier premise"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Final step and orphan tolerance tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_proof_step_structure_final_step_not_false_fails() {
        // A proof where the final step concludes something other than `false`
        // must fail verification -- the refutation is incomplete.
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "p".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "(=> p q)".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(AYProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(), // NOT false -- incomplete proof
            premises: vec![0, 1],
            annotations: BTreeMap::new(),
        });

        let err = check_proof_step_structure(&cert).expect_err("incomplete record should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(
                    reason.contains("expected 'false'"),
                    "error should mention expected false, got: {reason}"
                );
                assert!(
                    reason.contains("refutation incomplete"),
                    "error should mention refutation incomplete, got: {reason}"
                );
            }
            other => panic!("expected VerificationFailed, got: {other:?}"),
        }
    }

    #[test]
    fn test_check_proof_step_structure_rejects_all_orphans() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");

        // 97 asserted steps (axioms -- these are NOT orphans)
        for i in 0..97 {
            cert.proof_steps.push(AYProofStep {
                rule_name: "asserted".to_string(),
                rule: None,
                conclusion: format!("p{i}"),
                premises: vec![],
                annotations: BTreeMap::new(),
            });
        }

        // 3 non-axiom orphan steps (no premises, not axiom rules)
        for _ in 0..3 {
            cert.proof_steps.push(AYProofStep {
                rule_name: "rewrite".to_string(),
                rule: None,
                conclusion: "false".to_string(),
                premises: vec![], // orphan: non-axiom with no premises
                annotations: BTreeMap::new(),
            });
        }

        let err = check_proof_step_structure(&cert).expect_err("orphans should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("orphan"), "error should mention orphan, got: {reason}");
            }
            other => panic!("expected VerificationFailed, got: {other:?}"),
        }
    }

    #[test]
    fn test_check_proof_step_structure_valid_with_false_conclusion() {
        // A valid proof: correct DAG, no orphans, final step is `false`.
        let cert = sample_ay_certificate();
        check_proof_step_structure(&cert).expect("record structure should be valid");
    }

    #[test]
    fn test_check_proof_step_structure_hash_false_accepted() {
        // `#false` is an accepted refutation marker.
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "#false".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });

        check_proof_step_structure(&cert).expect("structure should be accepted");
    }

    #[test]
    fn test_check_proof_step_structure_not_true_accepted() {
        // `(not true)` is an accepted refutation marker.
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "asserted".to_string(),
            rule: None,
            conclusion: "(not true)".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });

        check_proof_step_structure(&cert).expect("structure should be accepted");
    }

    // -----------------------------------------------------------------------
    // Unsat core extraction
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_unsat_core_basic() {
        let output = "(a0 a1 a3 a7)";
        let core = extract_unsat_core(output);
        assert_eq!(core, vec!["a0", "a1", "a3", "a7"]);
    }

    #[test]
    fn test_extract_unsat_core_single() {
        let output = "(a0)";
        let core = extract_unsat_core(output);
        assert_eq!(core, vec!["a0"]);
    }

    #[test]
    fn test_extract_unsat_core_empty_parens() {
        let output = "()";
        let core = extract_unsat_core(output);
        assert!(core.is_empty());
    }

    #[test]
    fn test_extract_unsat_core_empty_string() {
        let core = extract_unsat_core("");
        assert!(core.is_empty());
    }

    #[test]
    fn test_extract_unsat_core_whitespace() {
        let output = "  ( a0   a1   a2 )  ";
        let core = extract_unsat_core(output);
        assert_eq!(core, vec!["a0", "a1", "a2"]);
    }

    #[test]
    fn test_extract_unsat_core_no_parens() {
        let output = "a0 a1";
        let core = extract_unsat_core(output);
        assert_eq!(core, vec!["a0", "a1"]);
    }

    // -----------------------------------------------------------------------
    // CertificateStore integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_ay_certificate_roundtrip() {
        use crate::{CertificateChain, FunctionHash, ProofCertificate, SolverInfo, VcSnapshot};
        use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

        let mut store = CertificateStore::new("test-crate");
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "test".to_string() },
            function: "foo".into(),
            location: SourceSpan {
                file: "test.rs".to_string(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot");
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "4.13.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let cert = ProofCertificate::new_trusted(
            "foo".to_string(),
            FunctionHash::from_bytes(b"foo-body"),
            snapshot,
            solver,
            vec![],
            "2026-03-30T00:00:00Z".to_string(),
        );
        let cert_id = cert.id.clone();
        store.insert(cert, CertificateChain::new());

        let ay_cert = sample_ay_certificate();
        store.store_ay_certificate(&cert_id, &ay_cert).expect("should store");

        let retrieved =
            store.get_ay_certificate(&cert_id).expect("should not error").expect("should exist");
        assert_eq!(retrieved, ay_cert);
    }

    #[test]
    fn test_store_ay_certificate_missing_cert() {
        let mut store = CertificateStore::new("test-crate");
        let ay_cert = sample_ay_certificate();
        let missing_id = CertificateId::generate("nonexistent", "2026-01-01T00:00:00Z");

        let err = store
            .store_ay_certificate(&missing_id, &ay_cert)
            .expect_err("should fail for missing cert");
        match err {
            CertError::StoreError { reason } => {
                assert!(reason.contains("not found"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_get_ay_certificate_empty_trace() {
        use crate::{CertificateChain, FunctionHash, ProofCertificate, SolverInfo, VcSnapshot};
        use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

        let mut store = CertificateStore::new("test-crate");
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "test".to_string() },
            function: "bar".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot");
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "4.13.0".to_string(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let cert = ProofCertificate::new_trusted(
            "bar".to_string(),
            FunctionHash::from_bytes(b"bar-body"),
            snapshot,
            solver,
            vec![], // empty proof_trace
            "2026-03-30T00:00:00Z".to_string(),
        );
        let cert_id = cert.id.clone();
        store.insert(cert, CertificateChain::new());

        let result = store.get_ay_certificate(&cert_id).expect("should not error");
        assert!(result.is_none(), "empty proof_trace should return None");
    }

    #[test]
    fn test_get_ay_certificate_nonexistent_id() {
        let store = CertificateStore::new("test-crate");
        let missing_id = CertificateId::generate("nonexistent", "2026-01-01T00:00:00Z");

        let result = store.get_ay_certificate(&missing_id).expect("should not error");
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // Tokenizer tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_tokenize_sexpr_basic() {
        let tokens = tokenize_sexpr("a b c");
        assert_eq!(tokens, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_tokenize_sexpr_nested() {
        let tokens = tokenize_sexpr("a (b c) d");
        assert_eq!(tokens, vec!["a", "(b c)", "d"]);
    }

    #[test]
    fn test_tokenize_sexpr_empty() {
        let tokens = tokenize_sexpr("");
        assert!(tokens.is_empty());
    }

    #[test]
    fn test_tokenize_sexpr_deeply_nested() {
        let tokens = tokenize_sexpr("mp (asserted (=> p q)) @0");
        assert_eq!(tokens, vec!["mp", "(asserted (=> p q))", "@0"]);
    }

    // -----------------------------------------------------------------------
    // Split first token tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_first_token_simple() {
        let (tok, rest) = split_first_token("hello world").unwrap();
        assert_eq!(tok, "hello");
        assert_eq!(rest, "world");
    }

    #[test]
    fn test_split_first_token_single() {
        let (tok, rest) = split_first_token("hello").unwrap();
        assert_eq!(tok, "hello");
        assert_eq!(rest, "");
    }

    #[test]
    fn test_split_first_token_empty() {
        assert!(split_first_token("").is_none());
    }
}
