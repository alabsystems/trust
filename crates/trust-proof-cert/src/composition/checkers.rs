// trust-proof-cert proof composition checkers
//
// Composability checks, proof composition, transitive closure,
// weakening, and strengthening operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use crate::formula_norm::formula_subsumes;
use crate::{ChainValidator, ProofCertificate};

use super::types::{ComposabilityResult, ComposedProof, CompositionError, Property};

/// Check structural compatibility between two certificate records.
///
/// Two certificate records are structurally compatible if:
/// 1. They are not for the same function+VC (would be redundant)
/// 2. Their VC assumptions don't obviously contradict each other
///
/// This function has no replay-bound proof-authority input. Consequently,
/// [`ComposabilityResult::composable`] is always `false`; callers may use
/// `structurally_compatible` and `issues` only as planning/diagnostic hints.
///
/// Returns `Err(CompositionError::FormulaDeserializationFailed)` if either
/// certificate's `formula_json` is corrupted and cannot be deserialized.
pub fn check_composability(
    a: &ProofCertificate,
    b: &ProofCertificate,
) -> Result<ComposabilityResult, CompositionError> {
    use trust_types::Formula;

    let mut issues = Vec::new();
    let mut shared_deps = Vec::new();

    for (side, cert) in [("left", a), ("right", b)] {
        if !cert.verify_vc_hash() {
            issues.push(format!(
                "{side} certificate for `{}` has a VC snapshot/hash mismatch",
                cert.function
            ));
        }
        let chain_validation = ChainValidator::validate(&cert.chain);
        if !chain_validation.valid {
            let details = chain_validation
                .findings
                .iter()
                .map(|finding| finding.detail.as_str())
                .collect::<Vec<_>>()
                .join("; ");
            issues.push(format!(
                "{side} certificate for `{}` has broken provenance metadata: {details}",
                cert.function,
            ));
        }
        serde_json::from_str::<Formula>(&cert.vc_snapshot.formula_json).map_err(|e| {
            CompositionError::FormulaDeserializationFailed {
                function: cert.function.clone(),
                reason: e.to_string(),
            }
        })?;
    }
    let integrity_clean = issues.is_empty();

    // Check for same function + same VC kind (redundant composition)
    let same_function_and_vc = a.function == b.function && a.vc_snapshot.kind == b.vc_snapshot.kind;
    if same_function_and_vc {
        issues.push(format!(
            "both certificates prove the same VC kind ({}) for function `{}`",
            a.vc_snapshot.kind, a.function
        ));
    }

    // Check for contradictory VC assumptions by examining the formula JSON.
    // If one proves P and the other proves NOT P for the same scope, they conflict.
    // This is a conservative syntactic check; semantic checking would require SMT.
    let syntactic_contradiction = a.function == b.function
        && a.vc_snapshot.formula_json == negate_formula_json(&b.vc_snapshot.formula_json);
    if syntactic_contradiction {
        issues.push(format!(
            "contradictory formulas for function `{}`: one proves negation of the other",
            a.function
        ));
    }

    // Track shared function dependencies
    if a.function == b.function {
        shared_deps.push(a.function.clone());
    }

    let result = ComposabilityResult {
        composable: false,
        structurally_compatible: issues.is_empty(),
        issues,
        shared_deps,
    };

    // Only the narrow syntactic-negation diagnostic can be reconsidered by the
    // semantic hint. Broken integrity and duplicate-VC findings must never be
    // erased by a formula-level fallback.
    if result.structurally_compatible {
        return Ok(result);
    }

    if integrity_clean && syntactic_contradiction && !same_function_and_vc {
        check_composability_semantic(a, b)
    } else {
        Ok(result)
    }
}

/// Semantic composability check using formula-level implication.
///
/// When the syntactic `check_composability` detects a potential conflict
/// (e.g., formula JSON negation match), this function deserializes the
/// formulas and uses `formula_subsumes` from `formula_norm.rs` to check
/// whether the callee's conclusion logically implies the caller's assumption
/// (or vice versa). Semantically equivalent but syntactically different
/// formulas will pass this check.
///
/// Reports structural compatibility when subsumption holds in either direction,
/// or when no structural contradiction is found. It never authorizes proof
/// composition. Returns `Err(CompositionError::FormulaDeserializationFailed)`
/// if either certificate's `formula_json` cannot be deserialized.
pub(crate) fn check_composability_semantic(
    a: &ProofCertificate,
    b: &ProofCertificate,
) -> Result<ComposabilityResult, CompositionError> {
    use trust_types::Formula;

    let mut issues = Vec::new();
    let mut shared_deps = Vec::new();

    // Track shared function dependencies
    if a.function == b.function {
        shared_deps.push(a.function.clone());
    }

    // Same function + same VC kind is redundant regardless of semantics
    if a.function == b.function && a.vc_snapshot.kind == b.vc_snapshot.kind {
        issues.push(format!(
            "both certificates prove the same VC kind ({}) for function `{}`",
            a.vc_snapshot.kind, a.function
        ));
        return Ok(ComposabilityResult {
            composable: false,
            structurally_compatible: false,
            issues,
            shared_deps,
        });
    }

    // Deserialize formulas for semantic comparison — propagate errors instead
    // of silently dropping them.
    let formula_a: Formula = serde_json::from_str(&a.vc_snapshot.formula_json).map_err(|e| {
        CompositionError::FormulaDeserializationFailed {
            function: a.function.clone(),
            reason: e.to_string(),
        }
    })?;
    let formula_b: Formula = serde_json::from_str(&b.vc_snapshot.formula_json).map_err(|e| {
        CompositionError::FormulaDeserializationFailed {
            function: b.function.clone(),
            reason: e.to_string(),
        }
    })?;

    // Check semantic compatibility: if either subsumes the other,
    // they are logically consistent (not contradictory).
    // Also check if they are not direct negations at the formula level.
    let a_subsumes_b = formula_subsumes(&formula_a, &formula_b);
    let b_subsumes_a = formula_subsumes(&formula_b, &formula_a);

    if a_subsumes_b || b_subsumes_a {
        // Formulas are semantically compatible — one implies the other
        Ok(ComposabilityResult {
            composable: false,
            structurally_compatible: true,
            issues: Vec::new(),
            shared_deps,
        })
    } else {
        // Cannot determine semantic compatibility; check for contradiction
        // via implication of negation: if fa => NOT fb (or vice versa),
        // they are contradictory.
        let neg_fb = Formula::Not(Box::new(formula_b.clone()));
        let neg_fa = Formula::Not(Box::new(formula_a.clone()));
        if formula_subsumes(&formula_a, &neg_fb) || formula_subsumes(&formula_b, &neg_fa) {
            issues.push(format!(
                "semantic contradiction detected for function `{}`: formulas are mutually exclusive",
                a.function
            ));
        } else {
            // Formulas are neither subsuming nor contradictory at the
            // structural level — retain a compatibility hint only.
        }

        Ok(ComposabilityResult {
            composable: false,
            structurally_compatible: issues.is_empty(),
            issues,
            shared_deps,
        })
    }
}

/// Attempt to compose multiple proof certificates.
///
/// This authority-bearing API rejects immediately: it has no sealed trust-root
/// configuration, exact obligation binding, or independently replayed
/// composition evidence. Public `status`, `strength`, signature, and hash-chain
/// fields must not mint a [`ComposedProof`]. Use [`check_composability`] for
/// separate structural diagnostics.
pub fn compose_proofs(certs: &[&ProofCertificate]) -> Result<ComposedProof, CompositionError> {
    if certs.is_empty() {
        return Err(CompositionError::CompositionFailed {
            reason: "cannot compose zero certificates".to_string(),
        });
    }

    Err(CompositionError::ProofAuthorityUnavailable { operation: "compose_proofs" })
}

/// Return the direct certificate-record inventory.
///
/// The former implementation inferred that an unproved caller was verified when
/// every callee merely had a public certificate record. That is not a proof of
/// the caller. Until exact call-site assumptions and replay-bound evidence are
/// wired, this compatibility API intentionally returns only names with direct
/// records and never derives transitive proof authority from `call_graph`.
// Trust: BTreeSet for deterministic diagnostic output
pub fn transitive_closure(
    certs: &[&ProofCertificate],
    _call_graph: &BTreeMap<String, Vec<String>>,
) -> BTreeSet<String> {
    certs.iter().map(|c| c.function.clone()).collect()
}

/// Weaken a certificate to a less precise property.
///
/// This compatibility entry point is fail-closed. It retains the structural
/// property check for diagnostics, but a VC-kind string relation cannot create
/// a new certificate. In particular, cloning and mutating a certificate would
/// retain a stale signature, VC hash, proof trace, and certification label.
pub fn weakening(
    cert: &ProofCertificate,
    weaker_property: &Property,
) -> Result<ProofCertificate, CompositionError> {
    // Reject labels that are not even a delimited structural prefix of the
    // original VC-kind label.
    let original_kind = &cert.vc_snapshot.kind;
    if !is_valid_weakening(original_kind, &weaker_property.0) {
        return Err(CompositionError::WeakeningFailed {
            target_property: weaker_property.0.clone(),
        });
    }

    Err(CompositionError::ProofAuthorityUnavailable { operation: "weakening" })
}

/// Check if a certificate can prove a stronger property.
///
/// Retains a structural label check for useful rejection diagnostics, then
/// fails closed because no proof implication is replayed.
pub fn strengthening_check(
    cert: &ProofCertificate,
    stronger_property: &Property,
) -> Result<(), CompositionError> {
    let original_kind = &cert.vc_snapshot.kind;

    // Preserve the legacy structural relation as a diagnostic: an exact label,
    // or a more specific variant, is plausible enough to reach the authority
    // gate. It is not proof implication.
    //
    // Example: cert proves "Assertion { message: \"x > 0\" }" which is at least
    // as strong as "Assertion" (the general category).
    if original_kind == &stronger_property.0 {
        return Err(CompositionError::ProofAuthorityUnavailable {
            operation: "strengthening_check",
        });
    }

    // Check whether the reported VC-kind label is a more specific variant of
    // the requested label.
    if original_kind.starts_with(&stronger_property.0) {
        let rest = &original_kind[stronger_property.0.len()..];
        if rest.is_empty() {
            return Err(CompositionError::ProofAuthorityUnavailable {
                operation: "strengthening_check",
            });
        }
        if let Some(ch) = rest.chars().next()
            && (ch == ' ' || ch == '{' || ch == '(' || ch == '<')
        {
            return Err(CompositionError::ProofAuthorityUnavailable {
                operation: "strengthening_check",
            });
        }
    }

    Err(CompositionError::StrengtheningFailed {
        cert_id: cert.id.0.clone(),
        target_property: stronger_property.0.clone(),
    })
}

/// Rank proof strengths from weakest (0) to strongest (4).
///
/// Ranking is based on the reasoning technique used. Bounded proofs rank
/// lowest, followed by SMT, deductive, inductive, and constructive.
pub(crate) fn strength_rank(s: &trust_types::ProofStrength) -> u8 {
    use trust_types::ReasoningKind;
    match &s.reasoning {
        ReasoningKind::BoundedModelCheck { .. } => 0,
        ReasoningKind::Smt => 1,
        ReasoningKind::Deductive => 2,
        ReasoningKind::Inductive | ReasoningKind::Pdr | ReasoningKind::ChcSpacer => 3,
        ReasoningKind::Constructive => 4,
        _ => 1, // default to SMT-level for unknown future variants
    }
}

/// Structural plausibility check for a weakening request.
///
/// This does not establish logical implication. It recognizes only:
/// - It is exactly equal to the original kind (identity weakening)
/// - It is a known category that generalizes the original (e.g., "Assertion"
///   generalizes "Assertion { message: ... }")
/// - The original kind starts with the weaker property followed by a structural
///   delimiter (space, '{', '('), indicating a more specific variant
///
/// Does NOT use arbitrary substring containment, which would allow nonsensical
/// weakenings like "sert" matching "Assertion".
fn is_valid_weakening(original_kind: &str, weaker: &str) -> bool {
    // Exact match (identity weakening is always valid)
    if original_kind == weaker {
        return true;
    }

    // The weaker property is a structural prefix of the original kind.
    // e.g., "Assertion" weakens "Assertion { message: ... }"
    // The original must start with the weaker string AND the next character
    // must be a structural delimiter (not a continuation of a word).
    if let Some(rest) = original_kind.strip_prefix(weaker) {
        if rest.is_empty() {
            return true;
        }
        // The character after the prefix must be a structural delimiter
        if let Some(ch) = rest.chars().next()
            && (ch == ' ' || ch == '{' || ch == '(' || ch == '<')
        {
            return true;
        }
    }

    false
}

/// Structural negation of a JSON-serialized [`Formula`].
///
/// Deserializes the formula, wraps it in [`Formula::Not`], and re-serializes.
/// Falls back to a conservative string wrapper if deserialization fails
/// (which means it will never spuriously match, only miss real contradictions).
pub(crate) fn negate_formula_json(formula: &str) -> String {
    use trust_types::Formula;

    match serde_json::from_str::<Formula>(formula) {
        Ok(f) => {
            let negated = Formula::Not(Box::new(f));
            // Serialization of a valid Formula should not fail.
            serde_json::to_string(&negated).unwrap_or_else(|_| format!("Not({formula})"))
        }
        Err(_) => {
            // Conservative fallback: will never match a real serialized formula,
            // so contradiction detection simply becomes a no-op.
            format!("Not({formula})")
        }
    }
}
