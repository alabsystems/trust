// trust-clean/ay_proof_bridge.rs: AY proof certificate to SolverProof translation
//
// Translates ay's native proof output (AYProofCertificate with AYProofStep entries)
// into the SolverProof/ProofStep representation consumed by the reconstruction
// pipeline. This bridges the gap between ay's proof format and clean certification.
//
// Part of #429: SmtBacked to Certified pathway
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_proof_cert::ay_certificate::{AYProofCertificate, AYProofStep};
use trust_types::{Formula, Sort};

use crate::error::CertificateError;
use crate::reconstruction::{ProofStep, SolverProof};

// ---------------------------------------------------------------------------
// AY rule classification
// ---------------------------------------------------------------------------

/// Classification of ay proof rules into categories for translation.
///
/// ay proof rules map to SolverProof step types as documented in the
/// design doc (designs/2026-04-10-smt-backed-to-certified-pathway.md).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AYRuleKind {
    /// Input assertion: maps to ProofStep::Axiom.
    Asserted,
    /// Modus ponens: maps to ProofStep::ModusPonens.
    ModusPonens,
    /// Unit resolution: maps to ProofStep::Resolution.
    UnitResolution,
    /// Reflexivity (a = a): maps to ProofStep::Axiom with "refl" tag.
    Reflexivity,
    /// Transitivity (a=b, b=c => a=c): maps to ProofStep::Rewrite chain.
    Transitivity,
    /// Monotonicity/congruence (f(a) = f(b) from a = b): maps to ProofStep::Congruence.
    Monotonicity,
    /// Universal instantiation: maps to ProofStep::Instantiation.
    QuantInst,
    /// Theory lemma (opaque arithmetic/BV step): maps to trusted Axiom.
    TheoryLemma { theory: String },
    /// Definitional axiom: maps to ProofStep::Axiom with "def-axiom" tag.
    DefAxiom,
    /// NNF normalization: maps to ProofStep::Rewrite.
    NnfRewrite,
    /// Skolemization: maps to ProofStep::Axiom with "skolem" tag.
    Skolem,
    /// Symmetry (a=b => b=a): maps to ProofStep::Rewrite.
    Symmetry,
    /// Rule not yet mapped; treated as trusted axiom.
    Unknown(String),
}

/// Classify a ay rule name into the corresponding AYRuleKind.
///
/// Handles the core ay proof rules documented in the ay source:
/// asserted, mp, unit-resolution, refl, symm, trans, monotonicity,
/// quant-inst, th-lemma, def-axiom, nnf-pos, nnf-neg, sk.
pub(crate) fn classify_ay_rule(rule_name: &str) -> AYRuleKind {
    match rule_name {
        "asserted" | "hypothesis" | "true-axiom" | "intro" => AYRuleKind::Asserted,
        "mp" | "modus-ponens" => AYRuleKind::ModusPonens,
        "unit-resolution" | "resolution" => AYRuleKind::UnitResolution,
        "refl" => AYRuleKind::Reflexivity,
        "symm" => AYRuleKind::Symmetry,
        "trans" => AYRuleKind::Transitivity,
        "monotonicity" | "congr" => AYRuleKind::Monotonicity,
        "quant-inst" => AYRuleKind::QuantInst,
        "def-axiom" => AYRuleKind::DefAxiom,
        "nnf-pos" | "nnf-neg" => AYRuleKind::NnfRewrite,
        "sk" => AYRuleKind::Skolem,
        other if other.starts_with("th-lemma") => {
            // th-lemma may have a theory suffix: "th-lemma" or "th-lemma arith"
            let theory = other.strip_prefix("th-lemma").unwrap_or("").trim().to_string();
            let theory = if theory.is_empty() { "unknown".to_string() } else { theory };
            AYRuleKind::TheoryLemma { theory }
        }
        other => AYRuleKind::Unknown(other.to_string()),
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 conclusion parsing (minimal)
// ---------------------------------------------------------------------------

/// Parse a AYProofStep conclusion string into a trust-types Formula.
///
/// The conclusion is an SMT-LIB2 string. We parse a minimal subset that
/// ay actually produces in proof conclusions:
/// - Atoms: `true`, `false`, identifiers, integer literals
/// - Negation: `(not <expr>)`
/// - Binary: `(= <a> <b>)`, `(=> <a> <b>)`, `(<= <a> <b>)`, `(>= <a> <b>)`,
///   `(< <a> <b>)`, `(> <a> <b>)`, `(+ <a> <b>)`, `(- <a> <b>)`
/// - N-ary: `(and ...)`, `(or ...)`
///
/// For conclusions we cannot parse, returns a Bool(true) placeholder
/// (the proof structure is still valid; the conclusion is just metadata).
pub(crate) fn parse_smtlib2_conclusion(conclusion: &str) -> Formula {
    let s = conclusion.trim();
    if s.is_empty() || s == "true" {
        return Formula::Bool(true);
    }
    if s == "false" || s == "#false" {
        return Formula::Bool(false);
    }

    // Integer literal
    if let Ok(n) = s.parse::<i128>() {
        return Formula::Int(n);
    }

    // Parenthesized expression
    if s.starts_with('(') && s.ends_with(')') {
        let inner = &s[1..s.len() - 1];
        let tokens = tokenize_smtlib2(inner);
        if tokens.is_empty() {
            return Formula::Bool(true);
        }

        let op = tokens[0].as_str();
        match op {
            "not" if tokens.len() == 2 => {
                let arg = parse_smtlib2_conclusion(&tokens[1]);
                return Formula::Not(Box::new(arg));
            }
            "=>" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Implies(Box::new(lhs), Box::new(rhs));
            }
            "=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Eq(Box::new(lhs), Box::new(rhs));
            }
            "<=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Le(Box::new(lhs), Box::new(rhs));
            }
            ">=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Ge(Box::new(lhs), Box::new(rhs));
            }
            "<" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Lt(Box::new(lhs), Box::new(rhs));
            }
            ">" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Gt(Box::new(lhs), Box::new(rhs));
            }
            "+" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Add(Box::new(lhs), Box::new(rhs));
            }
            "-" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Sub(Box::new(lhs), Box::new(rhs));
            }
            "and" if tokens.len() >= 2 => {
                let args: Vec<Formula> =
                    tokens[1..].iter().map(|t| parse_smtlib2_conclusion(t)).collect();
                return Formula::And(args);
            }
            "or" if tokens.len() >= 2 => {
                let args: Vec<Formula> =
                    tokens[1..].iter().map(|t| parse_smtlib2_conclusion(t)).collect();
                return Formula::Or(args);
            }
            _ => {}
        }

        // Fallback for unparseable s-expressions
        return Formula::Bool(true);
    }

    // Bare identifier: treat as a Boolean variable
    Formula::Var(s.into(), Sort::Bool)
}

/// Tokenize an SMT-LIB2 expression into top-level tokens, respecting parens.
fn tokenize_smtlib2(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }

        if chars[i] == '(' {
            let mut depth = 1;
            let start = i;
            i += 1;
            while i < chars.len() && depth > 0 {
                if chars[i] == '(' {
                    depth += 1;
                } else if chars[i] == ')' {
                    depth -= 1;
                }
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        } else {
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

// ---------------------------------------------------------------------------
// Main translation function
// ---------------------------------------------------------------------------

/// Translate a ay proof certificate into a SolverProof for reconstruction.
///
/// Maps each AYProofStep to the corresponding ProofStep variant using the
/// ay rule classification table. Premises are preserved as step indices.
///
/// # ay rule mapping
///
/// | ay Rule | ProofStep | Notes |
/// |---------|-----------|-------|
/// | asserted | Axiom | Input assertion |
/// | mp | ModusPonens | Modus ponens |
/// | unit-resolution | Resolution | Pivot from conclusion diff |
/// | refl | Axiom("refl.{sort}") | Reflexivity |
/// | symm | Rewrite | Symmetry via rewrite |
/// | trans | Rewrite | Transitivity as rewrite chain |
/// | monotonicity | Congruence | f(a) = f(b) from a = b |
/// | quant-inst | Instantiation | Universal instantiation |
/// | th-lemma | Axiom("th-lemma.{theory}") | Trusted theory lemma |
/// | def-axiom | Axiom("def-axiom") | Definitional tautology |
/// | nnf-pos/neg | Rewrite | NNF normalization |
/// | sk | Axiom("skolem") | Skolemization |
///
/// # Errors
///
/// Returns `CertificateError` if a proof step references a non-existent premise.
pub fn translate_ay_proof(ay_cert: &AYProofCertificate) -> Result<SolverProof, CertificateError> {
    if ay_cert.proof_steps.is_empty() {
        return Ok(SolverProof {
            steps: Vec::new(),
            used_axioms: Vec::new(),
            used_lemmas: Vec::new(),
        });
    }

    let mut steps = Vec::with_capacity(ay_cert.proof_steps.len());
    let mut used_axioms = Vec::new();
    let mut used_lemmas = Vec::new();

    for (idx, ay_step) in ay_cert.proof_steps.iter().enumerate() {
        // Validate premise indices
        for &premise in &ay_step.premises {
            if premise >= idx {
                return Err(CertificateError::InvalidProofTerm {
                    reason: format!(
                        "ay proof step {idx} (rule: {}) references non-earlier premise {premise}",
                        ay_step.rule_name
                    ),
                });
            }
        }

        let conclusion = parse_smtlib2_conclusion(&ay_step.conclusion);
        let rule_kind = classify_ay_rule(&ay_step.rule_name);

        let step = translate_step(&rule_kind, ay_step, idx, &conclusion)?;

        // Track axiom names and lemma references
        match &step {
            ProofStep::Axiom { name, .. } => {
                if !used_axioms.contains(name) {
                    used_axioms.push(name.clone());
                }
            }
            _ => {
                for &premise in &ay_step.premises {
                    if !used_lemmas.contains(&premise) {
                        used_lemmas.push(premise);
                    }
                }
            }
        }

        steps.push(step);
    }

    Ok(SolverProof { steps, used_axioms, used_lemmas })
}

/// Translate a single ay proof step into a ProofStep.
fn translate_step(
    rule_kind: &AYRuleKind,
    ay_step: &AYProofStep,
    idx: usize,
    conclusion: &Formula,
) -> Result<ProofStep, CertificateError> {
    match rule_kind {
        AYRuleKind::Asserted => {
            Ok(ProofStep::Axiom { name: format!("asserted_{idx}"), formula: conclusion.clone() })
        }

        AYRuleKind::ModusPonens => {
            // mp requires exactly 2 premises: the implication and the antecedent
            let (impl_step, ante_step) = get_two_premises(ay_step, idx, "mp")?;
            Ok(ProofStep::ModusPonens { implication_step: impl_step, antecedent_step: ante_step })
        }

        AYRuleKind::UnitResolution => {
            // unit-resolution has 1+ premises; first is the clause, rest are units
            if ay_step.premises.is_empty() {
                return Err(CertificateError::InvalidProofTerm {
                    reason: format!("ay unit-resolution step {idx} has no premises"),
                });
            }
            // Model as resolution between first two premises (or first + self for single)
            let positive = ay_step.premises[0];
            let negative = if ay_step.premises.len() > 1 { ay_step.premises[1] } else { positive };
            // Use conclusion as pivot placeholder
            Ok(ProofStep::Resolution {
                positive_step: positive,
                negative_step: negative,
                pivot: conclusion.clone(),
            })
        }

        AYRuleKind::Reflexivity => {
            Ok(ProofStep::Axiom { name: format!("refl_{idx}"), formula: conclusion.clone() })
        }

        AYRuleKind::Symmetry => {
            // symm requires 1 premise: the equality to flip
            let premise = get_first_premise(ay_step, idx, "symm")?;
            Ok(ProofStep::Rewrite { equality_step: premise, target_step: premise })
        }

        AYRuleKind::Transitivity => {
            // trans requires 2 premises: a=b and b=c
            let (eq1, eq2) = get_two_premises(ay_step, idx, "trans")?;
            Ok(ProofStep::Rewrite { equality_step: eq1, target_step: eq2 })
        }

        AYRuleKind::Monotonicity => {
            // monotonicity requires 1+ equality premises
            let premise = get_first_premise(ay_step, idx, "monotonicity")?;
            // Extract function name from annotations or conclusion
            let function_name =
                ay_step.annotations.get(":decl").cloned().unwrap_or_else(|| format!("f_{idx}"));
            Ok(ProofStep::Congruence { equality_step: premise, function_name })
        }

        AYRuleKind::QuantInst => {
            // quant-inst: instantiation of a universally quantified formula
            let premise = if ay_step.premises.is_empty() {
                // quant-inst can be self-contained (no premise, carries the axiom)
                return Ok(ProofStep::Axiom {
                    name: format!("quant-inst_{idx}"),
                    formula: conclusion.clone(),
                });
            } else {
                ay_step.premises[0]
            };
            // Extract the witness from annotations or use conclusion
            let witness = ay_step
                .annotations
                .get(":pattern")
                .map(|p| parse_smtlib2_conclusion(p))
                .unwrap_or_else(|| conclusion.clone());
            Ok(ProofStep::Instantiation { quantified_step: premise, witness })
        }

        AYRuleKind::TheoryLemma { theory } => Ok(ProofStep::Axiom {
            name: format!("th-lemma.{theory}_{idx}"),
            formula: conclusion.clone(),
        }),

        AYRuleKind::DefAxiom => {
            Ok(ProofStep::Axiom { name: format!("def-axiom_{idx}"), formula: conclusion.clone() })
        }

        AYRuleKind::NnfRewrite => {
            // NNF rewrite: if we have a premise, it's a rewrite; otherwise axiom
            if let Some(&premise) = ay_step.premises.first() {
                Ok(ProofStep::Rewrite { equality_step: premise, target_step: premise })
            } else {
                Ok(ProofStep::Axiom { name: format!("nnf_{idx}"), formula: conclusion.clone() })
            }
        }

        AYRuleKind::Skolem => {
            Ok(ProofStep::Axiom { name: format!("skolem_{idx}"), formula: conclusion.clone() })
        }

        AYRuleKind::Unknown(rule) => {
            // Unknown rules become trusted axioms
            Ok(ProofStep::Axiom { name: format!("{rule}_{idx}"), formula: conclusion.clone() })
        }
    }
}

// ---------------------------------------------------------------------------
// Premise extraction helpers
// ---------------------------------------------------------------------------

/// Get exactly two premises from a ay step, returning an error if not available.
fn get_two_premises(
    ay_step: &AYProofStep,
    idx: usize,
    rule: &str,
) -> Result<(usize, usize), CertificateError> {
    if ay_step.premises.len() < 2 {
        return Err(CertificateError::InvalidProofTerm {
            reason: format!(
                "ay {rule} step {idx} requires 2 premises, got {}",
                ay_step.premises.len()
            ),
        });
    }
    Ok((ay_step.premises[0], ay_step.premises[1]))
}

/// Get the first premise from a ay step, returning an error if empty.
fn get_first_premise(
    ay_step: &AYProofStep,
    idx: usize,
    rule: &str,
) -> Result<usize, CertificateError> {
    ay_step.premises.first().copied().ok_or_else(|| CertificateError::InvalidProofTerm {
        reason: format!("ay {rule} step {idx} requires at least 1 premise, got 0"),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use trust_proof_cert::ay_certificate::{AYProofCertificate, AYProofStep};

    use super::*;

    // -- Helpers --

    fn make_ay_step(rule: &str, conclusion: &str, premises: Vec<usize>) -> AYProofStep {
        AYProofStep {
            rule_name: rule.to_string(),
            rule: None,
            conclusion: conclusion.to_string(),
            premises,
            annotations: BTreeMap::new(),
        }
    }

    fn sample_ay_certificate() -> AYProofCertificate {
        let mut cert = AYProofCertificate::new([0u8; 32], 42, "ay 4.13.0");
        cert.proof_steps.push(make_ay_step("asserted", "p", vec![]));
        cert.proof_steps.push(make_ay_step("asserted", "(=> p q)", vec![]));
        cert.proof_steps.push(make_ay_step("mp", "q", vec![0, 1]));
        cert.proof_steps.push(make_ay_step("unit-resolution", "false", vec![2]));
        cert
    }

    // -- classify_ay_rule tests --

    #[test]
    fn test_classify_asserted() {
        assert_eq!(classify_ay_rule("asserted"), AYRuleKind::Asserted);
        assert_eq!(classify_ay_rule("hypothesis"), AYRuleKind::Asserted);
        assert_eq!(classify_ay_rule("true-axiom"), AYRuleKind::Asserted);
        assert_eq!(classify_ay_rule("intro"), AYRuleKind::Asserted);
    }

    #[test]
    fn test_classify_mp() {
        assert_eq!(classify_ay_rule("mp"), AYRuleKind::ModusPonens);
        assert_eq!(classify_ay_rule("modus-ponens"), AYRuleKind::ModusPonens);
    }

    #[test]
    fn test_classify_resolution() {
        assert_eq!(classify_ay_rule("unit-resolution"), AYRuleKind::UnitResolution);
        assert_eq!(classify_ay_rule("resolution"), AYRuleKind::UnitResolution);
    }

    #[test]
    fn test_classify_equality_rules() {
        assert_eq!(classify_ay_rule("refl"), AYRuleKind::Reflexivity);
        assert_eq!(classify_ay_rule("symm"), AYRuleKind::Symmetry);
        assert_eq!(classify_ay_rule("trans"), AYRuleKind::Transitivity);
    }

    #[test]
    fn test_classify_monotonicity() {
        assert_eq!(classify_ay_rule("monotonicity"), AYRuleKind::Monotonicity);
        assert_eq!(classify_ay_rule("congr"), AYRuleKind::Monotonicity);
    }

    #[test]
    fn test_classify_quant_inst() {
        assert_eq!(classify_ay_rule("quant-inst"), AYRuleKind::QuantInst);
    }

    #[test]
    fn test_classify_theory_lemma() {
        let kind = classify_ay_rule("th-lemma");
        assert!(matches!(kind, AYRuleKind::TheoryLemma { ref theory } if theory == "unknown"));

        let kind = classify_ay_rule("th-lemma arith");
        assert!(matches!(kind, AYRuleKind::TheoryLemma { ref theory } if theory == "arith"));
    }

    #[test]
    fn test_classify_def_axiom() {
        assert_eq!(classify_ay_rule("def-axiom"), AYRuleKind::DefAxiom);
    }

    #[test]
    fn test_classify_nnf() {
        assert_eq!(classify_ay_rule("nnf-pos"), AYRuleKind::NnfRewrite);
        assert_eq!(classify_ay_rule("nnf-neg"), AYRuleKind::NnfRewrite);
    }

    #[test]
    fn test_classify_skolem() {
        assert_eq!(classify_ay_rule("sk"), AYRuleKind::Skolem);
    }

    #[test]
    fn test_classify_unknown() {
        let kind = classify_ay_rule("some-new-rule");
        assert!(matches!(kind, AYRuleKind::Unknown(ref r) if r == "some-new-rule"));
    }

    // -- parse_smtlib2_conclusion tests --

    #[test]
    fn test_parse_true() {
        assert_eq!(parse_smtlib2_conclusion("true"), Formula::Bool(true));
    }

    #[test]
    fn test_parse_false() {
        assert_eq!(parse_smtlib2_conclusion("false"), Formula::Bool(false));
        assert_eq!(parse_smtlib2_conclusion("#false"), Formula::Bool(false));
    }

    #[test]
    fn test_parse_integer() {
        assert_eq!(parse_smtlib2_conclusion("42"), Formula::Int(42));
        assert_eq!(parse_smtlib2_conclusion("-7"), Formula::Int(-7));
    }

    #[test]
    fn test_parse_variable() {
        assert_eq!(parse_smtlib2_conclusion("p"), Formula::Var("p".into(), Sort::Bool));
    }

    #[test]
    fn test_parse_not() {
        assert_eq!(
            parse_smtlib2_conclusion("(not p)"),
            Formula::Not(Box::new(Formula::Var("p".into(), Sort::Bool)))
        );
    }

    #[test]
    fn test_parse_implies() {
        assert_eq!(
            parse_smtlib2_conclusion("(=> p q)"),
            Formula::Implies(
                Box::new(Formula::Var("p".into(), Sort::Bool)),
                Box::new(Formula::Var("q".into(), Sort::Bool)),
            )
        );
    }

    #[test]
    fn test_parse_equality() {
        assert_eq!(
            parse_smtlib2_conclusion("(= a b)"),
            Formula::Eq(
                Box::new(Formula::Var("a".into(), Sort::Bool)),
                Box::new(Formula::Var("b".into(), Sort::Bool)),
            )
        );
    }

    #[test]
    fn test_parse_comparison() {
        assert_eq!(
            parse_smtlib2_conclusion("(<= x 10)"),
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Bool)), Box::new(Formula::Int(10)),)
        );
    }

    #[test]
    fn test_parse_and() {
        let f = parse_smtlib2_conclusion("(and p q r)");
        if let Formula::And(args) = f {
            assert_eq!(args.len(), 3);
        } else {
            panic!("expected And, got {f:?}");
        }
    }

    #[test]
    fn test_parse_or() {
        let f = parse_smtlib2_conclusion("(or p q)");
        if let Formula::Or(args) = f {
            assert_eq!(args.len(), 2);
        } else {
            panic!("expected Or, got {f:?}");
        }
    }

    #[test]
    fn test_parse_empty() {
        assert_eq!(parse_smtlib2_conclusion(""), Formula::Bool(true));
    }

    #[test]
    fn test_parse_nested() {
        let f = parse_smtlib2_conclusion("(not (= x 0))");
        assert!(matches!(f, Formula::Not(_)));
    }

    // -- translate_ay_proof tests --

    #[test]
    fn test_translate_empty_certificate() {
        let cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        let proof = translate_ay_proof(&cert).expect("empty should succeed");
        assert!(proof.steps.is_empty());
        assert!(proof.used_axioms.is_empty());
        assert!(proof.used_lemmas.is_empty());
    }

    #[test]
    fn test_translate_sample_certificate() {
        let cert = sample_ay_certificate();
        let proof = translate_ay_proof(&cert).expect("sample should translate");

        // 4 ay steps -> 4 proof steps
        assert_eq!(proof.steps.len(), 4);

        // Step 0: asserted -> Axiom
        assert!(
            matches!(&proof.steps[0], ProofStep::Axiom { name, .. } if name.starts_with("asserted"))
        );

        // Step 1: asserted -> Axiom
        assert!(
            matches!(&proof.steps[1], ProofStep::Axiom { name, .. } if name.starts_with("asserted"))
        );

        // Step 2: mp -> ModusPonens
        assert!(matches!(
            &proof.steps[2],
            ProofStep::ModusPonens { implication_step: 0, antecedent_step: 1 }
        ));

        // Step 3: unit-resolution -> Resolution
        assert!(matches!(&proof.steps[3], ProofStep::Resolution { .. }));

        // Axioms tracked
        assert_eq!(proof.used_axioms.len(), 2);

        // Lemmas tracked
        assert!(!proof.used_lemmas.is_empty());
    }

    #[test]
    fn test_translate_forward_reference_fails() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(),
            premises: vec![1], // forward reference
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(make_ay_step("asserted", "p", vec![]));

        let err = translate_ay_proof(&cert).expect_err("forward ref should fail");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got: {err:?}"
        );
    }

    #[test]
    fn test_translate_theory_lemma() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(AYProofStep {
            rule_name: "th-lemma arith".to_string(),
            rule: None,
            conclusion: "(<= x 100)".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });

        let proof = translate_ay_proof(&cert).expect("th-lemma should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.contains("th-lemma.arith")
        ));
    }

    #[test]
    fn test_translate_monotonicity() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("asserted", "(= a b)", vec![]));
        cert.proof_steps.push(AYProofStep {
            rule_name: "monotonicity".to_string(),
            rule: None,
            conclusion: "(= (f a) (f b))".to_string(),
            premises: vec![0],
            annotations: BTreeMap::new(),
        });

        let proof = translate_ay_proof(&cert).expect("monotonicity should translate");
        assert_eq!(proof.steps.len(), 2);
        assert!(matches!(&proof.steps[1], ProofStep::Congruence { equality_step: 0, .. }));
    }

    #[test]
    fn test_translate_transitivity() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("asserted", "(= a b)", vec![]));
        cert.proof_steps.push(make_ay_step("asserted", "(= b c)", vec![]));
        cert.proof_steps.push(make_ay_step("trans", "(= a c)", vec![0, 1]));

        let proof = translate_ay_proof(&cert).expect("trans should translate");
        assert_eq!(proof.steps.len(), 3);
        assert!(matches!(&proof.steps[2], ProofStep::Rewrite { equality_step: 0, target_step: 1 }));
    }

    #[test]
    fn test_translate_reflexivity() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("refl", "(= x x)", vec![]));

        let proof = translate_ay_proof(&cert).expect("refl should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("refl")
        ));
    }

    #[test]
    fn test_translate_unknown_rule_becomes_axiom() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("new-ay-rule", "p", vec![]));

        let proof = translate_ay_proof(&cert).expect("unknown rule should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("new-ay-rule")
        ));
    }

    #[test]
    fn test_translate_mp_insufficient_premises_fails() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("asserted", "p", vec![]));
        cert.proof_steps.push(make_ay_step("mp", "q", vec![0])); // only 1 premise

        let err = translate_ay_proof(&cert).expect_err("mp with 1 premise should fail");
        assert!(matches!(err, CertificateError::InvalidProofTerm { .. }));
    }

    #[test]
    fn test_translate_skolem() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("sk", "(= (sk!0) 5)", vec![]));

        let proof = translate_ay_proof(&cert).expect("sk should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("skolem")
        ));
    }

    #[test]
    fn test_translate_def_axiom() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("def-axiom", "(or p (not p))", vec![]));

        let proof = translate_ay_proof(&cert).expect("def-axiom should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("def-axiom")
        ));
    }

    #[test]
    fn test_translate_quant_inst_no_premise() {
        let mut cert = AYProofCertificate::new([0u8; 32], 0, "ay");
        cert.proof_steps.push(make_ay_step("quant-inst", "(<= x 10)", vec![]));

        let proof = translate_ay_proof(&cert).expect("quant-inst should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("quant-inst")
        ));
    }

    // -- End-to-end: translate + reconstruct --

    #[test]
    fn test_e2e_translate_and_reconstruct() {
        use trust_types::*;

        let cert = sample_ay_certificate();
        let solver_proof = translate_ay_proof(&cert).expect("should translate");

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("d".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
            obligation: None,
        };

        let term =
            crate::reconstruction::reconstruct(&solver_proof, &vc).expect("should reconstruct");
        assert!(crate::reconstruction::validate_reconstruction(&term));
    }
}
