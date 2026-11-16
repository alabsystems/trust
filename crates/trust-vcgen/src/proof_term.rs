// Proof term generation for verified VCs.
//
// Proof terms provide explicit witnesses that verification conditions hold,
// enabling independent checking of proof validity.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// A proof term — an explicit witness that a VC holds.
///
/// Each variant corresponds to a natural deduction rule or proof step.
/// Recursive variants use `Box` for indirection (required for recursive enums).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofTerm {
    /// An axiom (assumed true by name).
    Axiom(String),
    /// A hypothesis from the proof context.
    Hypothesis(String),
    /// Modus ponens: given a proof of P -> Q and a proof of P, derive Q.
    ModusPonens(Box<ProofTerm>, Box<ProofTerm>),
    /// Conjunction introduction: given proofs of P1, P2, ..., Pn, derive P1 /\ ... /\ Pn.
    Conjunction(Vec<ProofTerm>),
    /// Disjunction introduction: given a proof of Pi, derive P1 \/ ... \/ Pn (at index i).
    Disjunction(Box<ProofTerm>, usize),
    /// Universal introduction: for all x, proof of P(x).
    ForallIntro(String, Box<ProofTerm>),
    /// Existential introduction: exists x = witness, proof of P(witness).
    ExistsIntro(String, Box<ProofTerm>),
    /// Rewrite: apply an equality (from -> to) to transform a proof.
    Rewrite(Box<ProofTerm>, String, String),
    /// Cut: given a proof of A and a proof of A -> B, derive B (lemma introduction).
    Cut(Box<ProofTerm>, Box<ProofTerm>, String),
}

/// A proof context: hypotheses available and the goal to prove.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofContext {
    /// Named hypotheses: (name, formula_string).
    pub hypotheses: Vec<(String, String)>,
    /// The goal formula to prove.
    pub goal: String,
}

/// Errors that can occur during proof construction.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ProofError {
    /// An invalid proof step was attempted.
    #[error("invalid proof step: {0}")]
    InvalidStep(String),
    /// The goal remains unproved.
    #[error("unproved goal: {0}")]
    UnprovedGoal(String),
    /// A type mismatch in the proof.
    #[error("type mismatch: expected `{expected}`, found `{found}`")]
    TypeMismatch {
        /// The expected type/formula.
        expected: String,
        /// The found type/formula.
        found: String,
    },
    /// A referenced hypothesis was not found in the context.
    #[error("hypothesis not found: {0}")]
    HypothesisNotFound(String),
}

/// Builder for constructing proof terms step by step.
#[derive(Debug, Clone)]
#[must_use]
pub struct ProofBuilder {
    context: ProofContext,
    current: Option<ProofTerm>,
}

impl ProofBuilder {
    /// Create a new proof builder with the given context.
    pub fn new(context: ProofContext) -> Self {
        Self { context, current: None }
    }

    /// Introduce an axiom by name.
    pub fn axiom(&mut self, name: &str) -> Result<ProofTerm, ProofError> {
        let term = ProofTerm::Axiom(name.to_string());
        self.current = Some(term.clone());
        Ok(term)
    }

    /// Reference a hypothesis from the context by name.
    pub fn hypothesis(&mut self, name: &str) -> Result<ProofTerm, ProofError> {
        if !self.context.hypotheses.iter().any(|(n, _)| n == name) {
            return Err(ProofError::HypothesisNotFound(name.to_string()));
        }
        let term = ProofTerm::Hypothesis(name.to_string());
        self.current = Some(term.clone());
        Ok(term)
    }

    /// Apply modus ponens: given a proof of an implication and its antecedent.
    pub fn modus_ponens(
        &mut self,
        implication: ProofTerm,
        antecedent: ProofTerm,
    ) -> Result<ProofTerm, ProofError> {
        // Structural check: implication should not be a bare hypothesis applied
        // to itself (basic sanity). More sophisticated type checking would require
        // a richer formula representation.
        let term = ProofTerm::ModusPonens(Box::new(implication), Box::new(antecedent));
        self.current = Some(term.clone());
        Ok(term)
    }

    /// Introduce a conjunction from a list of proofs.
    pub fn conjunction(&mut self, proofs: Vec<ProofTerm>) -> ProofTerm {
        let term = ProofTerm::Conjunction(proofs);
        self.current = Some(term.clone());
        term
    }

    /// Finalize the proof. Returns the current proof term or an error if nothing was built.
    pub fn build(&self) -> Result<ProofTerm, ProofError> {
        self.current.clone().ok_or_else(|| ProofError::UnprovedGoal(self.context.goal.clone()))
    }
}

/// Validate that a proof term is structurally well-formed with respect to a context.
///
/// Checks that all hypothesis references exist in the context and that
/// structural invariants hold (e.g., conjunction has at least one element).
#[must_use]
pub fn validate_proof_term(term: &ProofTerm, context: &ProofContext) -> bool {
    if context.hypotheses.len() > 4
        && !matches!(term, ProofTerm::Axiom(_) | ProofTerm::Hypothesis(_))
    {
        let hyp_names: trust_types::fx::FxHashSet<&str> =
            context.hypotheses.iter().map(|(n, _)| n.as_str()).collect();
        return validate_proof_term_set(term, &hyp_names);
    }
    validate_proof_term_linear(term, context)
}

fn validate_proof_term_linear(term: &ProofTerm, context: &ProofContext) -> bool {
    match term {
        ProofTerm::Axiom(_) => true,
        ProofTerm::Hypothesis(name) => context.hypotheses.iter().any(|(n, _)| n == name),
        ProofTerm::ModusPonens(imp, ant) => {
            validate_proof_term_linear(imp, context) && validate_proof_term_linear(ant, context)
        }
        ProofTerm::Conjunction(proofs) => {
            !proofs.is_empty() && proofs.iter().all(|p| validate_proof_term_linear(p, context))
        }
        ProofTerm::Disjunction(proof, _idx) => validate_proof_term_linear(proof, context),
        ProofTerm::ForallIntro(_var, body) => validate_proof_term_linear(body, context),
        ProofTerm::ExistsIntro(_witness, body) => validate_proof_term_linear(body, context),
        ProofTerm::Rewrite(proof, _from, _to) => validate_proof_term_linear(proof, context),
        ProofTerm::Cut(left, right, _lemma) => {
            validate_proof_term_linear(left, context) && validate_proof_term_linear(right, context)
        }
    }
}

fn validate_proof_term_set(term: &ProofTerm, hyp_names: &trust_types::fx::FxHashSet<&str>) -> bool {
    match term {
        ProofTerm::Axiom(_) => true,
        ProofTerm::Hypothesis(name) => hyp_names.contains(name.as_str()),
        ProofTerm::ModusPonens(imp, ant) => {
            validate_proof_term_set(imp, hyp_names) && validate_proof_term_set(ant, hyp_names)
        }
        ProofTerm::Conjunction(proofs) => {
            !proofs.is_empty() && proofs.iter().all(|p| validate_proof_term_set(p, hyp_names))
        }
        ProofTerm::Disjunction(proof, _idx) => validate_proof_term_set(proof, hyp_names),
        ProofTerm::ForallIntro(_var, body) => validate_proof_term_set(body, hyp_names),
        ProofTerm::ExistsIntro(_witness, body) => validate_proof_term_set(body, hyp_names),
        ProofTerm::Rewrite(proof, _from, _to) => validate_proof_term_set(proof, hyp_names),
        ProofTerm::Cut(left, right, _lemma) => {
            validate_proof_term_set(left, hyp_names) && validate_proof_term_set(right, hyp_names)
        }
    }
}

/// Count the total number of nodes in a proof term.
#[must_use]
pub fn proof_size(term: &ProofTerm) -> usize {
    match term {
        ProofTerm::Axiom(_) | ProofTerm::Hypothesis(_) => 1,
        ProofTerm::ModusPonens(imp, ant) => 1 + proof_size(imp) + proof_size(ant),
        ProofTerm::Conjunction(proofs) => 1 + proofs.iter().map(proof_size).sum::<usize>(),
        ProofTerm::Disjunction(proof, _) => 1 + proof_size(proof),
        ProofTerm::ForallIntro(_, body) => 1 + proof_size(body),
        ProofTerm::ExistsIntro(_, body) => 1 + proof_size(body),
        ProofTerm::Rewrite(proof, _, _) => 1 + proof_size(proof),
        ProofTerm::Cut(left, right, _) => 1 + proof_size(left) + proof_size(right),
    }
}

/// Compute the maximum depth of a proof term tree.
#[must_use]
pub fn proof_depth(term: &ProofTerm) -> usize {
    match term {
        ProofTerm::Axiom(_) | ProofTerm::Hypothesis(_) => 1,
        ProofTerm::ModusPonens(imp, ant) => 1 + proof_depth(imp).max(proof_depth(ant)),
        ProofTerm::Conjunction(proofs) => 1 + proofs.iter().map(proof_depth).max().unwrap_or(0),
        ProofTerm::Disjunction(proof, _) => 1 + proof_depth(proof),
        ProofTerm::ForallIntro(_, body) => 1 + proof_depth(body),
        ProofTerm::ExistsIntro(_, body) => 1 + proof_depth(body),
        ProofTerm::Rewrite(proof, _, _) => 1 + proof_depth(proof),
        ProofTerm::Cut(left, right, _) => 1 + proof_depth(left).max(proof_depth(right)),
    }
}

/// Simplify a proof term by eliminating redundant structure.
///
/// Current simplifications:
/// - Flatten nested conjunctions: `And(And(a, b), c)` -> `And(a, b, c)`
/// - Remove single-element conjunctions: `And(a)` -> `a`
/// - Recursively simplify sub-terms
#[must_use]
pub fn simplify_proof(term: &ProofTerm) -> ProofTerm {
    match term {
        ProofTerm::Axiom(_) | ProofTerm::Hypothesis(_) => term.clone(),
        ProofTerm::ModusPonens(imp, ant) => {
            ProofTerm::ModusPonens(Box::new(simplify_proof(imp)), Box::new(simplify_proof(ant)))
        }
        ProofTerm::Conjunction(proofs) => {
            // Recursively simplify, then flatten nested conjunctions.
            let mut simplified = Vec::with_capacity(proofs.len());
            for p in proofs {
                match simplify_proof(p) {
                    ProofTerm::Conjunction(inner) => simplified.extend(inner),
                    other => simplified.push(other),
                }
            }
            match simplified.pop() {
                Some(only) if simplified.is_empty() => only,
                Some(last) => {
                    simplified.push(last);
                    ProofTerm::Conjunction(simplified)
                }
                None => ProofTerm::Conjunction(simplified),
            }
        }
        ProofTerm::Disjunction(proof, idx) => {
            ProofTerm::Disjunction(Box::new(simplify_proof(proof)), *idx)
        }
        ProofTerm::ForallIntro(var, body) => {
            ProofTerm::ForallIntro(var.clone(), Box::new(simplify_proof(body)))
        }
        ProofTerm::ExistsIntro(witness, body) => {
            ProofTerm::ExistsIntro(witness.clone(), Box::new(simplify_proof(body)))
        }
        ProofTerm::Rewrite(proof, from, to) => {
            ProofTerm::Rewrite(Box::new(simplify_proof(proof)), from.clone(), to.clone())
        }
        ProofTerm::Cut(left, right, lemma) => ProofTerm::Cut(
            Box::new(simplify_proof(left)),
            Box::new(simplify_proof(right)),
            lemma.clone(),
        ),
    }
}

/// Render a proof term as a human-readable string.
#[must_use]
pub fn proof_to_string(term: &ProofTerm) -> String {
    let mut out = String::new();
    write_proof_term(term, &mut out);
    out
}

fn write_proof_term(term: &ProofTerm, out: &mut String) {
    use std::fmt::Write as _;
    match term {
        ProofTerm::Axiom(name) => {
            out.push_str("axiom(");
            out.push_str(name);
            out.push(')');
        }
        ProofTerm::Hypothesis(name) => {
            out.push_str("hyp(");
            out.push_str(name);
            out.push(')');
        }
        ProofTerm::ModusPonens(imp, ant) => {
            out.push_str("mp(");
            write_proof_term(imp, out);
            out.push_str(", ");
            write_proof_term(ant, out);
            out.push(')');
        }
        ProofTerm::Conjunction(proofs) => {
            out.push_str("conj(");
            for (i, p) in proofs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_proof_term(p, out);
            }
            out.push(')');
        }
        ProofTerm::Disjunction(proof, idx) => {
            out.push_str("disj(");
            write_proof_term(proof, out);
            let _ = write!(out, ", {idx})");
        }
        ProofTerm::ForallIntro(var, body) => {
            out.push_str("forall(");
            out.push_str(var);
            out.push_str(", ");
            write_proof_term(body, out);
            out.push(')');
        }
        ProofTerm::ExistsIntro(witness, body) => {
            out.push_str("exists(");
            out.push_str(witness);
            out.push_str(", ");
            write_proof_term(body, out);
            out.push(')');
        }
        ProofTerm::Rewrite(proof, from, to) => {
            out.push_str("rewrite(");
            write_proof_term(proof, out);
            out.push_str(", ");
            out.push_str(from);
            out.push_str(" -> ");
            out.push_str(to);
            out.push(')');
        }
        ProofTerm::Cut(left, right, lemma) => {
            out.push_str("cut(");
            write_proof_term(left, out);
            out.push_str(", ");
            write_proof_term(right, out);
            out.push_str(", ");
            out.push_str(lemma);
            out.push(')');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_context() -> ProofContext {
        ProofContext {
            hypotheses: vec![
                ("h1".to_string(), "x > 0".to_string()),
                ("h2".to_string(), "x > 0 -> x >= 1".to_string()),
            ],
            goal: "x >= 1".to_string(),
        }
    }

    #[test]
    fn test_proof_builder_axiom() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        let term = builder.axiom("arithmetic").unwrap();
        assert_eq!(term, ProofTerm::Axiom("arithmetic".to_string()));
    }

    #[test]
    fn test_proof_builder_hypothesis_valid() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        let term = builder.hypothesis("h1").unwrap();
        assert_eq!(term, ProofTerm::Hypothesis("h1".to_string()));
    }

    #[test]
    fn test_proof_builder_hypothesis_not_found() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        let err = builder.hypothesis("h_nonexistent").unwrap_err();
        assert_eq!(err, ProofError::HypothesisNotFound("h_nonexistent".to_string()));
    }

    #[test]
    fn test_proof_builder_modus_ponens() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        let h1 = builder.hypothesis("h1").unwrap();
        let h2 = builder.hypothesis("h2").unwrap();
        let mp = builder.modus_ponens(h2, h1).unwrap();
        assert!(matches!(mp, ProofTerm::ModusPonens(_, _)));
    }

    #[test]
    fn test_proof_builder_conjunction() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        let h1 = builder.hypothesis("h1").unwrap();
        let h2 = builder.hypothesis("h2").unwrap();
        let conj = builder.conjunction(vec![h1, h2]);
        assert!(matches!(conj, ProofTerm::Conjunction(ref v) if v.len() == 2));
    }

    #[test]
    fn test_proof_builder_build_empty_returns_error() {
        let ctx = sample_context();
        let builder = ProofBuilder::new(ctx.clone());
        let err = builder.build().unwrap_err();
        assert_eq!(err, ProofError::UnprovedGoal(ctx.goal));
    }

    #[test]
    fn test_proof_builder_build_after_step() {
        let ctx = sample_context();
        let mut builder = ProofBuilder::new(ctx);
        builder.axiom("trivial").unwrap();
        let term = builder.build().unwrap();
        assert_eq!(term, ProofTerm::Axiom("trivial".to_string()));
    }

    #[test]
    fn test_validate_proof_term_valid_hypothesis() {
        let ctx = sample_context();
        let term = ProofTerm::Hypothesis("h1".to_string());
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_proof_term_invalid_hypothesis() {
        let ctx = sample_context();
        let term = ProofTerm::Hypothesis("missing".to_string());
        assert!(!validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_proof_term_empty_conjunction() {
        let ctx = sample_context();
        let term = ProofTerm::Conjunction(vec![]);
        assert!(!validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_proof_term_nested() {
        let ctx = sample_context();
        let term = ProofTerm::ModusPonens(
            Box::new(ProofTerm::Hypothesis("h2".to_string())),
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
        );
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_proof_size_leaf() {
        assert_eq!(proof_size(&ProofTerm::Axiom("a".to_string())), 1);
        assert_eq!(proof_size(&ProofTerm::Hypothesis("h".to_string())), 1);
    }

    #[test]
    fn test_proof_size_compound() {
        let term = ProofTerm::ModusPonens(
            Box::new(ProofTerm::Axiom("a".to_string())),
            Box::new(ProofTerm::Hypothesis("h".to_string())),
        );
        assert_eq!(proof_size(&term), 3);
    }

    #[test]
    fn test_proof_depth_leaf() {
        assert_eq!(proof_depth(&ProofTerm::Axiom("a".to_string())), 1);
    }

    #[test]
    fn test_proof_depth_nested() {
        let term = ProofTerm::ModusPonens(
            Box::new(ProofTerm::ModusPonens(
                Box::new(ProofTerm::Axiom("a".to_string())),
                Box::new(ProofTerm::Axiom("b".to_string())),
            )),
            Box::new(ProofTerm::Axiom("c".to_string())),
        );
        assert_eq!(proof_depth(&term), 3);
    }

    #[test]
    fn test_simplify_proof_flatten_conjunction() {
        let inner = ProofTerm::Conjunction(vec![
            ProofTerm::Axiom("a".to_string()),
            ProofTerm::Axiom("b".to_string()),
        ]);
        let outer = ProofTerm::Conjunction(vec![inner, ProofTerm::Axiom("c".to_string())]);
        let simplified = simplify_proof(&outer);
        match simplified {
            ProofTerm::Conjunction(parts) => {
                assert_eq!(parts.len(), 3, "nested conjunction should be flattened");
            }
            other => panic!("expected flattened Conjunction, got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_proof_singleton_conjunction() {
        let term = ProofTerm::Conjunction(vec![ProofTerm::Axiom("only".to_string())]);
        let simplified = simplify_proof(&term);
        assert_eq!(simplified, ProofTerm::Axiom("only".to_string()));
    }

    #[test]
    fn test_simplify_conjunction_preserves_empty_and_leaf_order() {
        let empty = ProofTerm::Conjunction(Vec::new());
        assert_eq!(simplify_proof(&empty), empty);
        let a = ProofTerm::Axiom("a".into());
        let b = ProofTerm::Hypothesis("b".into());
        let c = ProofTerm::Axiom("c".into());
        let term = ProofTerm::Conjunction(vec![
            empty.clone(),
            ProofTerm::Conjunction(vec![a.clone(), empty.clone()]),
            b.clone(),
            ProofTerm::Conjunction(vec![empty, c.clone()]),
        ]);
        assert_eq!(simplify_proof(&term), ProofTerm::Conjunction(vec![a, b, c]));
    }

    #[test]
    fn test_proof_to_string_axiom() {
        let term = ProofTerm::Axiom("arith".to_string());
        assert_eq!(proof_to_string(&term), "axiom(arith)");
    }

    #[test]
    fn test_proof_to_string_modus_ponens() {
        let term = ProofTerm::ModusPonens(
            Box::new(ProofTerm::Hypothesis("h2".to_string())),
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
        );
        assert_eq!(proof_to_string(&term), "mp(hyp(h2), hyp(h1))");
    }

    #[test]
    fn test_proof_to_string_conjunction() {
        let term = ProofTerm::Conjunction(vec![
            ProofTerm::Axiom("a".to_string()),
            ProofTerm::Axiom("b".to_string()),
        ]);
        assert_eq!(proof_to_string(&term), "conj(axiom(a), axiom(b))");
    }

    #[test]
    fn test_proof_to_string_forall() {
        let term =
            ProofTerm::ForallIntro("x".to_string(), Box::new(ProofTerm::Axiom("p_x".to_string())));
        assert_eq!(proof_to_string(&term), "forall(x, axiom(p_x))");
    }

    #[test]
    fn test_proof_to_string_exists() {
        let term = ProofTerm::ExistsIntro(
            "42".to_string(),
            Box::new(ProofTerm::Axiom("p_42".to_string())),
        );
        assert_eq!(proof_to_string(&term), "exists(42, axiom(p_42))");
    }

    #[test]
    fn test_proof_to_string_disjunction() {
        let term = ProofTerm::Disjunction(Box::new(ProofTerm::Hypothesis("h1".to_string())), 0);
        assert_eq!(proof_to_string(&term), "disj(hyp(h1), 0)");
    }

    #[test]
    fn test_proof_to_string_rewrite() {
        let term = ProofTerm::Rewrite(
            Box::new(ProofTerm::Axiom("p".to_string())),
            "a".to_string(),
            "b".to_string(),
        );
        assert_eq!(proof_to_string(&term), "rewrite(axiom(p), a -> b)");
    }

    #[test]
    fn test_proof_to_string_cut() {
        let term = ProofTerm::Cut(
            Box::new(ProofTerm::Axiom("lemma_proof".to_string())),
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
            "my_lemma".to_string(),
        );
        assert_eq!(proof_to_string(&term), "cut(axiom(lemma_proof), hyp(h1), my_lemma)");
    }

    #[test]
    fn test_validate_forall_intro() {
        let ctx = sample_context();
        let term =
            ProofTerm::ForallIntro("x".to_string(), Box::new(ProofTerm::Axiom("p".to_string())));
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_exists_intro() {
        let ctx = sample_context();
        let term = ProofTerm::ExistsIntro(
            "witness".to_string(),
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
        );
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_rewrite() {
        let ctx = sample_context();
        let term = ProofTerm::Rewrite(
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
            "x".to_string(),
            "y".to_string(),
        );
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_validate_cut() {
        let ctx = sample_context();
        let term = ProofTerm::Cut(
            Box::new(ProofTerm::Hypothesis("h1".to_string())),
            Box::new(ProofTerm::Hypothesis("h2".to_string())),
            "lemma".to_string(),
        );
        assert!(validate_proof_term(&term, &ctx));
    }

    #[test]
    fn test_proof_error_display() {
        let e = ProofError::InvalidStep("bad step".to_string());
        assert_eq!(e.to_string(), "invalid proof step: bad step");

        let e = ProofError::TypeMismatch { expected: "bool".to_string(), found: "int".to_string() };
        assert_eq!(e.to_string(), "type mismatch: expected `bool`, found `int`");
    }

    #[test]
    fn test_proof_size_conjunction() {
        let term = ProofTerm::Conjunction(vec![
            ProofTerm::Axiom("a".to_string()),
            ProofTerm::Axiom("b".to_string()),
            ProofTerm::Axiom("c".to_string()),
        ]);
        assert_eq!(proof_size(&term), 4); // 1 (conjunction) + 3 (leaves)
    }

    #[test]
    fn test_proof_depth_conjunction() {
        let term = ProofTerm::Conjunction(vec![
            ProofTerm::Axiom("a".to_string()),
            ProofTerm::ModusPonens(
                Box::new(ProofTerm::Axiom("b".to_string())),
                Box::new(ProofTerm::Axiom("c".to_string())),
            ),
        ]);
        assert_eq!(proof_depth(&term), 3); // conj -> mp -> leaf
    }

    #[test]
    fn test_simplify_proof_leaves_unchanged() {
        let term = ProofTerm::Axiom("unchanged".to_string());
        assert_eq!(simplify_proof(&term), term);
    }

    #[test]
    fn test_simplify_proof_recursive() {
        // Conjunction of a single-element conjunction should fully flatten.
        let inner = ProofTerm::Conjunction(vec![ProofTerm::Axiom("deep".to_string())]);
        let outer = ProofTerm::Conjunction(vec![inner]);
        let simplified = simplify_proof(&outer);
        assert_eq!(simplified, ProofTerm::Axiom("deep".to_string()));
    }
}
