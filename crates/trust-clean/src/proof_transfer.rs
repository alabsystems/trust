// trust-clean/proof_transfer.rs: Proof transfer between lemmas
//
// Finds proven lemmas whose proofs can be adapted to new goals via
// structural similarity analysis. Supports direct application, renaming,
// specialization, generalization, and hypothesis addition.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

// ---------------------------------------------------------------------------
// Adaptation — a single proof modification step
// ---------------------------------------------------------------------------

/// A single modification needed to adapt a proof from one lemma to another.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Adaptation {
    /// Rename a variable or lemma reference.
    Rename { from: String, to: String },
    /// Specialize a universally quantified variable to a concrete term.
    Specialize { variable: String, term: Formula },
    /// Generalize a concrete subexpression to a fresh variable.
    Generalize { term: Formula, variable: String },
    /// Add an extra hypothesis that the target lemma requires.
    AddHypothesis { hypothesis: Formula },
}

// ---------------------------------------------------------------------------
// LemmaSignature — the statement of a lemma
// ---------------------------------------------------------------------------

/// The logical signature of a lemma: its name, hypotheses, and conclusion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LemmaSignature {
    /// Fully qualified lemma name.
    pub name: String,
    /// Hypotheses (preconditions) of the lemma.
    pub hypotheses: Vec<Formula>,
    /// The conclusion (goal) the lemma proves.
    pub conclusion: Formula,
}

// ---------------------------------------------------------------------------
// TransferCandidate — a potential proof donor
// ---------------------------------------------------------------------------

/// A candidate lemma whose proof may transfer to a new goal.
///
/// Contains the source lemma, a similarity score (0.0 = unrelated,
/// 1.0 = identical), and the adaptations required. Because `score`
/// is `f64`, this type derives only `PartialEq` (not `Eq`).
#[derive(Debug, Clone, PartialEq)]
pub struct TransferCandidate {
    /// The proven lemma whose proof might transfer.
    pub source: LemmaSignature,
    /// Structural similarity between source and target (0.0..=1.0).
    pub score: f64,
    /// Adaptations needed to make the source proof fit the target.
    pub required_adaptations: Vec<Adaptation>,
}

// ---------------------------------------------------------------------------
// TransferResult — outcome of a transfer attempt
// ---------------------------------------------------------------------------

/// The result of attempting to transfer a proof from one lemma to another.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TransferResult {
    /// The source proof applies directly with no changes.
    DirectApply,
    /// The source proof applies after the listed adaptations.
    NeedsAdaptation(Vec<Adaptation>),
    /// No viable transfer path exists.
    NoTransfer,
}

// ---------------------------------------------------------------------------
// similarity_score — structural similarity between two lemma signatures
// ---------------------------------------------------------------------------

/// Compute structural similarity between two lemma signatures.
///
/// Returns a value in `[0.0, 1.0]` where 1.0 means structurally identical
/// and 0.0 means completely unrelated. The score blends conclusion similarity
/// (weighted 0.6) with hypothesis overlap (weighted 0.4).
#[must_use]
pub fn similarity_score(a: &LemmaSignature, b: &LemmaSignature) -> f64 {
    let conclusion_sim = formula_similarity(&a.conclusion, &b.conclusion);

    let hyp_sim = if a.hypotheses.is_empty() && b.hypotheses.is_empty() {
        1.0
    } else if a.hypotheses.is_empty() || b.hypotheses.is_empty() {
        0.0
    } else {
        hypothesis_overlap(&a.hypotheses, &b.hypotheses)
    };

    conclusion_sim * 0.6 + hyp_sim * 0.4
}

/// Structural similarity between two formulas.
///
/// Returns 1.0 for identical structure, fractional values for partial match,
/// and 0.0 for completely different shapes.
fn formula_similarity(a: &Formula, b: &Formula) -> f64 {
    match (a, b) {
        // Exact match
        _ if a == b => 1.0,

        // Same top-level constructor, compare children
        (Formula::Not(x), Formula::Not(y)) => formula_similarity(x, y),
        (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
            vec_formula_similarity(xs, ys)
        }
        (Formula::Implies(p1, q1), Formula::Implies(p2, q2)) => {
            (formula_similarity(p1, p2) + formula_similarity(q1, q2)) / 2.0
        }
        (Formula::Eq(l1, r1), Formula::Eq(l2, r2))
        | (Formula::Lt(l1, r1), Formula::Lt(l2, r2))
        | (Formula::Le(l1, r1), Formula::Le(l2, r2))
        | (Formula::Gt(l1, r1), Formula::Gt(l2, r2))
        | (Formula::Ge(l1, r1), Formula::Ge(l2, r2))
        | (Formula::Add(l1, r1), Formula::Add(l2, r2))
        | (Formula::Sub(l1, r1), Formula::Sub(l2, r2))
        | (Formula::Mul(l1, r1), Formula::Mul(l2, r2))
        | (Formula::Div(l1, r1), Formula::Div(l2, r2)) => {
            (formula_similarity(l1, l2) + formula_similarity(r1, r2)) / 2.0
        }
        (Formula::Neg(x), Formula::Neg(y)) => formula_similarity(x, y),

        // Variables with same sort but different name: high similarity
        (Formula::Var(_, s1), Formula::Var(_, s2)) if s1 == s2 => 0.8,
        // Variables with different sort: low similarity
        (Formula::Var(_, _), Formula::Var(_, _)) => 0.2,

        // Same constructor family (both boolean, both arithmetic) but
        // different specific connective: partial credit
        (Formula::And(_), Formula::Or(_)) | (Formula::Or(_), Formula::And(_)) => 0.3,
        (Formula::Lt(_, _), Formula::Le(_, _))
        | (Formula::Le(_, _), Formula::Lt(_, _))
        | (Formula::Gt(_, _), Formula::Ge(_, _))
        | (Formula::Ge(_, _), Formula::Gt(_, _)) => 0.5,

        // Everything else: no structural similarity
        _ => 0.0,
    }
}

/// Average pairwise similarity between two lists of formulas.
fn vec_formula_similarity(xs: &[Formula], ys: &[Formula]) -> f64 {
    if xs.is_empty() && ys.is_empty() {
        return 1.0;
    }
    let max_len = xs.len().max(ys.len());
    if max_len == 0 {
        return 1.0;
    }
    let paired_sim: f64 = xs.iter().zip(ys.iter()).map(|(x, y)| formula_similarity(x, y)).sum();
    paired_sim / max_len as f64
}

/// Fraction of hypotheses in `a` that have a close match in `b`.
fn hypothesis_overlap(a: &[Formula], b: &[Formula]) -> f64 {
    if a.is_empty() {
        return if b.is_empty() { 1.0 } else { 0.0 };
    }
    let matches: f64 = a
        .iter()
        .map(|ha| b.iter().map(|hb| formula_similarity(ha, hb)).fold(0.0_f64, f64::max))
        .sum();
    matches / a.len() as f64
}

// ---------------------------------------------------------------------------
// find_transferable — search for proof donors
// ---------------------------------------------------------------------------

/// Minimum similarity threshold for considering a transfer candidate.
///
/// Raised from 0.3 to 0.5 per audit finding F17: a 30% threshold
/// wastes solver resources on proofs unlikely to type-check, and if the
/// kernel has bugs, incorrect proofs could slip through.
const TRANSFER_THRESHOLD: f64 = 0.5;

/// Search a library of proven lemmas for proofs that may transfer to `target`.
///
/// Returns candidates sorted by descending similarity score. Only lemmas
/// with similarity above [`TRANSFER_THRESHOLD`] are included.
#[must_use]
pub fn find_transferable(
    library: &[LemmaSignature],
    target: &LemmaSignature,
) -> Vec<TransferCandidate> {
    let mut candidates: Vec<TransferCandidate> = library
        .iter()
        .filter(|src| src.name != target.name)
        .filter_map(|src| {
            let score = similarity_score(src, target);
            if score >= TRANSFER_THRESHOLD {
                let required_adaptations = compute_adaptations(src, target);
                Some(TransferCandidate { source: src.clone(), score, required_adaptations })
            } else {
                None
            }
        })
        .collect();

    // Sort by descending score (total_cmp handles NaN safely)
    candidates.sort_by(|a, b| b.score.total_cmp(&a.score));
    candidates
}

// ---------------------------------------------------------------------------
// adapt_proof — apply adaptations to transfer a proof
// ---------------------------------------------------------------------------

/// Attempt to adapt a source lemma's proof to prove the target lemma.
///
/// Returns `DirectApply` if the lemmas are structurally identical,
/// `NeedsAdaptation` with the required changes, or `NoTransfer` if the
/// similarity is below threshold.
#[must_use]
pub fn adapt_proof(source: &LemmaSignature, target: &LemmaSignature) -> TransferResult {
    let score = similarity_score(source, target);

    if score < TRANSFER_THRESHOLD {
        return TransferResult::NoTransfer;
    }

    // Identical structure: direct application
    if source.conclusion == target.conclusion && source.hypotheses == target.hypotheses {
        return TransferResult::DirectApply;
    }

    let adaptations = compute_adaptations(source, target);
    if adaptations.is_empty() {
        // Same score but no adaptations computed — structures match modulo
        // naming, which is still a direct apply.
        TransferResult::DirectApply
    } else {
        TransferResult::NeedsAdaptation(adaptations)
    }
}

// ---------------------------------------------------------------------------
// compute_adaptations — diff two signatures into adaptation steps
// ---------------------------------------------------------------------------

/// Compute the adaptations needed to convert a source proof into a target proof.
fn compute_adaptations(source: &LemmaSignature, target: &LemmaSignature) -> Vec<Adaptation> {
    let mut adaptations = Vec::new();

    // Check for variable renames between conclusions
    collect_renames(&source.conclusion, &target.conclusion, &mut adaptations);

    // Check for extra hypotheses in target that source lacks
    for th in &target.hypotheses {
        let has_match = source.hypotheses.iter().any(|sh| formula_similarity(sh, th) > 0.7);
        if !has_match {
            adaptations.push(Adaptation::AddHypothesis { hypothesis: th.clone() });
        }
    }

    // Deduplicate renames
    adaptations.dedup();
    adaptations
}

/// Collect variable renames by walking two formulas in parallel.
fn collect_renames(src: &Formula, tgt: &Formula, out: &mut Vec<Adaptation>) {
    match (src, tgt) {
        (Formula::Var(a, sa), Formula::Var(b, sb)) if sa == sb && a != b => {
            let rename = Adaptation::Rename { from: a.clone(), to: b.clone() };
            if !out.contains(&rename) {
                out.push(rename);
            }
        }
        (Formula::Not(x), Formula::Not(y)) => collect_renames(x, y, out),
        (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
            for (x, y) in xs.iter().zip(ys.iter()) {
                collect_renames(x, y, out);
            }
        }
        (Formula::Implies(p1, q1), Formula::Implies(p2, q2))
        | (Formula::Eq(p1, q1), Formula::Eq(p2, q2))
        | (Formula::Lt(p1, q1), Formula::Lt(p2, q2))
        | (Formula::Le(p1, q1), Formula::Le(p2, q2))
        | (Formula::Gt(p1, q1), Formula::Gt(p2, q2))
        | (Formula::Ge(p1, q1), Formula::Ge(p2, q2))
        | (Formula::Add(p1, q1), Formula::Add(p2, q2))
        | (Formula::Sub(p1, q1), Formula::Sub(p2, q2))
        | (Formula::Mul(p1, q1), Formula::Mul(p2, q2))
        | (Formula::Div(p1, q1), Formula::Div(p2, q2)) => {
            collect_renames(p1, p2, out);
            collect_renames(q1, q2, out);
        }
        (Formula::Neg(x), Formula::Neg(y)) => collect_renames(x, y, out),
        _ => {}
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    // Helpers
    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn sig(name: &str, hyps: Vec<Formula>, conclusion: Formula) -> LemmaSignature {
        LemmaSignature { name: name.to_string(), hypotheses: hyps, conclusion }
    }

    // --- 1. Identical lemmas have similarity 1.0 ---
    #[test]
    fn test_similarity_score_identical_returns_one() {
        let a = sig("lem", vec![var("x")], Formula::Bool(true));
        let b = a.clone();
        let score = similarity_score(&a, &b);
        assert!((score - 1.0).abs() < f64::EPSILON, "expected 1.0, got {score}");
    }

    // --- 2. Completely different lemmas have low similarity ---
    #[test]
    fn test_similarity_score_unrelated_returns_low() {
        let a = sig("a", vec![], Formula::Bool(true));
        let b = sig("b", vec![var("x"), var("y")], Formula::Int(42));
        let score = similarity_score(&a, &b);
        assert!(score < 0.3, "expected < 0.3, got {score}");
    }

    // --- 3. Variable rename detected ---
    #[test]
    fn test_similarity_score_renamed_variable_high() {
        let a = sig("lem_a", vec![], Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));
        let b = sig("lem_b", vec![], Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))));
        let score = similarity_score(&a, &b);
        // Var same sort ≠ name → 0.8, combined with Int match → high
        assert!(score > 0.5, "expected > 0.5, got {score}");
    }

    // --- 4. find_transferable returns empty for no matches ---
    #[test]
    fn test_find_transferable_empty_library() {
        let target = sig("goal", vec![], Formula::Bool(true));
        let result = find_transferable(&[], &target);
        assert!(result.is_empty());
    }

    // --- 5. find_transferable excludes self ---
    #[test]
    fn test_find_transferable_excludes_self() {
        let lemma = sig("goal", vec![], Formula::Bool(true));
        let result = find_transferable(std::slice::from_ref(&lemma), &lemma);
        assert!(result.is_empty(), "should exclude lemma with same name");
    }

    // --- 6. find_transferable returns sorted candidates ---
    #[test]
    fn test_find_transferable_sorted_by_score() {
        let target =
            sig("goal", vec![], Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));
        // Close match: same shape, different var name
        let close =
            sig("close", vec![], Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))));
        // Distant match: different structure entirely
        let distant = sig("distant", vec![], Formula::Lt(Box::new(var("a")), Box::new(var("b"))));

        let results = find_transferable(&[distant.clone(), close.clone()], &target);
        assert!(!results.is_empty());
        // First result should be the closer match
        assert_eq!(results[0].source.name, "close");
    }

    // --- 7. adapt_proof returns DirectApply for identical ---
    #[test]
    fn test_adapt_proof_direct_apply() {
        let a = sig("src", vec![Formula::Bool(true)], Formula::Bool(false));
        let b = sig("tgt", vec![Formula::Bool(true)], Formula::Bool(false));
        let result = adapt_proof(&a, &b);
        assert_eq!(result, TransferResult::DirectApply);
    }

    // --- 8. adapt_proof returns NoTransfer for unrelated ---
    #[test]
    fn test_adapt_proof_no_transfer() {
        let a = sig("src", vec![], Formula::Bool(true));
        let b = sig("tgt", vec![var("x"), var("y"), var("z")], Formula::Int(999));
        let result = adapt_proof(&a, &b);
        assert_eq!(result, TransferResult::NoTransfer);
    }

    // --- 9. adapt_proof returns NeedsAdaptation with renames ---
    #[test]
    fn test_adapt_proof_needs_rename() {
        let a = sig("src", vec![], Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));
        let b = sig("tgt", vec![], Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))));
        let result = adapt_proof(&a, &b);
        match result {
            TransferResult::NeedsAdaptation(adaptations) => {
                assert!(
                    adaptations.contains(&Adaptation::Rename {
                        from: "x".to_string(),
                        to: "y".to_string(),
                    }),
                    "expected Rename adaptation, got {adaptations:?}"
                );
            }
            other => panic!("expected NeedsAdaptation, got {other:?}"),
        }
    }

    // --- 10. adapt_proof detects AddHypothesis ---
    #[test]
    fn test_adapt_proof_add_hypothesis() {
        let src = sig("src", vec![], Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));
        let extra_hyp = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let tgt = sig(
            "tgt",
            vec![extra_hyp.clone()],
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        );
        let result = adapt_proof(&src, &tgt);
        match result {
            TransferResult::NeedsAdaptation(adaptations) => {
                assert!(
                    adaptations.contains(&Adaptation::AddHypothesis { hypothesis: extra_hyp }),
                    "expected AddHypothesis, got {adaptations:?}"
                );
            }
            other => panic!("expected NeedsAdaptation, got {other:?}"),
        }
    }

    // --- 11. formula_similarity symmetric ---
    #[test]
    fn test_formula_similarity_symmetric() {
        let a = Formula::Implies(Box::new(var("x")), Box::new(Formula::Bool(true)));
        let b = Formula::Implies(Box::new(var("y")), Box::new(Formula::Bool(false)));
        let ab = formula_similarity(&a, &b);
        let ba = formula_similarity(&b, &a);
        assert!((ab - ba).abs() < f64::EPSILON, "similarity not symmetric: {ab} vs {ba}");
    }

    // --- 12. hypothesis_overlap with identical sets ---
    #[test]
    fn test_hypothesis_overlap_identical() {
        let hyps = vec![var("x"), Formula::Bool(true)];
        let overlap = hypothesis_overlap(&hyps, &hyps);
        assert!((overlap - 1.0).abs() < f64::EPSILON, "expected 1.0, got {overlap}");
    }

    // --- 13. TransferCandidate PartialEq works ---
    #[test]
    fn test_transfer_candidate_partial_eq() {
        let s = sig("s", vec![], Formula::Bool(true));
        let c1 = TransferCandidate { source: s.clone(), score: 0.5, required_adaptations: vec![] };
        let c2 = TransferCandidate { source: s, score: 0.5, required_adaptations: vec![] };
        assert_eq!(c1, c2);
    }

    // --- 14. Adaptation enum variants constructible ---
    #[test]
    fn test_adaptation_variants() {
        let rename = Adaptation::Rename { from: "a".to_string(), to: "b".to_string() };
        let spec = Adaptation::Specialize { variable: "T".to_string(), term: Formula::Int(42) };
        let generalize =
            Adaptation::Generalize { term: Formula::Int(0), variable: "n".to_string() };
        let hyp = Adaptation::AddHypothesis { hypothesis: Formula::Bool(true) };
        // Verify Debug works (compile-time check, runtime smoke test)
        assert!(!format!("{rename:?}").is_empty());
        assert!(!format!("{spec:?}").is_empty());
        assert!(!format!("{generalize:?}").is_empty());
        assert!(!format!("{hyp:?}").is_empty());
    }

    // --- 15. find_transferable respects threshold ---
    #[test]
    fn test_find_transferable_below_threshold_excluded() {
        let target = sig("goal", vec![], Formula::Bool(true));
        // Bool(false) vs Bool(true) → score 0.0
        let unrelated = sig("unrelated", vec![var("a"), var("b"), var("c")], Formula::Int(999));
        let results = find_transferable(&[unrelated], &target);
        assert!(results.is_empty(), "below-threshold lemma should be excluded");
    }
}
