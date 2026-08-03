// trust-vcgen/shared_prefix.rs: Per-function shared assertion-prefix splitting
//
// The v2 VC pipeline conjoins a function's `global_facts` (and, per block, its
// versioned preconditions / path guards / semantic guards) into EVERY VC's
// formula before dispatch (see `generate.rs`, the `global_facts` clone loop and
// the precondition/guard passes below it). The result is that a function with M
// VCs over a shared prefix of N conjuncts ships `M * (N + obligation)` worth of
// assertions to the solver.
//
// This module provides a PURE, additive helper that recovers the prefix shared
// by every VC of a function so an incremental-session backend can assert it ONCE
// at the solver's base scope (turning `M * N` assert work into `M + N`) WITHOUT
// changing any verdict. It does NOT touch the existing pre-conjoined formulas —
// callers that do not opt into the split keep dispatching the full conjunction
// exactly as before.
//
// # Equivalence contract
//
// `split_shared_prefix(vcs)` returns `(prefix, bare_vcs)` such that, for each
// input VC `v`:
//
//   And(prefix ++ bare_vcs[i].formula_conjuncts)  ≡  v.formula
//
// as a logical formula. The proof is purely propositional: `prefix` is a subset
// of `v`'s own top-level conjuncts (it is the intersection across all VCs), and
// `bare_vcs[i].formula` is exactly `v`'s conjuncts with the prefix conjuncts
// removed. Re-conjoining the prefix with the remainder reconstructs the same
// SET of conjuncts as `v.formula`, and `And` is commutative, associative, and
// idempotent — so the conjunction VALUE (hence the solver's model set, hence the
// verdict) is identical regardless of conjunct order or multiplicity.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{Formula, VerificationCondition};

/// Flatten the top-level conjunction of a formula into its conjuncts.
///
/// `And([a, And([b, c]), d])` flattens to `[a, b, c, d]`. A non-`And` formula
/// `f` yields the singleton `[f]`. `And([])` (the trivial-true conjunction)
/// yields the empty vector. Flattening is sound because `And` is associative.
#[must_use]
pub fn flatten_conjuncts(formula: &Formula) -> Vec<Formula> {
    let mut out = Vec::new();
    push_conjuncts(formula, &mut out);
    out
}

fn push_conjuncts(formula: &Formula, out: &mut Vec<Formula>) {
    match formula {
        Formula::And(terms) => {
            for t in terms {
                push_conjuncts(t, out);
            }
        }
        other => out.push(other.clone()),
    }
}

/// Re-wrap a list of conjuncts into a single formula.
///
/// An empty list becomes `Bool(true)` (the identity of conjunction); a single
/// conjunct is returned bare (avoids a pointless `And` wrapper); otherwise an
/// `And`.
#[must_use]
pub fn conjoin(mut conjuncts: Vec<Formula>) -> Formula {
    match conjuncts.len() {
        0 => Formula::Bool(true),
        1 => conjuncts.pop().expect("len checked == 1"),
        _ => Formula::And(conjuncts),
    }
}

/// Compute the per-function shared assertion prefix and rewrite each VC to
/// carry only its bare (prefix-free) obligation.
///
/// Returns `(prefix, bare_vcs)`:
/// - `prefix` is the list of top-level conjuncts present (by structural
///   equality) in EVERY input VC, in the order they first appear in the first
///   VC. It is the common base scope a session backend asserts once.
/// - `bare_vcs` is the input VCs with `formula` replaced by the conjunction of
///   their remaining (non-prefix) conjuncts. Every other field is preserved.
///
/// # Equivalence
///
/// For each `i`, `And(prefix ++ bare_vcs[i].conjuncts) ≡ vcs[i].formula` (see
/// the module-level contract). Therefore deciding `prefix ∧ bare_vcs[i]` is
/// verdict-identical to deciding the original pre-conjoined `vcs[i].formula`.
///
/// When the VC list is empty, or the VCs share no common conjunct, `prefix` is
/// empty and `bare_vcs` carries each VC's original formula unchanged — so the
/// caller transparently falls back to the per-VC behavior.
#[must_use]
pub fn split_shared_prefix(
    vcs: &[VerificationCondition],
) -> (Vec<Formula>, Vec<VerificationCondition>) {
    if vcs.is_empty() {
        return (Vec::new(), Vec::new());
    }

    // Conjuncts of the first VC define the candidate prefix order. Use the first
    // VC's DISTINCT conjuncts as candidates; a conjunct is in the prefix iff it
    // appears in every VC.
    let first_conjuncts = flatten_conjuncts(&vcs[0].formula);

    // Build a per-VC presence set for membership tests. Hashing on the structural
    // `Formula` (which derives Eq + Hash) keeps the check O(total conjuncts).
    let presence: Vec<FxHashMap<&Formula, ()>> = vcs
        .iter()
        .map(|vc| match &vc.formula {
            Formula::And(terms) => flat_presence(terms),
            other => {
                let mut m = FxHashMap::default();
                m.insert(other, ());
                m
            }
        })
        .collect();

    // A candidate is shared iff present in EVERY VC. Preserve first-VC order and
    // de-duplicate (idempotent conjunction: one copy in the prefix suffices).
    let mut prefix: Vec<Formula> = Vec::new();
    let mut prefix_seen: FxHashMap<Formula, ()> = FxHashMap::default();
    for cand in &first_conjuncts {
        if prefix_seen.contains_key(cand) {
            continue;
        }
        if presence.iter().all(|p| p.contains_key(cand)) {
            prefix_seen.insert(cand.clone(), ());
            prefix.push(cand.clone());
        }
    }

    // Rewrite each VC to drop the prefix conjuncts. Dropping ALL occurrences is
    // sound: the prefix re-supplies one copy and `A ∧ A ≡ A`.
    let bare_vcs: Vec<VerificationCondition> = vcs
        .iter()
        .map(|vc| {
            let remaining: Vec<Formula> = flatten_conjuncts(&vc.formula)
                .into_iter()
                .filter(|c| !prefix_seen.contains_key(c))
                .collect();
            let mut bare = vc.clone();
            bare.formula = conjoin(remaining);
            bare
        })
        .collect();

    (prefix, bare_vcs)
}

/// Build a borrowed presence set from a flattened conjunct list. Nested `And`s
/// are flattened recursively so `And([a, And([b])])` registers both `a` and `b`.
fn flat_presence(terms: &[Formula]) -> FxHashMap<&Formula, ()> {
    let mut m = FxHashMap::default();
    register_presence(terms, &mut m);
    m
}

fn register_presence<'a>(terms: &'a [Formula], m: &mut FxHashMap<&'a Formula, ()>) {
    for t in terms {
        match t {
            Formula::And(inner) => register_presence(inner, m),
            other => {
                m.insert(other, ());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn le(a: Formula, b: Formula) -> Formula {
        Formula::Le(Box::new(a), Box::new(b))
    }

    fn vc(function: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: function.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// `And(prefix ++ bare) ≡ original` as a SET of conjuncts (the equivalence
    /// the solver sees). The trivial-true conjunct is the identity of `∧`
    /// (`A ∧ true ≡ A`), so it is normalized away — its presence or absence
    /// never changes the formula value or verdict.
    fn conjunct_set(f: &Formula) -> std::collections::BTreeSet<String> {
        flatten_conjuncts(f)
            .iter()
            .filter(|c| !matches!(c, Formula::Bool(true)))
            .map(|c| c.to_smtlib())
            .collect()
    }

    #[test]
    fn empty_input_yields_empty_prefix() {
        let (prefix, bare) = split_shared_prefix(&[]);
        assert!(prefix.is_empty());
        assert!(bare.is_empty());
    }

    #[test]
    fn flatten_handles_nested_and_and_singletons() {
        let nested = Formula::And(vec![var("a"), Formula::And(vec![var("b"), var("c")]), var("d")]);
        assert_eq!(flatten_conjuncts(&nested).len(), 4);
        // A bare (non-And) formula is its own single conjunct.
        assert_eq!(flatten_conjuncts(&var("x")).len(), 1);
        // Trivial-true And flattens to nothing.
        assert!(flatten_conjuncts(&Formula::And(vec![])).is_empty());
    }

    #[test]
    fn shared_prefix_is_common_conjuncts_and_split_is_equivalent() {
        // Two VCs over the same function sharing facts [a<=10, b<=10].
        let fact_a = le(var("a"), Formula::Int(10));
        let fact_b = le(var("b"), Formula::Int(10));
        let obl0 = le(var("a"), Formula::Int(5)); // bare obligation 0
        let obl1 = le(var("b"), Formula::Int(5)); // bare obligation 1

        let v0 = vc("f", Formula::And(vec![fact_a.clone(), fact_b.clone(), obl0.clone()]));
        let v1 = vc("f", Formula::And(vec![fact_a.clone(), fact_b.clone(), obl1.clone()]));

        let originals = [v0.clone(), v1.clone()];
        let (prefix, bare) = split_shared_prefix(&originals);

        // Prefix is exactly the two shared facts.
        assert_eq!(prefix.len(), 2);
        let prefix_set: std::collections::BTreeSet<String> =
            prefix.iter().map(|c| c.to_smtlib()).collect();
        assert!(prefix_set.contains(&fact_a.to_smtlib()));
        assert!(prefix_set.contains(&fact_b.to_smtlib()));

        // EQUIVALENCE: for each VC, prefix ∪ bare reconstructs the original
        // conjunct set exactly (the conjunction the solver decides).
        for (orig, bare_vc) in originals.iter().zip(bare.iter()) {
            let mut reassembled: Vec<Formula> = prefix.clone();
            reassembled.extend(flatten_conjuncts(&bare_vc.formula));
            let reassembled = conjoin(reassembled);
            assert_eq!(
                conjunct_set(&orig.formula),
                conjunct_set(&reassembled),
                "split must preserve the exact conjunct set"
            );
        }

        // The bare obligations dropped the shared facts.
        assert_eq!(conjunct_set(&bare[0].formula), conjunct_set(&obl0));
        assert_eq!(conjunct_set(&bare[1].formula), conjunct_set(&obl1));
    }

    #[test]
    fn no_common_conjunct_yields_empty_prefix_and_unchanged_formulas() {
        let v0 = vc("f", le(var("a"), Formula::Int(1)));
        let v1 = vc("f", le(var("b"), Formula::Int(2)));
        let (prefix, bare) = split_shared_prefix(&[v0.clone(), v1.clone()]);
        assert!(prefix.is_empty());
        assert_eq!(conjunct_set(&bare[0].formula), conjunct_set(&v0.formula));
        assert_eq!(conjunct_set(&bare[1].formula), conjunct_set(&v1.formula));
    }

    #[test]
    fn single_vc_prefix_is_its_own_conjuncts() {
        // With one VC, every conjunct is trivially "shared" — the whole formula
        // moves to the prefix and the bare obligation is trivial-true. The
        // reassembly is still exactly equivalent.
        let f = Formula::And(vec![le(var("a"), Formula::Int(10)), le(var("a"), Formula::Int(5))]);
        let v0 = vc("f", f.clone());
        let (prefix, bare) = split_shared_prefix(&[v0]);
        let mut reassembled = prefix.clone();
        reassembled.extend(flatten_conjuncts(&bare[0].formula));
        assert_eq!(conjunct_set(&conjoin(reassembled)), conjunct_set(&f));
    }
}
