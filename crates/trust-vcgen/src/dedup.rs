// VC deduplication to avoid redundant solver calls.
//
// Many VCs for the same function or across functions may be structurally
// identical (up to variable renaming). This module provides:
// - Structural hashing of Formula and VerificationCondition
// - Alpha-equivalence normalization (rename bound variables canonically)
// - VcDeduplicator cache that uses fingerprints only as bucket selectors and
//   exact canonical VC identity before reusing prior solver results
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::{Hash, Hasher};

use trust_types::fx::FxHashMap;
use trust_types::{Formula, Sort, VerificationCondition, VerificationResult};

/// Compute a structural fingerprint of a `Formula`.
///
/// Performs alpha-equivalence normalization before hashing: quantifier-bound
/// variables are renamed to canonical de Bruijn-style names (`__alpha_0`,
/// `__alpha_1`, ...) so that structurally identical formulas that differ only
/// in bound variable names produce the same fingerprint.
///
/// Free variables are hashed by their original names since they represent
/// semantically distinct program values.
#[must_use]
pub fn formula_fingerprint(f: &Formula) -> u64 {
    // Normalize bound variables for alpha-equivalence, then hash.
    let normalized = normalize_alpha(f);
    let mut hasher = std::hash::DefaultHasher::new();
    normalized.hash(&mut hasher);
    hasher.finish()
}

/// Compute a structural fingerprint of a `VerificationCondition`.
///
/// Combines the VcKind description (which encodes the kind, operation, and
/// types) with the formula fingerprint. Two VCs with the same kind and
/// structurally equivalent formulas will have the same fingerprint.
#[must_use]
pub fn vc_fingerprint(vc: &VerificationCondition) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    // Hash the kind description as a stable string representation.
    vc.kind.description().hash(&mut hasher);
    // Hash the formula structurally (with alpha-normalization).
    let normalized = normalize_alpha(&vc.formula);
    normalized.hash(&mut hasher);
    hasher.finish()
}

/// Cache for deduplicating VCs across solver calls.
///
/// Maps structural fingerprints to buckets, then requires exact canonical VC
/// equality so that a collision or source/contract change cannot inherit proof
/// evidence from another public row.
#[derive(Debug, Default)]
pub struct VcDeduplicator {
    // The fixed-width fingerprint is only a bucket selector. Exact canonical
    // payload equality is mandatory before a solver result can be reused.
    cache: FxHashMap<u64, Vec<CachedVcResult>>,
    entries: usize,
}

#[derive(Debug)]
struct CachedVcResult {
    canonical_payload: String,
    result: VerificationResult,
}

impl VcDeduplicator {
    /// Create a new empty deduplicator.
    #[must_use]
    pub fn new() -> Self {
        Self { cache: FxHashMap::default(), entries: 0 }
    }

    /// Look up a cached result for a VC.
    ///
    /// Returns `Some(&VerificationResult)` if an exactly identical,
    /// alpha-normalized VC was previously recorded, `None` otherwise.
    #[must_use]
    pub fn check(&self, vc: &VerificationCondition) -> Option<&VerificationResult> {
        let fp = vc_fingerprint(vc);
        let canonical_payload = canonical_vc_payload(vc)?;
        self.cache
            .get(&fp)?
            .iter()
            .find(|entry| entry.canonical_payload == canonical_payload)
            .map(|entry| &entry.result)
    }

    /// Record a solver result for a VC.
    ///
    /// Future calls to `check` with the same exact canonical VC will return a
    /// reference to this result.
    pub fn record(&mut self, vc: &VerificationCondition, result: VerificationResult) {
        let fp = vc_fingerprint(vc);
        let Some(canonical_payload) = canonical_vc_payload(vc) else {
            // Serialization failure means exact equality is unavailable. Never
            // cache under a lossy fallback that could transfer proof evidence.
            return;
        };
        let bucket = self.cache.entry(fp).or_default();
        if let Some(entry) =
            bucket.iter_mut().find(|entry| entry.canonical_payload == canonical_payload)
        {
            entry.result = result;
        } else {
            bucket.push(CachedVcResult { canonical_payload, result });
            self.entries = self.entries.saturating_add(1);
        }
    }

    /// Number of cached entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries == 0
    }

    /// Clear all cached entries.
    pub fn clear(&mut self) {
        self.cache.clear();
        self.entries = 0;
    }
}

/// Exact, alpha-normalized VC identity for result reuse. Source and contract
/// metadata remain in the payload because `VerificationResult` may carry
/// evidence bound to those fields; semantic formula equality alone is not
/// sufficient authority to move that evidence to another public row.
fn canonical_vc_payload(vc: &VerificationCondition) -> Option<String> {
    let formula = normalize_alpha(&vc.formula);
    serde_json::to_string(&(&vc.kind, vc.function, &vc.location, formula, &vc.contract_metadata))
        .ok()
}

// ---------------------------------------------------------------------------
// Alpha-equivalence normalization
// ---------------------------------------------------------------------------

/// Normalize bound variables to canonical names for alpha-equivalence.
///
/// Quantifier-bound variables are renamed to `__alpha_0`, `__alpha_1`, etc.
/// in order of first binding encounter. Free variables are left unchanged.
#[must_use]
pub(crate) fn normalize_alpha(f: &Formula) -> Formula {
    let mut counter = 0usize;
    let mut env: FxHashMap<String, String> = FxHashMap::default();
    // Generated canonical binders must never capture a free program variable.
    // Identity mappings preserve free names and reserve them from generation.
    for name in f.free_variables() {
        env.insert(name.clone(), name);
    }
    normalize_inner(f, &mut env, &mut counter)
}

/// Recursive alpha-normalization with scoped environment.
fn normalize_inner(
    f: &Formula,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    match f {
        Formula::Var(name, sort) => {
            // Look up in environment for bound vars, else keep free name.
            let resolved = env.get(name).cloned().unwrap_or_else(|| name.clone());
            Formula::Var(resolved, sort.clone())
        }
        Formula::SymVar(name, sort) => {
            let name = name.as_str();
            let resolved = env.get(name).cloned().unwrap_or_else(|| name.to_string());
            // Var and SymVar are semantically identical representations. Use
            // one canonical spelling so representation choice cannot defeat
            // alpha-equivalent deduplication.
            Formula::Var(resolved, sort.clone())
        }
        Formula::Forall(bindings, body) => normalize_quantifier(bindings, body, true, env, counter),
        Formula::Exists(bindings, body) => {
            normalize_quantifier(bindings, body, false, env, counter)
        }
        // Formula owns an exhaustive child mapper. Using it here keeps
        // alpha-normalization wired for FP, predicate, datatype, and future
        // term families instead of silently cloning new variants unchanged.
        _ => f.clone().map_children(&mut |child| normalize_inner(&child, env, counter)),
    }
}

/// Normalize a quantifier node (Forall or Exists).
fn normalize_quantifier(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    is_forall: bool,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    // Save old bindings so we can restore after scope exit.
    let mut saved: Vec<(String, Option<String>)> = Vec::new();
    let mut new_bindings = Vec::new();

    for (name, sort) in bindings {
        let canonical = loop {
            let candidate = format!("__alpha_{counter}");
            *counter =
                counter.checked_add(1).expect("VC dedup alpha-normalization counter exhausted");
            if !env.contains_key(&candidate) {
                break candidate;
            }
        };
        let name_str = name.to_string();
        saved.push((name_str.clone(), env.get(&name_str).cloned()));
        env.insert(name_str, canonical.clone());
        new_bindings.push((trust_types::Symbol::intern(&canonical), sort.clone()));
    }

    let new_body = normalize_inner(body, env, counter);

    // Restore previous bindings (important for nested quantifiers).
    for (name, old_val) in saved.into_iter().rev() {
        match old_val {
            Some(v) => {
                env.insert(name, v);
            }
            None => {
                env.remove(&name);
            }
        }
    }

    if is_forall {
        Formula::Forall(new_bindings, Box::new(new_body))
    } else {
        Formula::Exists(new_bindings, Box::new(new_body))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationResult};

    use super::*;

    /// Helper: build a variable formula.
    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    /// Helper: build a basic VC with the given kind and formula.
    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Helper: build a Proved result.
    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    #[test]
    fn test_formula_fingerprint_identical_formulas_same_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_eq!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_different_formulas_different_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Sub(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_different_vars_different_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Add(Box::new(var("y")), Box::new(Formula::Int(1)));
        // Free variables have different names, so fingerprints differ.
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_alpha_equivalence_forall() {
        // forall x: Int. x > 0  vs  forall y: Int. y > 0
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "alpha-equivalent formulas must have the same fingerprint"
        );
    }

    #[test]
    fn test_formula_fingerprint_alpha_equivalence_exists() {
        // exists a: Int. a = 42  vs  exists b: Int. b = 42
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(42)))),
        );
        let f2 = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(42)))),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "alpha-equivalent exists formulas must have the same fingerprint"
        );
    }

    #[test]
    fn test_alpha_normalization_never_captures_free_canonical_name() {
        let has_free_canonical_name = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(var("__alpha_0")))),
        );
        let genuinely_reflexive = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(var("b")))),
        );

        assert_ne!(
            normalize_alpha(&has_free_canonical_name),
            normalize_alpha(&genuinely_reflexive)
        );
        assert_ne!(
            formula_fingerprint(&has_free_canonical_name),
            formula_fingerprint(&genuinely_reflexive)
        );

        let first = make_vc(VcKind::Postcondition, has_free_canonical_name);
        let second = make_vc(VcKind::Postcondition, genuinely_reflexive);
        let mut dedup = VcDeduplicator::new();
        dedup.record(&first, proved());
        assert!(
            dedup.check(&second).is_none(),
            "a free-variable obligation must not inherit a reflexive proof"
        );
    }

    #[test]
    fn test_formula_fingerprint_nested_quantifiers_alpha() {
        // forall x. exists y. x < y  vs  forall a. exists b. a < b
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Lt(Box::new(var("x")), Box::new(var("y")))),
            )),
        );
        let f2 = Formula::Forall(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Lt(Box::new(var("a")), Box::new(var("b")))),
            )),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "nested quantifiers with alpha-renamed bound vars must match"
        );
    }

    #[test]
    fn test_formula_fingerprint_leaf_types_distinguished() {
        // Bool(true) vs Int(1) -- different tags.
        let f1 = Formula::Bool(true);
        let f2 = Formula::Int(1);
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_vc_fingerprint_same_kind_same_formula() {
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
        );
        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
        );
        assert_eq!(vc_fingerprint(&vc1), vc_fingerprint(&vc2));
    }

    #[test]
    fn test_vc_fingerprint_different_kind_same_formula() {
        let formula = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));
        let vc1 = make_vc(VcKind::DivisionByZero, formula.clone());
        let vc2 = make_vc(VcKind::RemainderByZero, formula);
        assert_ne!(
            vc_fingerprint(&vc1),
            vc_fingerprint(&vc2),
            "different VcKind must produce different fingerprints"
        );
    }

    #[test]
    fn test_deduplicator_check_miss_returns_none() {
        let dedup = VcDeduplicator::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        assert!(dedup.check(&vc).is_none());
    }

    #[test]
    fn test_deduplicator_record_then_check_hit() {
        let mut dedup = VcDeduplicator::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        let result = proved();
        dedup.record(&vc, result);

        // Same VC should hit.
        let hit = dedup.check(&vc);
        assert!(hit.is_some());
        assert!(hit.unwrap().is_proved());
    }

    #[test]
    fn test_deduplicator_structurally_identical_vc_hits() {
        let mut dedup = VcDeduplicator::new();
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        dedup.record(&vc1, proved());

        // Build an identical VC separately.
        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        assert!(dedup.check(&vc2).is_some(), "structurally identical VC must hit cache");
    }

    #[test]
    fn test_deduplicator_different_formula_misses() {
        let mut dedup = VcDeduplicator::new();
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        dedup.record(&vc1, proved());

        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("c")), Box::new(Formula::Int(0))),
        );
        assert!(dedup.check(&vc2).is_none(), "different free var name must miss");
    }

    #[test]
    fn test_deduplicator_fingerprint_match_does_not_move_source_bound_evidence() {
        let mut dedup = VcDeduplicator::new();
        let vc1 = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        let mut vc2 = vc1.clone();
        vc2.function = "different_function".into();

        assert_eq!(vc_fingerprint(&vc1), vc_fingerprint(&vc2));
        dedup.record(&vc1, proved());
        assert!(
            dedup.check(&vc2).is_none(),
            "a fingerprint bucket match must not transfer source-bound proof evidence"
        );
    }

    #[test]
    fn test_deduplicator_alpha_equivalent_exact_vcs_hit() {
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
            ),
        );
        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Forall(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))),
            ),
        );
        let mut dedup = VcDeduplicator::new();
        dedup.record(&vc1, proved());
        assert!(dedup.check(&vc2).is_some());
    }

    #[test]
    fn test_deduplicator_len_and_clear() {
        let mut dedup = VcDeduplicator::new();
        assert_eq!(dedup.len(), 0);
        assert!(dedup.is_empty());

        dedup.record(&make_vc(VcKind::DivisionByZero, Formula::Bool(true)), proved());
        assert_eq!(dedup.len(), 1);
        assert!(!dedup.is_empty());

        dedup.clear();
        assert_eq!(dedup.len(), 0);
        assert!(dedup.is_empty());
    }

    #[test]
    fn test_normalize_alpha_free_vars_unchanged() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let normalized = normalize_alpha(&f);
        // Free vars should remain unchanged.
        assert_eq!(normalized, f);
    }

    #[test]
    fn test_normalize_alpha_bound_vars_renamed() {
        let f = Formula::Forall(
            vec![("my_var".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("my_var".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let normalized = normalize_alpha(&f);
        match &normalized {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings[0].0, "__alpha_0");
                match body.as_ref() {
                    Formula::Gt(lhs, _) => {
                        assert_eq!(**lhs, Formula::Var("__alpha_0".into(), Sort::Int));
                    }
                    other => panic!("expected Gt, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_normalize_alpha_preserves_sorts() {
        let bv_sort = Sort::BitVec(32);
        let f = Formula::Forall(
            vec![("v".into(), bv_sort.clone())],
            Box::new(Formula::Var("v".into(), bv_sort.clone())),
        );
        let normalized = normalize_alpha(&f);
        match &normalized {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings[0].1, bv_sort);
                match body.as_ref() {
                    Formula::Var(_, sort) => assert_eq!(*sort, bv_sort),
                    other => panic!("expected Var, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_normalize_alpha_reaches_new_term_families_and_symvars() {
        let pred = Formula::Pred(
            "p".into(),
            vec![Formula::FpIsNaN(Box::new(Formula::SymVar("v".into(), Sort::Int)))],
        );
        let formula = Formula::Forall(vec![("v".into(), Sort::Int)], Box::new(pred));
        let normalized = normalize_alpha(&formula);

        let Formula::Forall(_, body) = normalized else {
            panic!("expected normalized quantifier");
        };
        let Formula::Pred(_, args) = *body else {
            panic!("expected normalized predicate");
        };
        assert_eq!(
            args,
            vec![Formula::FpIsNaN(Box::new(Formula::Var("__alpha_0".into(), Sort::Int,)))],
        );
    }

    #[test]
    fn test_formula_fingerprint_bitvec_ops_distinguished() {
        let a = Formula::Var("a".into(), Sort::BitVec(32));
        let b = Formula::Var("b".into(), Sort::BitVec(32));
        let f_add = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 32);
        let f_sub = Formula::BvSub(Box::new(a), Box::new(b), 32);
        assert_ne!(
            formula_fingerprint(&f_add),
            formula_fingerprint(&f_sub),
            "BvAdd and BvSub must produce different fingerprints"
        );
    }

    #[test]
    fn test_formula_fingerprint_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        // Just check it does not panic and produces a deterministic value.
        let fp1 = formula_fingerprint(&f);
        let fp2 = formula_fingerprint(&f);
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn test_formula_fingerprint_array_ops() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let sel = Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0)));
        let sto =
            Formula::Store(Box::new(arr), Box::new(Formula::Int(0)), Box::new(Formula::Int(42)));
        assert_ne!(
            formula_fingerprint(&sel),
            formula_fingerprint(&sto),
            "Select and Store must produce different fingerprints"
        );
    }
}
