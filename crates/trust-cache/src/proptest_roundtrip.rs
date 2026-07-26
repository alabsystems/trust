// trust-cache/proptest_roundtrip.rs: Property-based idempotency and roundtrip tests
//
// Tests critical soundness properties of the cache:
// - Alpha-normalization idempotency: normalize(normalize(f)) == normalize(f)
// - Fingerprint determinism: hash(f) == hash(f.clone())
// - CacheEntry serialization roundtrip: deserialize(serialize(e)) == e
// - CachedResult serialization roundtrip: deserialize(serialize(r)) == r
//
// The arb_formula strategy is adapted from trust_vcgen/formula_proptest.rs
// (trust-cache does not depend on trust_vcgen).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use trust_types::{Formula, FunctionVerdict, Sort};

    use crate::CacheEntry;
    use crate::alpha_normalize::{SubFormulaCache, alpha_normalize, alpha_normalized_hash};
    use crate::result_cache::{CachedResult, ResultCacheKey};

    // -----------------------------------------------------------------------
    // Arbitrary Formula strategy (adapted from trust_vcgen/formula_proptest.rs)
    // -----------------------------------------------------------------------

    /// Generate an arbitrary Sort.
    fn arb_sort() -> impl Strategy<Value = Sort> {
        prop_oneof![Just(Sort::Bool), Just(Sort::Int),]
    }

    /// Generate a leaf-level Formula (depth 0).
    fn arb_formula_leaf() -> impl Strategy<Value = Formula> {
        prop_oneof![
            any::<bool>().prop_map(Formula::Bool),
            (-100i128..=100i128).prop_map(Formula::Int),
            (0u128..=100u128).prop_map(Formula::UInt),
            ("[a-e]", arb_sort()).prop_map(|(name, sort)| Formula::Var(name, sort)),
        ]
    }

    /// Generate a Formula with bounded depth.
    fn arb_formula(max_depth: u32) -> BoxedStrategy<Formula> {
        if max_depth == 0 {
            return arb_formula_leaf().boxed();
        }

        let leaf = arb_formula_leaf();
        let child = arb_formula(max_depth - 1);

        prop_oneof![
            // Weight leaves higher to keep formulas manageable
            3 => leaf,
            // Unary
            1 => child.clone().prop_map(|f| Formula::Not(Box::new(f))),
            1 => child.clone().prop_map(|f| Formula::Neg(Box::new(f))),
            // Binary
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::And(vec![a, b])),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Or(vec![a, b])),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Implies(Box::new(a), Box::new(b))),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Eq(Box::new(a), Box::new(b))),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Lt(Box::new(a), Box::new(b))),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Add(Box::new(a), Box::new(b))),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Sub(Box::new(a), Box::new(b))),
            1 => (child.clone(), child.clone())
                .prop_map(|(a, b)| Formula::Mul(Box::new(a), Box::new(b))),
            // Quantifiers (essential for alpha-normalization testing)
            1 => (child.clone(), arb_sort())
                .prop_map(|(body, sort)| Formula::Exists(
                    vec![("q_var".into(), sort)],
                    Box::new(body),
                )),
            1 => (child.clone(), arb_sort())
                .prop_map(|(body, sort)| Formula::Forall(
                    vec![("q_var".into(), sort)],
                    Box::new(body),
                )),
            // Ite
            1 => (child.clone(), child.clone(), child.clone())
                .prop_map(|(a, b, c)| Formula::Ite(
                    Box::new(a), Box::new(b), Box::new(c),
                )),
        ]
        .boxed()
    }

    /// Default strategy: depth 3 for reasonable size and coverage.
    fn arb_formula_default() -> BoxedStrategy<Formula> {
        arb_formula(3)
    }

    // -----------------------------------------------------------------------
    // Arbitrary CacheEntry / CachedResult strategies
    // -----------------------------------------------------------------------

    fn arb_function_verdict() -> impl Strategy<Value = FunctionVerdict> {
        prop_oneof![
            Just(FunctionVerdict::Verified),
            Just(FunctionVerdict::HasViolations),
            Just(FunctionVerdict::Inconclusive),
        ]
    }

    fn arb_cache_entry() -> impl Strategy<Value = CacheEntry> {
        (
            "[a-f0-9]{64}", // content_hash (SHA-256 hex)
            arb_function_verdict(),
            0usize..100,      // total_obligations
            0usize..100,      // proved
            0usize..100,      // failed
            0usize..100,      // unknown
            0usize..100,      // runtime_checked
            0u64..=u64::MAX,  // cached_at
            "[a-f0-9]{0,64}", // spec_hash
            "[a-f0-9]{0,64}", // solver_fingerprint
        )
            .prop_map(
                |(
                    content_hash,
                    verdict,
                    total,
                    proved,
                    failed,
                    unknown,
                    runtime,
                    ts,
                    spec,
                    solver_fp,
                )| {
                    CacheEntry {
                        content_hash,
                        verdict,
                        total_obligations: total,
                        proved,
                        failed,
                        unknown,
                        runtime_checked: runtime,
                        cached_at: ts,
                        spec_hash: spec,
                        solver_fingerprint: solver_fp,
                        obligation_results: vec![],
                    }
                },
            )
    }

    fn arb_cached_result() -> impl Strategy<Value = CachedResult> {
        (
            "[a-f0-9]{16}",                           // formula_hash
            "[a-z]{2,8}",                             // solver_name
            "(proved|failed|unknown|timeout)",        // verdict
            proptest::option::of("[a-z0-9= ]{0,30}"), // model
            0u64..10_000,                             // time_ms
            0u64..=u64::MAX,                          // cached_at
        )
            .prop_map(|(fhash, solver, verdict, model, time_ms, cached_at)| CachedResult {
                key: ResultCacheKey { formula_hash: fhash, solver_name: solver },
                verdict,
                model,
                time_ms,
                cached_at,
                strength_json: None,
                proof_certificate: None,
            })
    }

    // -----------------------------------------------------------------------
    // Alpha-normalization idempotency
    // -----------------------------------------------------------------------

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// normalize(normalize(f)) == normalize(f)
        ///
        /// If this fails, cache lookups become non-deterministic: the same
        /// formula may or may not hit the cache depending on how many times
        /// it was normalized.
        #[test]
        fn test_alpha_normalize_idempotent(f in arb_formula_default()) {
            let once = alpha_normalize(&f);
            let twice = alpha_normalize(&once);
            prop_assert_eq!(
                twice,
                once,
                "alpha-normalization must be idempotent"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Fingerprint determinism
    // -----------------------------------------------------------------------

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// hash(f) == hash(f.clone())
        ///
        /// The alpha-normalized hash must be deterministic: cloning a formula
        /// and hashing the clone must produce the same result.
        #[test]
        fn test_fingerprint_deterministic(f in arb_formula_default()) {
            let h1 = alpha_normalized_hash(&f);
            let h2 = alpha_normalized_hash(&f.clone());
            prop_assert_eq!(
                h1,
                h2,
                "hash must be deterministic for cloned formulas"
            );
        }

        /// SubFormulaCache must agree with alpha_normalized_hash.
        ///
        /// The cached path and the non-cached path must produce identical
        /// hashes for the same formula.
        #[test]
        fn test_subformula_cache_agrees_with_standalone(f in arb_formula_default()) {
            let standalone = alpha_normalized_hash(&f);
            let mut cache = SubFormulaCache::new();
            let cached = cache.hash_formula(&f);
            prop_assert_eq!(
                cached,
                standalone,
                "SubFormulaCache must agree with alpha_normalized_hash"
            );
        }
    }

    // -----------------------------------------------------------------------
    // CacheEntry serialization roundtrip
    // -----------------------------------------------------------------------

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// deserialize(serialize(cache_entry)) == cache_entry
        ///
        /// If this fails, the on-disk cache silently loses or corrupts fields
        /// (verdict, content_hash, obligation counts), returning stale or
        /// incorrect verdicts.
        #[test]
        fn test_cache_entry_serde_roundtrip(entry in arb_cache_entry()) {
            let json = serde_json::to_string(&entry)
                .expect("CacheEntry must serialize");
            let recovered: CacheEntry = serde_json::from_str(&json)
                .expect("CacheEntry must deserialize");
            prop_assert_eq!(
                recovered,
                entry,
                "CacheEntry serde roundtrip must be identity"
            );
        }

        /// CacheEntry roundtrip through pretty-printed JSON (how save() writes).
        #[test]
        fn test_cache_entry_serde_pretty_roundtrip(entry in arb_cache_entry()) {
            let json = serde_json::to_string_pretty(&entry)
                .expect("CacheEntry must serialize (pretty)");
            let recovered: CacheEntry = serde_json::from_str(&json)
                .expect("CacheEntry must deserialize (pretty)");
            prop_assert_eq!(
                recovered,
                entry,
                "CacheEntry pretty-JSON roundtrip must be identity"
            );
        }
    }

    // -----------------------------------------------------------------------
    // CachedResult serialization roundtrip
    // -----------------------------------------------------------------------

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// deserialize(serialize(cached_result)) == cached_result
        ///
        /// CachedResult is the solver result cache's on-disk format.
        /// If roundtrip fails, cached solver answers are silently corrupted.
        #[test]
        fn test_cached_result_serde_roundtrip(result in arb_cached_result()) {
            let json = serde_json::to_string(&result)
                .expect("CachedResult must serialize");
            let recovered: CachedResult = serde_json::from_str(&json)
                .expect("CachedResult must deserialize");
            prop_assert_eq!(
                recovered,
                result,
                "CachedResult serde roundtrip must be identity"
            );
        }

        /// CachedResult roundtrip with pretty JSON.
        #[test]
        fn test_cached_result_serde_pretty_roundtrip(result in arb_cached_result()) {
            let json = serde_json::to_string_pretty(&result)
                .expect("CachedResult must serialize (pretty)");
            let recovered: CachedResult = serde_json::from_str(&json)
                .expect("CachedResult must deserialize (pretty)");
            prop_assert_eq!(
                recovered,
                result,
                "CachedResult pretty-JSON roundtrip must be identity"
            );
        }
    }
}
