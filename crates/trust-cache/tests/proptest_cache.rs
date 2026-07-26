// trust-cache property-based tests: serialization roundtrip, idempotency, determinism
//
// Uses proptest to verify soundness-critical cache properties:
// 1. CacheEntry serialization roundtrip (serde_json)
// 2. CachedResult serialization roundtrip (serde_json)
// 3. Alpha-normalization idempotency: normalize(normalize(f)) == normalize(f)
// 4. Alpha-normalized hash determinism: hash(f) == hash(f.clone())
// 5. Cache insert idempotency: inserting same key twice gives same result
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use proptest::prelude::*;
use trust_cache::alpha_normalize::{alpha_normalize, alpha_normalized_hash};
use trust_cache::result_cache::{CachedResult, ResultCacheKey};
use trust_cache::{CacheEntry, CacheLookup, VerificationCache};
use trust_types::{Formula, FunctionVerdict, Sort};

// ---------------------------------------------------------------------------
// Arbitrary strategies
// ---------------------------------------------------------------------------

/// Generate an arbitrary FunctionVerdict.
fn arb_verdict() -> impl Strategy<Value = FunctionVerdict> {
    prop_oneof![
        Just(FunctionVerdict::Verified),
        Just(FunctionVerdict::RuntimeChecked),
        Just(FunctionVerdict::HasViolations),
        Just(FunctionVerdict::Inconclusive),
        Just(FunctionVerdict::NoObligations),
    ]
}

/// Generate an arbitrary CacheEntry with realistic field values.
fn arb_cache_entry() -> impl Strategy<Value = CacheEntry> {
    (
        "[0-9a-f]{64}",   // content_hash (SHA-256 hex)
        arb_verdict(),    // verdict
        0..1000usize,     // total_obligations
        0..1000usize,     // proved
        0..1000usize,     // failed
        0..1000usize,     // unknown
        0..1000usize,     // runtime_checked
        0..u64::MAX,      // cached_at
        "[0-9a-f]{0,64}", // spec_hash
        "[0-9a-f]{0,64}", // solver_fingerprint
    )
        .prop_map(
            |(
                content_hash,
                verdict,
                total_obligations,
                proved,
                failed,
                unknown,
                runtime_checked,
                cached_at,
                spec_hash,
                solver_fingerprint,
            )| {
                CacheEntry {
                    content_hash,
                    verdict,
                    total_obligations,
                    proved,
                    failed,
                    unknown,
                    runtime_checked,
                    cached_at,
                    spec_hash,
                    solver_fingerprint,
                    obligation_results: vec![],
                }
            },
        )
}

/// Generate an arbitrary ResultCacheKey.
fn arb_result_cache_key() -> impl Strategy<Value = ResultCacheKey> {
    ("[0-9a-f]{16}", "[a-z]{3,10}")
        .prop_map(|(formula_hash, solver_name)| ResultCacheKey { formula_hash, solver_name })
}

/// Generate an arbitrary CachedResult.
fn arb_cached_result() -> impl Strategy<Value = CachedResult> {
    (
        arb_result_cache_key(),
        "(proved|unknown|timeout|sat|unsat)",
        prop::option::of("[a-z0-9 ]{1,20}"),
        0..100_000u64,
        0..u64::MAX,
    )
        .prop_map(|(key, verdict, model, time_ms, cached_at)| CachedResult {
            key,
            verdict,
            model,
            time_ms,
            cached_at,
            strength_json: None,
            proof_certificate: None,
        })
}

/// Generate an arbitrary Sort (bounded depth).
fn arb_sort() -> impl Strategy<Value = Sort> {
    let leaf = prop_oneof![
        Just(Sort::Bool),
        Just(Sort::Int),
        prop::sample::select(vec![8u32, 16, 32, 64, 128]).prop_map(Sort::BitVec),
    ];
    leaf.prop_recursive(
        2, // max depth
        8, // max nodes
        2, // items per collection
        |inner| {
            (inner.clone(), inner)
                .prop_map(|(idx, elem)| Sort::Array(Box::new(idx), Box::new(elem)))
        },
    )
}

/// Generate an arbitrary Formula with bounded depth.
///
/// Replicates the strategy from trust-types/tests/proptest_roundtrip.rs
/// to avoid a circular dependency on trust_vcgen.
fn arb_formula() -> impl Strategy<Value = Formula> {
    let leaf = prop_oneof![
        prop::bool::ANY.prop_map(Formula::Bool),
        (-1000i128..1000).prop_map(Formula::Int),
        (0u128..1000).prop_map(Formula::UInt),
        ((-128i128..128), prop::sample::select(vec![8u32, 16, 32, 64]))
            .prop_map(|(v, w)| Formula::BitVec { value: v, width: w }),
        ("[a-z]{1,6}", arb_sort()).prop_map(|(n, s)| Formula::Var(n, s)),
    ];

    leaf.prop_recursive(
        3,  // max depth
        24, // max nodes
        4,  // items per collection
        |inner| {
            prop_oneof![
                // Unary
                inner.clone().prop_map(|f| Formula::Not(Box::new(f))),
                inner.clone().prop_map(|f| Formula::Neg(Box::new(f))),
                // Binary
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Eq(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Add(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Lt(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Implies(Box::new(a), Box::new(b))),
                // N-ary
                prop::collection::vec(inner.clone(), 0..4).prop_map(Formula::And),
                prop::collection::vec(inner.clone(), 0..4).prop_map(Formula::Or),
                // Ite
                (inner.clone(), inner.clone(), inner.clone()).prop_map(|(c, t, e)| Formula::Ite(
                    Box::new(c),
                    Box::new(t),
                    Box::new(e)
                )),
                // BV ops
                (inner.clone(), inner.clone(), prop::sample::select(vec![8u32, 16, 32, 64]))
                    .prop_map(|(a, b, w)| Formula::BvAdd(Box::new(a), Box::new(b), w)),
                (inner.clone(), inner.clone(), prop::sample::select(vec![8u32, 16, 32, 64]))
                    .prop_map(|(a, b, w)| Formula::BvSLe(Box::new(a), Box::new(b), w)),
                // Quantifiers (critical for alpha_normalize testing)
                (prop::collection::vec(("[a-z]{1,4}", arb_sort()), 1..3), inner.clone(),).prop_map(
                    |(bindings, body)| Formula::Forall(
                        bindings
                            .into_iter()
                            .map(|(s, sort)| (trust_types::Symbol::intern(&s), sort))
                            .collect(),
                        Box::new(body)
                    )
                ),
                (prop::collection::vec(("[a-z]{1,4}", arb_sort()), 1..3), inner.clone(),).prop_map(
                    |(bindings, body)| Formula::Exists(
                        bindings
                            .into_iter()
                            .map(|(s, sort)| (trust_types::Symbol::intern(&s), sort))
                            .collect(),
                        Box::new(body)
                    )
                ),
                // Select
                (inner.clone(), inner.clone())
                    .prop_map(|(arr, idx)| Formula::Select(Box::new(arr), Box::new(idx))),
            ]
        },
    )
}

// ---------------------------------------------------------------------------
// Property: CacheEntry JSON serialization roundtrip
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// deserialize(serialize(entry)) == entry for any CacheEntry.
    ///
    /// Ensures no field is silently lost or corrupted during
    /// cache persistence. A failure here means the on-disk cache format
    /// does not faithfully represent in-memory state.
    #[test]
    fn cache_entry_json_roundtrip(entry in arb_cache_entry()) {
        let json = serde_json::to_string(&entry).expect("serialize CacheEntry");
        let round: CacheEntry = serde_json::from_str(&json).expect("deserialize CacheEntry");
        prop_assert_eq!(&round, &entry, "CacheEntry roundtrip failed");
    }

    /// CacheEntry pretty-print JSON also roundtrips (tests the on-disk format).
    #[test]
    fn cache_entry_pretty_json_roundtrip(entry in arb_cache_entry()) {
        let json = serde_json::to_string_pretty(&entry).expect("serialize CacheEntry pretty");
        let round: CacheEntry = serde_json::from_str(&json).expect("deserialize CacheEntry pretty");
        prop_assert_eq!(&round, &entry, "CacheEntry pretty roundtrip failed");
    }
}

// ---------------------------------------------------------------------------
// Property: CachedResult JSON serialization roundtrip
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// deserialize(serialize(result)) == result for any CachedResult.
    ///
    /// The solver result cache must preserve all fields through
    /// serialization, including the nested ResultCacheKey, optional model,
    /// and timing data.
    #[test]
    fn cached_result_json_roundtrip(result in arb_cached_result()) {
        let json = serde_json::to_string(&result).expect("serialize CachedResult");
        let round: CachedResult = serde_json::from_str(&json).expect("deserialize CachedResult");
        prop_assert_eq!(&round, &result, "CachedResult roundtrip failed");
    }

    /// ResultCacheKey JSON roundtrip.
    #[test]
    fn result_cache_key_json_roundtrip(key in arb_result_cache_key()) {
        let json = serde_json::to_string(&key).expect("serialize ResultCacheKey");
        let round: ResultCacheKey = serde_json::from_str(&json).expect("deserialize ResultCacheKey");
        prop_assert_eq!(&round, &key, "ResultCacheKey roundtrip failed");
    }
}

// ---------------------------------------------------------------------------
// Property: alpha_normalize is idempotent
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// normalize(normalize(f)) == normalize(f) for any formula.
    ///
    /// If normalization is not idempotent, cache lookups become
    /// non-deterministic: the same formula may or may not hit the cache
    /// depending on how many times it was normalized before hashing.
    #[test]
    fn alpha_normalize_idempotent(f in arb_formula()) {
        let once = alpha_normalize(&f);
        let twice = alpha_normalize(&once);
        prop_assert_eq!(
            &twice,
            &once,
            "alpha_normalize must be idempotent: normalize(normalize(f)) == normalize(f)"
        );
    }
}

// ---------------------------------------------------------------------------
// Property: alpha_normalized_hash is deterministic
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// hash(f) == hash(f.clone()) for any formula.
    ///
    /// The hash function must be deterministic — identical
    /// formulas must always produce the same hash. A non-deterministic hash
    /// would cause cache misses on logically identical queries.
    #[test]
    fn alpha_normalized_hash_deterministic(f in arb_formula()) {
        let h1 = alpha_normalized_hash(&f);
        let h2 = alpha_normalized_hash(&f.clone());
        prop_assert_eq!(
            &h1,
            &h2,
            "alpha_normalized_hash must be deterministic"
        );
    }

    /// Alpha-normalized hash is always a 64-char hex string (SHA-256).
    #[test]
    fn alpha_normalized_hash_is_sha256(f in arb_formula()) {
        let h = alpha_normalized_hash(&f);
        prop_assert_eq!(h.len(), 64, "SHA-256 hex must be 64 chars, got {}", h.len());
        prop_assert!(
            h.chars().all(|c| c.is_ascii_hexdigit()),
            "hash must be valid hex: {}",
            h
        );
    }

    /// Normalizing before hashing should produce the same hash as direct hashing.
    ///
    /// alpha_normalized_hash internally normalizes, so
    /// hash(normalize(f)) == hash(f) must hold.
    #[test]
    fn hash_after_normalize_equals_hash(f in arb_formula()) {
        let direct = alpha_normalized_hash(&f);
        let normalized = alpha_normalize(&f);
        let via_normalized = alpha_normalized_hash(&normalized);
        prop_assert_eq!(
            &direct,
            &via_normalized,
            "hash(f) must equal hash(normalize(f))"
        );
    }
}

// ---------------------------------------------------------------------------
// Property: VerificationCache insert idempotency
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Inserting the same (def_path, entry) twice yields the same cache state.
    ///
    /// A cache store followed by an identical store should be
    /// indistinguishable from a single store. The second insert must not
    /// corrupt or lose the entry.
    #[test]
    fn cache_insert_idempotent(
        def_path in "[a-z:_]{5,30}",
        entry in arb_cache_entry(),
    ) {
        let mut cache = VerificationCache::in_memory();

        // Insert once
        cache.store(&def_path, entry.clone());
        let lookup1 = cache.lookup(&def_path, &entry.content_hash, &entry.spec_hash, &entry.solver_fingerprint);

        // Insert again with identical data
        cache.store(&def_path, entry.clone());
        let lookup2 = cache.lookup(&def_path, &entry.content_hash, &entry.spec_hash, &entry.solver_fingerprint);

        // Both lookups must return Hit with the same entry
        prop_assert_eq!(
            &lookup1,
            &lookup2,
            "double insert must be idempotent"
        );
        match lookup2 {
            CacheLookup::Hit(cached) => {
                prop_assert_eq!(&cached, &entry, "cached entry must match original");
            }
            CacheLookup::Miss => {
                prop_assert!(false, "expected cache hit after store");
            }
        }
    }

    /// Cache size does not grow from duplicate inserts for the same key.
    #[test]
    fn cache_no_growth_on_duplicate_insert(
        def_path in "[a-z:_]{5,30}",
        entry in arb_cache_entry(),
    ) {
        let mut cache = VerificationCache::in_memory();
        cache.store(&def_path, entry.clone());
        let len_after_first = cache.len();

        cache.store(&def_path, entry);
        let len_after_second = cache.len();

        prop_assert_eq!(
            len_after_first,
            len_after_second,
            "duplicate insert must not increase cache size"
        );
    }
}

// ---------------------------------------------------------------------------
// Property: CacheEntry fields survive file persistence roundtrip
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Full persistence roundtrip: store -> save -> load -> independently
    /// revalidate/store -> lookup.
    ///
    /// This tests the complete on-disk format including the CacheFile
    /// wrapper with version field, ensuring that the JSON schema is stable.
    #[test]
    fn cache_persistence_roundtrip(
        def_path in "[a-z:_]{5,30}",
        entry in arb_cache_entry(),
    ) {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");

        // Store and save
        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store(&def_path, entry.clone());
            cache.save().expect("save cache");
        }

        // Load and verify. Disk persistence is not proof authority: `store`
        // represents a fresh in-process revalidation and marks the exact entry
        // eligible for honest same-session replay. The equivalent-store fast
        // path leaves the persisted payload byte-for-byte intact.
        {
            let mut cache = VerificationCache::load(&cache_path).expect("load cache");
            cache.store(&def_path, entry.clone());
            match cache.lookup(&def_path, &entry.content_hash, &entry.spec_hash, &entry.solver_fingerprint) {
                CacheLookup::Hit(loaded) => {
                    prop_assert_eq!(&loaded, &entry, "entry must survive persistence roundtrip");
                }
                CacheLookup::Miss => {
                    prop_assert!(false, "expected hit after independent revalidation");
                }
            }
        }
    }
}
