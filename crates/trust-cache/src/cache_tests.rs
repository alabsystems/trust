//! Tests for [`crate::cache::VerificationCache`].
//!
//! Extracted from `cache.rs` to keep that file under the 500 LOC budget.
//! Included as `#[cfg(test)] mod tests` via `#[path]`.

use trust_types::{
    BasicBlock, BlockId, Contract, ContractKind, FunctionVerdict, Outcome, SourceSpan, Terminator,
    TransportMonitorEvidence, TransportMonitorStatus, TransportObligationResult, Ty, VcKind,
    VerifiableBody, VerifiableFunction,
};

use super::{CacheError, VerificationCache};
use crate::coordination::CoordinationConfig;
use crate::entry::{CACHE_VERSION, CacheEntry, CacheLookup};
use crate::fingerprint::{
    compute_content_hash, compute_solver_fingerprint, fingerprint_solver_binary,
    snapshot_solver_binary,
};

fn sample_entry(hash: &str, verdict: FunctionVerdict) -> CacheEntry {
    CacheEntry {
        content_hash: hash.to_string(),
        verdict,
        total_obligations: 3,
        proved: 2,
        failed: 0,
        unknown: 1,
        runtime_checked: 0,
        cached_at: 0,
        spec_hash: String::new(),
        solver_fingerprint: String::new(),
        obligation_results: vec![],
    }
}

fn sample_non_proof_entry(hash: &str, verdict: FunctionVerdict) -> CacheEntry {
    let mut entry = sample_entry(hash, verdict);
    entry.proved = 0;
    entry.unknown = entry.total_obligations;
    entry
}

fn sample_non_proof_transport_result() -> TransportObligationResult {
    TransportObligationResult {
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "divzero".to_string(),
        typed_kind: Some(Box::new(VcKind::DivisionByZero)),
        description: "division by zero".to_string(),
        location: None,
        outcome: Outcome::Unknown,
        solver: "constant-folder".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some("not proved".to_string()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
    }
}

fn make_function(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![],
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

fn make_function_with_contract(name: &str, contract_desc: &str) -> VerifiableFunction {
    let mut func = make_function(name);
    func.contracts.push(Contract {
        kind: ContractKind::Ensures,
        span: SourceSpan::default(),
        body: contract_desc.to_string(),
    });
    func
}

// -----------------------------------------------------------------------
// SHA-256 content hashing tests
// -----------------------------------------------------------------------

#[test]
fn test_content_hash_deterministic() {
    let func = make_function("foo");
    let h1 = compute_content_hash(&func);
    let h2 = compute_content_hash(&func);
    assert_eq!(h1, h2, "content hash must be deterministic");
}

#[test]
fn test_content_hash_is_sha256_hex() {
    let func = make_function("foo");
    let hash = compute_content_hash(&func);
    // SHA-256 hex is 64 characters
    assert_eq!(hash.len(), 64, "SHA-256 hex digest is 64 chars, got {}", hash.len());
    assert!(hash.chars().all(|c| c.is_ascii_hexdigit()), "must be valid hex");
}

#[test]
fn test_content_hash_ignores_name() {
    let f1 = make_function("foo");
    let f2 = make_function("bar");
    assert_eq!(
        compute_content_hash(&f1),
        compute_content_hash(&f2),
        "content hash depends on body+contracts, not name — cache keys by def_path separately"
    );
}

#[test]
fn test_content_hash_changes_with_contracts() {
    let f1 = make_function("foo");
    let f2 = make_function_with_contract("foo", "result > 0");
    assert_ne!(
        compute_content_hash(&f1),
        compute_content_hash(&f2),
        "adding a contract must change the hash"
    );
}

#[test]
fn test_content_hash_changes_with_body() {
    let f1 = make_function("foo");
    let mut f2 = make_function("foo");
    f2.body.arg_count = 3;
    assert_ne!(
        compute_content_hash(&f1),
        compute_content_hash(&f2),
        "changing body must change the hash"
    );
}

// -----------------------------------------------------------------------
// Cache hit/miss tests
// -----------------------------------------------------------------------

#[test]
fn test_cache_hit_and_miss() {
    let mut cache = VerificationCache::in_memory();
    cache.store("mymod::foo", sample_entry("abc123", FunctionVerdict::Verified));

    assert_eq!(
        cache.lookup("mymod::foo", "abc123", "", ""),
        CacheLookup::Hit(sample_entry("abc123", FunctionVerdict::Verified))
    );
    assert_eq!(cache.lookup("mymod::foo", "different_hash", "", ""), CacheLookup::Miss);
    assert_eq!(cache.lookup("mymod::bar", "abc123", "", ""), CacheLookup::Miss);

    assert_eq!(cache.hits(), 1);
    assert_eq!(cache.misses(), 2);
}

#[test]
fn test_cache_invalidate() {
    let mut cache = VerificationCache::in_memory();
    cache.store("mymod::foo", sample_entry("abc123", FunctionVerdict::Verified));
    assert!(cache.invalidate("mymod::foo"));
    assert!(!cache.invalidate("mymod::foo")); // already removed
    assert_eq!(cache.lookup("mymod::foo", "abc123", "", ""), CacheLookup::Miss);
}

#[test]
fn test_cache_invalidate_all() {
    let mut cache = VerificationCache::in_memory();
    cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
    cache.store("b::g", sample_entry("h2", FunctionVerdict::HasViolations));
    cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));
    assert_eq!(cache.len(), 3);

    cache.invalidate_all();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_cache_retain_only() {
    let mut cache = VerificationCache::in_memory();
    cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
    cache.store("b::g", sample_entry("h2", FunctionVerdict::HasViolations));
    cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));

    cache.retain_only(&["a::f", "c::h"]);
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.lookup("b::g", "h2", "", ""), CacheLookup::Miss);
}

#[test]
fn test_cache_overwrite() {
    let mut cache = VerificationCache::in_memory();
    cache.store("m::f", sample_entry("old", FunctionVerdict::Inconclusive));
    cache.store("m::f", sample_entry("new", FunctionVerdict::Verified));

    assert_eq!(
        cache.lookup("m::f", "new", "", ""),
        CacheLookup::Hit(sample_entry("new", FunctionVerdict::Verified))
    );
    assert_eq!(cache.lookup("m::f", "old", "", ""), CacheLookup::Miss);
}

#[test]
fn test_cache_dirty_tracks_only_real_changes() {
    let mut cache = VerificationCache::in_memory();
    assert!(!cache.is_dirty(), "new in-memory cache starts clean");

    let entry = sample_entry("hash", FunctionVerdict::Verified);
    assert!(cache.store("m::f", entry.clone()));
    assert!(cache.is_dirty(), "new entry marks cache dirty");

    cache.save().expect("in-memory save should clear dirty state");
    assert!(!cache.is_dirty(), "successful save clears dirty state");

    assert!(!cache.store("m::f", entry), "storing an equivalent entry should be a no-op");
    assert!(!cache.is_dirty(), "equivalent store should leave clean cache clean");

    assert!(!cache.invalidate("missing::f"));
    assert!(!cache.is_dirty(), "missing invalidation should not dirty cache");

    assert!(cache.invalidate("m::f"));
    assert!(cache.is_dirty(), "real invalidation marks cache dirty");

    cache.save().expect("in-memory save should clear dirty state again");
    assert!(!cache.is_dirty());

    cache.invalidate_all();
    assert!(!cache.is_dirty(), "invalidating an empty cache is a no-op");
}

#[test]
fn test_cache_dirty_tracks_retain_only_changes() {
    let mut cache = VerificationCache::in_memory();
    cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
    cache.store("b::g", sample_entry("h2", FunctionVerdict::HasViolations));
    cache.save().expect("in-memory save should clear dirty state");
    assert!(!cache.is_dirty());

    cache.retain_only(&["a::f", "b::g"]);
    assert!(!cache.is_dirty(), "retaining all entries should be a no-op");

    cache.retain_only(&["a::f"]);
    assert!(cache.is_dirty(), "dropping an entry via retain_only marks dirty");
    assert_eq!(cache.len(), 1);
}

// -----------------------------------------------------------------------
// VerifiableFunction convenience methods
// -----------------------------------------------------------------------

#[test]
fn test_lookup_function_hit() {
    let func = make_function("foo");
    let mut cache = VerificationCache::in_memory();
    // Use store_function to ensure spec_hash matches lookup_function's computation.
    cache.store_function(&func, FunctionVerdict::Verified, 2, 2, 0, 0, 0, "");

    let result = cache.lookup_function(&func, "");
    assert!(matches!(result, CacheLookup::Hit(_)));
    assert_eq!(cache.hits(), 1);
}

#[test]
fn test_lookup_function_miss_on_change() {
    let func = make_function("foo");
    let mut cache = VerificationCache::in_memory();
    // Store with old hash
    cache.store(&func.def_path, sample_entry("stale_hash", FunctionVerdict::Verified));

    // Lookup with current function (different hash)
    let result = cache.lookup_function(&func, "");
    assert_eq!(result, CacheLookup::Miss);
    assert_eq!(cache.misses(), 1);
}

#[test]
fn test_store_function_roundtrip() {
    let func = make_function("bar");
    let mut cache = VerificationCache::in_memory();
    cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0, "");

    let result = cache.lookup_function(&func, "");
    match result {
        CacheLookup::Hit(entry) => {
            assert_eq!(entry.verdict, FunctionVerdict::Verified);
            assert_eq!(entry.total_obligations, 5);
            assert_eq!(entry.proved, 4);
            assert_eq!(entry.unknown, 1);
            assert!(entry.cached_at > 0, "timestamp should be set");
        }
        CacheLookup::Miss => panic!("expected cache hit after store_function"),
    }
}

#[test]
fn test_store_function_with_obligation_results_roundtrip() {
    let func = make_function("bar");
    let mut cache = VerificationCache::in_memory();
    let transport = vec![TransportObligationResult {
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "divzero".to_string(),
        typed_kind: Some(Box::new(VcKind::DivisionByZero)),
        description: "division by zero".to_string(),
        location: None,
        outcome: Outcome::Unknown,
        solver: "constant-folder".to_string(),
        time_ms: 7,
        counterexample: None,
        counterexample_model: None,
        reason: Some("no solver".to_string()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
    }];

    cache.store_function_with_obligation_results(
        &func,
        FunctionVerdict::Inconclusive,
        1,
        0,
        0,
        1,
        0,
        "",
        transport.clone(),
    );

    match cache.lookup_function(&func, "") {
        CacheLookup::Hit(entry) => {
            assert_eq!(entry.total_obligations, 1);
            assert_eq!(entry.obligation_results, transport);
        }
        CacheLookup::Miss => panic!("expected cache hit after store_function"),
    }
}

#[test]
fn test_store_function_is_noop_when_entry_is_unchanged() {
    let func = make_function("bar");
    let mut cache = VerificationCache::in_memory();

    assert!(cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0, ""));

    let cached_at = match cache.lookup_function(&func, "") {
        CacheLookup::Hit(entry) => entry.cached_at,
        CacheLookup::Miss => panic!("expected cache hit after initial store_function"),
    };

    assert!(
        !cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0, ""),
        "identical store_function call should be a no-op"
    );

    match cache.lookup_function(&func, "") {
        CacheLookup::Hit(entry) => {
            assert_eq!(entry.cached_at, cached_at, "no-op store should preserve timestamp");
        }
        CacheLookup::Miss => panic!("expected cache hit after no-op store_function"),
    }
}

#[test]
fn test_store_function_detects_body_change() {
    let func_v1 = make_function("baz");
    let mut cache = VerificationCache::in_memory();
    cache.store_function(&func_v1, FunctionVerdict::Verified, 1, 1, 0, 0, 0, "");

    // Modify the function body
    let mut func_v2 = make_function("baz");
    func_v2.body.arg_count = 2;

    // Lookup with modified function should miss
    let result = cache.lookup_function(&func_v2, "");
    assert_eq!(result, CacheLookup::Miss);
}

// -----------------------------------------------------------------------
// Persistence tests
// -----------------------------------------------------------------------

#[test]
fn test_cache_persistence_roundtrip() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");

    // Write
    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", sample_entry("hash1", FunctionVerdict::Verified));
        cache.store("m::g", sample_non_proof_entry("hash2", FunctionVerdict::HasViolations));
        cache.save().expect("save cache");
    }

    // Read back
    {
        let mut cache = VerificationCache::load(&cache_path).expect("load cache");
        assert_eq!(cache.len(), 2);
        assert_eq!(
            cache.lookup("m::f", "hash1", "", ""),
            CacheLookup::Miss,
            "proof-bearing disk records are not replay authority"
        );
        assert_eq!(
            cache.lookup("m::g", "hash2", "", ""),
            CacheLookup::Hit(sample_non_proof_entry("hash2", FunctionVerdict::HasViolations,))
        );
    }
}

#[cfg(unix)]
#[test]
fn direct_save_replaces_a_cache_symlink_without_truncating_its_target() {
    use std::os::unix::fs::symlink;

    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let victim_path = dir.path().join("victim.txt");
    std::fs::write(&victim_path, "unrelated sensitive data").expect("seed victim");
    symlink(&victim_path, &cache_path).expect("plant cache symlink");

    let mut cache = VerificationCache::load(&cache_path).expect("load through planted symlink");
    cache.store("m::f", sample_non_proof_entry("hash", FunctionVerdict::Inconclusive));
    cache.save().expect("secure atomic save");

    assert_eq!(
        std::fs::read_to_string(&victim_path).unwrap(),
        "unrelated sensitive data",
        "save must never open the symlink target for writing"
    );
    assert!(
        !std::fs::symlink_metadata(&cache_path).unwrap().file_type().is_symlink(),
        "the cache symlink directory entry must be atomically replaced"
    );
    assert!(
        serde_json::from_str::<serde_json::Value>(
            &std::fs::read_to_string(&cache_path).expect("read published cache")
        )
        .is_ok(),
        "the replacement cache must be complete JSON"
    );
}

#[cfg(unix)]
#[test]
fn coordinated_save_ignores_a_planted_legacy_temp_symlink() {
    use std::os::unix::fs::symlink;

    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let legacy_temp_path = cache_path.with_extension("tmp");
    let victim_path = dir.path().join("victim.txt");
    std::fs::write(&victim_path, "unrelated sensitive data").expect("seed victim");
    symlink(&victim_path, &legacy_temp_path).expect("plant legacy temp symlink");

    let config = CoordinationConfig::default();
    let mut cache =
        VerificationCache::load_coordinated(&cache_path, &config).expect("create cache");
    cache.store("m::f", sample_non_proof_entry("hash", FunctionVerdict::Inconclusive));
    cache.save_coordinated(&config).expect("secure coordinated save");

    assert_eq!(
        std::fs::read_to_string(&victim_path).unwrap(),
        "unrelated sensitive data",
        "coordinated save must not follow the predictable legacy temp symlink"
    );
    assert!(
        std::fs::symlink_metadata(&legacy_temp_path).unwrap().file_type().is_symlink(),
        "the obsolete predictable temp pathname must remain untouched"
    );
}

#[test]
fn test_loaded_cache_starts_clean_and_equivalent_store_stays_clean() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let entry = sample_entry("hash1", FunctionVerdict::Verified);

    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", entry.clone());
        cache.save().expect("save cache");
        assert!(!cache.is_dirty());
    }

    {
        let mut cache = VerificationCache::load(&cache_path).expect("load cache");
        assert!(!cache.is_dirty(), "loaded cache should start clean");
        assert!(!cache.store("m::f", entry), "equivalent store after load is clean");
        assert!(!cache.is_dirty());
    }
}

#[test]
fn test_coordinated_save_merges_concurrent_entries() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let config = CoordinationConfig::default();

    let mut writer_a =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer a");
    let mut writer_b =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer b");

    writer_a.store("a::f", sample_non_proof_entry("ha", FunctionVerdict::Inconclusive));
    writer_b.store("b::g", sample_non_proof_entry("hb", FunctionVerdict::HasViolations));

    writer_a.save_coordinated(&config).expect("save writer a");
    writer_b.save_coordinated(&config).expect("save writer b");
    assert!(!writer_a.is_dirty());
    assert!(!writer_b.is_dirty());

    let mut merged =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load merged cache");
    assert_eq!(merged.len(), 2);
    assert_eq!(
        merged.lookup("a::f", "ha", "", ""),
        CacheLookup::Hit(sample_non_proof_entry("ha", FunctionVerdict::Inconclusive))
    );
    assert_eq!(
        merged.lookup("b::g", "hb", "", ""),
        CacheLookup::Hit(sample_non_proof_entry("hb", FunctionVerdict::HasViolations))
    );
}

#[test]
fn test_coordinated_save_removal_does_not_reintroduce_deleted_entry() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let config = CoordinationConfig::default();

    {
        let mut cache =
            VerificationCache::load_coordinated(&cache_path, &config).expect("create cache");
        cache.store("base::f", sample_non_proof_entry("base", FunctionVerdict::Inconclusive));
        cache.save_coordinated(&config).expect("save base");
    }

    let mut remover =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load remover");
    let mut writer =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer");

    assert!(remover.invalidate("base::f"));
    writer.store("other::g", sample_non_proof_entry("other", FunctionVerdict::Inconclusive));

    writer.save_coordinated(&config).expect("save writer");
    remover.save_coordinated(&config).expect("save remover");

    let mut merged =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load merged cache");
    assert_eq!(merged.lookup("base::f", "base", "", ""), CacheLookup::Miss);
    assert_eq!(
        merged.lookup("other::g", "other", "", ""),
        CacheLookup::Hit(sample_non_proof_entry("other", FunctionVerdict::Inconclusive))
    );
}

#[test]
fn test_coordinated_invalidate_all_from_empty_local_removes_concurrent_entries() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let config = CoordinationConfig::default();

    let mut clearer =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load clearer");
    let mut writer =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer");

    writer.store("old::f", sample_entry("old", FunctionVerdict::Verified));
    writer.save_coordinated(&config).expect("save writer");

    clearer.invalidate_all();
    clearer.save_coordinated(&config).expect("save clearer");

    let merged =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load merged cache");
    assert_eq!(merged.len(), 0);
}

#[test]
fn test_coordinated_invalidate_all_then_store_drops_concurrent_entries() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let config = CoordinationConfig::default();

    let mut rewriter =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load rewriter");
    let mut writer =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer");

    writer.store("old::f", sample_entry("old", FunctionVerdict::Verified));
    writer.save_coordinated(&config).expect("save writer");

    rewriter.invalidate_all();
    rewriter.store("new::g", sample_non_proof_entry("new", FunctionVerdict::Inconclusive));
    rewriter.save_coordinated(&config).expect("save rewriter");

    let mut merged =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load merged cache");
    assert_eq!(merged.lookup("old::f", "old", "", ""), CacheLookup::Miss);
    assert_eq!(
        merged.lookup("new::g", "new", "", ""),
        CacheLookup::Hit(sample_non_proof_entry("new", FunctionVerdict::Inconclusive))
    );
}

#[test]
fn test_coordinated_retain_only_filters_concurrent_entries_without_local_removal() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    let config = CoordinationConfig::default();

    {
        let mut cache =
            VerificationCache::load_coordinated(&cache_path, &config).expect("create cache");
        cache.store("keep::f", sample_non_proof_entry("keep", FunctionVerdict::Inconclusive));
        cache.save_coordinated(&config).expect("save base");
    }

    let mut keeper =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load keeper");
    let mut writer =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load writer");

    writer.store("drop::g", sample_entry("drop", FunctionVerdict::HasViolations));
    writer.save_coordinated(&config).expect("save writer");

    keeper.retain_only(&["keep::f"]);
    keeper.save_coordinated(&config).expect("save keeper");

    let mut merged =
        VerificationCache::load_coordinated(&cache_path, &config).expect("load merged cache");
    assert_eq!(
        merged.lookup("keep::f", "keep", "", ""),
        CacheLookup::Hit(sample_non_proof_entry("keep", FunctionVerdict::Inconclusive))
    );
    assert_eq!(merged.lookup("drop::g", "drop", "", ""), CacheLookup::Miss);
}

#[test]
fn test_cache_persistence_with_timestamp() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");

    let func = make_function("stamped");
    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store_function(&func, FunctionVerdict::Verified, 2, 2, 0, 0, 0, "");
        cache.save().expect("save cache");
    }

    // Read back and verify timestamp survived
    {
        let mut cache = VerificationCache::load(&cache_path).expect("load cache");
        // Represent a fresh independent solve. The equivalent-store fast path
        // keeps the original persisted timestamp while granting only this
        // process in-session replay authority.
        assert!(!cache.store_function(&func, FunctionVerdict::Verified, 2, 2, 0, 0, 0, "",));
        match cache.lookup_function(&func, "") {
            CacheLookup::Hit(entry) => {
                assert!(entry.cached_at > 0, "timestamp should survive persistence");
            }
            CacheLookup::Miss => panic!("expected hit after independent revalidation"),
        }
    }
}

#[test]
fn test_cache_handles_corrupt_file() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    std::fs::write(&cache_path, "not valid json{{{").expect("write corrupt file");

    let cache = VerificationCache::load(&cache_path).expect("should not fail on corrupt");
    assert!(cache.is_empty(), "corrupt cache should start fresh");
}

#[test]
fn test_cache_handles_version_mismatch() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    std::fs::write(&cache_path, r#"{"version": 999, "entries": {}}"#)
        .expect("write future version");

    let cache = VerificationCache::load(&cache_path).expect("should not fail on version mismatch");
    assert!(cache.is_empty(), "version mismatch should start fresh");
}

#[test]
fn test_cache_handles_old_version() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("trust-cache.json");
    // Old version 1 cache should be discarded
    std::fs::write(&cache_path, r#"{"version": 1, "entries": {}}"#).expect("write old version");

    let cache = VerificationCache::load(&cache_path).expect("should not fail on old version");
    assert!(cache.is_empty(), "old version cache should start fresh");
}

#[test]
fn test_cache_len_and_is_empty() {
    let mut cache = VerificationCache::in_memory();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);

    cache.store("m::f", sample_entry("h", FunctionVerdict::Verified));
    assert!(!cache.is_empty());
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_cache_save_creates_parent_dirs() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("nested").join("deep").join("trust-cache.json");

    let mut cache = VerificationCache::load(&cache_path).expect("create cache");
    cache.store("m::f", sample_entry("h", FunctionVerdict::Verified));
    cache.save().expect("save should create parent dirs");
    assert!(cache_path.exists());
}

#[test]
fn test_in_memory_cache_save_is_noop() {
    let mut cache = VerificationCache::in_memory();
    cache.save().expect("in-memory save should be no-op");
}

// -----------------------------------------------------------------------
// Summary and statistics
// -----------------------------------------------------------------------

#[test]
fn test_cache_summary() {
    let mut cache = VerificationCache::in_memory();
    cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
    cache.store("b::g", sample_entry("h2", FunctionVerdict::Verified));
    cache.lookup("a::f", "h1", "", ""); // hit
    cache.lookup("c::h", "h3", "", ""); // miss

    let summary = cache.summary();
    assert_eq!(summary, "1 hits, 1 misses, 2 cached");
}

#[test]
fn test_invalidate_all_then_store() {
    let mut cache = VerificationCache::in_memory();
    cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
    cache.store("b::g", sample_entry("h2", FunctionVerdict::Verified));
    cache.invalidate_all();

    // Can store again after invalidation
    cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));
    assert_eq!(cache.len(), 1);
    assert_eq!(
        cache.lookup("c::h", "h3", "", ""),
        CacheLookup::Hit(sample_entry("h3", FunctionVerdict::Inconclusive))
    );
}

// -----------------------------------------------------------------------
// Regression tests for #372 and #368
// -----------------------------------------------------------------------

/// Regression test for #372: compute_content_hash() must agree with
/// VerifiableFunction::content_hash().
#[test]
fn test_compute_content_hash_matches_method() {
    let func = make_function("foo");
    assert_eq!(
        compute_content_hash(&func),
        func.content_hash(),
        "compute_content_hash() must delegate to VerifiableFunction::content_hash()"
    );
}

/// Regression test for #372: both hash functions must agree even with
/// contracts present.
#[test]
fn test_compute_content_hash_matches_method_with_contracts() {
    let func = make_function_with_contract("bar", "result > 0");
    assert_eq!(
        compute_content_hash(&func),
        func.content_hash(),
        "compute_content_hash() must match content_hash() with contracts"
    );
}

/// Regression test for #368: content_hash() must produce a 64-char SHA-256
/// hex digest, not a 16-char DefaultHasher output.
#[test]
fn test_content_hash_is_sha256_not_default_hasher() {
    let func = make_function("foo");
    let hash = func.content_hash();
    // SHA-256 = 64 hex chars; DefaultHasher = 16 hex chars
    assert_eq!(
        hash.len(),
        64,
        "content_hash() should be SHA-256 (64 hex chars), got {} chars: {}",
        hash.len(),
        hash
    );
    assert!(hash.chars().all(|c| c.is_ascii_hexdigit()), "content_hash() must be valid hex");
}

// -----------------------------------------------------------------------
// Regression tests for #690: spec_hash validation on lookup
// -----------------------------------------------------------------------

/// Regression test for #690: lookup must miss when spec_hash differs,
/// even if content_hash matches. This prevents stale "proved" verdicts
/// when a spec is strengthened but the function body stays the same.
#[test]
fn test_lookup_misses_on_spec_hash_mismatch() {
    let mut cache = VerificationCache::in_memory();
    let mut entry = sample_entry("body_hash", FunctionVerdict::Verified);
    entry.spec_hash = "spec_v1".to_string();
    cache.store("m::f", entry);

    // Same content_hash but different spec_hash: must miss
    assert_eq!(
        cache.lookup("m::f", "body_hash", "spec_v2", ""),
        CacheLookup::Miss,
        "spec change must cause cache miss even with same body hash"
    );
    // Same content_hash and same spec_hash: must hit
    assert_eq!(
        cache.lookup("m::f", "body_hash", "spec_v1", ""),
        CacheLookup::Hit(CacheEntry {
            content_hash: "body_hash".to_string(),
            verdict: FunctionVerdict::Verified,
            total_obligations: 3,
            proved: 2,
            failed: 0,
            unknown: 1,
            runtime_checked: 0,
            cached_at: 0,
            spec_hash: "spec_v1".to_string(),
            solver_fingerprint: String::new(),
            obligation_results: vec![],
        })
    );
}

/// regression: an empty *stored* spec_hash must not act as a
/// wildcard that matches a non-empty incoming spec_hash. Such an entry (written
/// before a spec existed, or deserialized without one) was previously served as
/// `proved` even after a real spec was added — a false-PROVE on cache hit.
#[test]
fn test_empty_stored_spec_hash_is_not_a_wildcard() {
    let mut cache = VerificationCache::in_memory();
    let mut entry = sample_entry("body_hash", FunctionVerdict::Verified);
    entry.spec_hash = String::new(); // stored with no spec fingerprint
    cache.store("m::f", entry);

    // A function that now carries a real spec must NOT hit the spec-less entry.
    assert_eq!(
        cache.lookup("m::f", "body_hash", "real_spec_hash", ""),
        CacheLookup::Miss,
        "empty stored spec_hash must not wildcard-match a real incoming spec_hash"
    );
    // An empty incoming hash still matches the empty stored hash (true equality).
    assert!(
        matches!(cache.lookup("m::f", "body_hash", "", ""), CacheLookup::Hit(_)),
        "equal (both-empty) spec hashes must still hit"
    );
}

/// Regression test for #690: lookup_function must miss when a contract
/// changes, even if the function body is identical.
#[test]
fn test_lookup_function_misses_on_spec_change() {
    let func_v1 = make_function_with_contract("foo", "result > 0");
    let mut cache = VerificationCache::in_memory();
    cache.store_function(&func_v1, FunctionVerdict::Verified, 1, 1, 0, 0, 0, "");

    // Lookup with same spec: should hit
    assert!(
        matches!(cache.lookup_function(&func_v1, ""), CacheLookup::Hit(_)),
        "identical function+spec must hit"
    );

    // Strengthen the postcondition: body identical, spec changed
    let func_v2 = make_function_with_contract("foo", "result > 0 && result < 100");
    let result = cache.lookup_function(&func_v2, "");
    assert_eq!(result, CacheLookup::Miss, "strengthened postcondition must cause cache miss");
}

// -----------------------------------------------------------------------
// HMAC integrity tests
// -----------------------------------------------------------------------

/// Disk persistence preserves the record but never grants proof authority.
#[test]
fn test_persisted_proof_requires_in_process_revalidation() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("hmac-test.json");

    // Write with HMAC
    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.save().expect("save with HMAC");
    }

    // Read back: the compatibility tag verifies and the record remains
    // inspectable, but a cross-process proof claim must not replay.
    {
        let mut cache = VerificationCache::load(&cache_path).expect("load cache");
        assert_eq!(cache.len(), 1, "tagged cache should preserve the record");
        assert_eq!(
            cache.lookup("m::f", "h1", "", ""),
            CacheLookup::Miss,
            "disk-origin proof must be revalidated, even with a valid tag"
        );

        // `store` represents the caller's fresh in-process verification. A
        // byte-identical record need not be rewritten, but is now eligible for
        // honest reuse within this process.
        assert!(!cache.store("m::f", sample_entry("h1", FunctionVerdict::Verified)));
        assert!(matches!(cache.lookup("m::f", "h1", "", ""), CacheLookup::Hit(_)));
    }
}

/// A local writer can derive the compatibility-tag key and forge a perfectly
/// valid `Verified` JSON record. The origin boundary—not the tag—must reject it.
#[test]
fn test_forged_tagged_persisted_proof_is_not_replayed() {
    use std::collections::BTreeMap;

    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("forged-proof.json");
    let mut entries = BTreeMap::new();
    entries.insert("m::f".to_string(), sample_entry("h1", FunctionVerdict::Verified));
    let entries_json = serde_json::to_string(&entries).expect("serialize forged entries");
    let key = crate::integrity::derive_cache_key();
    let hmac = crate::integrity::compute_hmac(&key, entries_json.as_bytes());
    let forged = serde_json::json!({
        "version": CACHE_VERSION,
        "entries": entries,
        "hmac": hmac,
    });
    std::fs::write(
        &cache_path,
        serde_json::to_vec_pretty(&forged).expect("serialize forged cache"),
    )
    .expect("write forged cache");

    let mut cache = VerificationCache::load(&cache_path).expect("load forged cache");
    assert_eq!(cache.len(), 1, "the tag is structurally valid");
    assert_eq!(
        cache.lookup("m::f", "h1", "", ""),
        CacheLookup::Miss,
        "a user-forgeable valid tag must never authorize a persisted proof"
    );
}

/// A zero-total record asserts that verification generated no obligations. That
/// is proof authority even when a forger disguises it as `Inconclusive` with no
/// proved rows: replaying it lets the compiler synthesize `NoObligations`.
#[test]
fn test_forged_tagged_zero_total_record_is_not_replayed() {
    use std::collections::BTreeMap;

    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("forged-zero-total.json");
    let mut entry = sample_non_proof_entry("h1", FunctionVerdict::Inconclusive);
    entry.total_obligations = 0;
    entry.unknown = 0;

    let mut entries = BTreeMap::new();
    entries.insert("m::f".to_string(), entry);
    let entries_json = serde_json::to_string(&entries).expect("serialize forged entries");
    let key = crate::integrity::derive_cache_key();
    let hmac = crate::integrity::compute_hmac(&key, entries_json.as_bytes());
    let forged = serde_json::json!({
        "version": CACHE_VERSION,
        "entries": entries,
        "hmac": hmac,
    });
    std::fs::write(
        &cache_path,
        serde_json::to_vec_pretty(&forged).expect("serialize forged cache"),
    )
    .expect("write forged cache");

    let mut cache = VerificationCache::load(&cache_path).expect("load forged cache");
    assert_eq!(cache.len(), 1, "the tag is structurally valid");
    assert_eq!(
        cache.lookup("m::f", "h1", "", ""),
        CacheLookup::Miss,
        "a disk record may not authorize a zero-obligation conclusion"
    );
}

/// Nested runtime-check, monitor, and design-mandate fields all affect later
/// authority decisions even when the entry's top-level counters and verdict are
/// inconclusive. A forgeable disk record must not replay any of them without
/// fresh in-process validation.
#[test]
fn test_forged_tagged_nested_authority_side_channels_are_not_replayed() {
    use std::collections::BTreeMap;

    let mut runtime_checked = sample_non_proof_transport_result();
    runtime_checked.outcome = Outcome::RuntimeChecked;

    let mut monitored = sample_non_proof_transport_result();
    monitored.monitor = Some(TransportMonitorEvidence {
        status: TransportMonitorStatus::Monitored,
        reason: "forged monitor certificate".to_string(),
        predicate_digest: format!("sha256:{}", "a".repeat(64)),
    });

    let mut design_mandate = sample_non_proof_transport_result();
    design_mandate.design_mandate = true;

    for (label, result) in [
        ("runtime-checked", runtime_checked),
        ("monitor", monitored),
        ("design-mandate", design_mandate),
    ] {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join(format!("forged-{label}.json"));
        let mut entry = sample_non_proof_entry("h1", FunctionVerdict::Inconclusive);
        entry.obligation_results = vec![result];

        let mut entries = BTreeMap::new();
        entries.insert("m::f".to_string(), entry);
        let entries_json = serde_json::to_string(&entries).expect("serialize forged entries");
        let key = crate::integrity::derive_cache_key();
        let hmac = crate::integrity::compute_hmac(&key, entries_json.as_bytes());
        let forged = serde_json::json!({
            "version": CACHE_VERSION,
            "entries": entries,
            "hmac": hmac,
        });
        std::fs::write(
            &cache_path,
            serde_json::to_vec_pretty(&forged).expect("serialize forged cache"),
        )
        .expect("write forged cache");

        let mut cache = VerificationCache::load(&cache_path).expect("load forged cache");
        assert_eq!(cache.len(), 1, "the {label} tag is structurally valid");
        assert_eq!(
            cache.lookup("m::f", "h1", "", ""),
            CacheLookup::Miss,
            "a disk record may not authorize nested {label} evidence",
        );
    }
}

/// #725: Tampered cache file must be rejected (starts fresh).
#[test]
fn test_hmac_rejects_tampered_cache() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("tampered.json");

    // Write a valid cache
    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", sample_entry("h1", FunctionVerdict::HasViolations));
        cache.save().expect("save cache");
    }

    // Tamper: change "HasViolations" to "Verified" in the JSON
    {
        let contents = std::fs::read_to_string(&cache_path).expect("read cache");
        let tampered = contents.replace("HasViolations", "Verified");
        assert_ne!(contents, tampered, "tamper should change file content");
        std::fs::write(&cache_path, tampered).expect("write tampered");
    }

    // Load should reject tampered file
    {
        let cache = VerificationCache::load(&cache_path).expect("load tampered");
        assert!(cache.is_empty(), "tampered cache must be rejected");
    }
}

/// #725: Cache file with empty HMAC (legacy v2 upgraded to v3) is rejected.
#[test]
fn test_hmac_rejects_empty_hmac() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("no-hmac.json");

    // Write a v3 cache with no HMAC (simulating legacy upgrade)
    let json = format!(r#"{{"version": {}, "entries": {{}}, "hmac": ""}}"#, CACHE_VERSION);
    std::fs::write(&cache_path, json).expect("write no-hmac file");

    let cache = VerificationCache::load(&cache_path).expect("load no-hmac");
    assert!(cache.is_empty(), "empty HMAC must be rejected");
}

/// #725: Saved cache file contains non-empty HMAC field.
#[test]
fn test_saved_cache_has_hmac() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cache_path = dir.path().join("has-hmac.json");

    {
        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.save().expect("save cache");
    }

    // Verify the on-disk file has an hmac field
    let contents = std::fs::read_to_string(&cache_path).expect("read cache");
    let parsed: serde_json::Value = serde_json::from_str(&contents).expect("parse saved JSON");
    let hmac_val = parsed.get("hmac").expect("hmac field must exist");
    let hmac_str = hmac_val.as_str().expect("hmac must be string");
    assert_eq!(hmac_str.len(), 64, "HMAC-SHA256 hex is 64 chars");
    assert!(hmac_str.chars().all(|c| c.is_ascii_hexdigit()));
}

// -----------------------------------------------------------------------
// v5: solver_fingerprint must match on lookup (catches out-of-process
// solver rebuilds that the trustc binary hash cannot detect on its own).
// -----------------------------------------------------------------------

#[test]
fn test_lookup_misses_on_solver_fingerprint_mismatch() {
    let func = make_function("foo");
    let mut cache = VerificationCache::in_memory();
    cache.store_function(&func, FunctionVerdict::Verified, 1, 1, 0, 0, 0, "ay-v1");

    // Same content + spec, different solver fingerprint → miss.
    assert_eq!(
        cache.lookup_function(&func, "ay-v2"),
        CacheLookup::Miss,
        "solver rebuild must invalidate cached proofs"
    );
    // Same solver fingerprint → hit.
    assert!(matches!(cache.lookup_function(&func, "ay-v1"), CacheLookup::Hit(_)));
}

#[test]
fn test_compute_solver_fingerprint_changes_with_solver_name() {
    let path = write_temp_solver("solver-name", b"same solver bytes");
    let fp_a = compute_solver_fingerprint("ay", Some(&path));
    let fp_b = compute_solver_fingerprint("cvc5", Some(&path));
    let _ = std::fs::remove_file(path);
    assert_ne!(fp_a, fp_b, "different solver names must produce different fingerprints");
}

#[test]
fn test_compute_solver_fingerprint_no_path_is_ineligible() {
    assert_eq!(compute_solver_fingerprint("ay", None), None);
}

// Write `bytes` to a uniquely-named temp file and return its path. The caller
// is responsible for removing it.
fn write_temp_solver(tag: &str, bytes: &[u8]) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("trust-fp-test-{}-{tag}-{n}", std::process::id()));
    std::fs::write(&path, bytes).expect("write temp solver binary");
    path
}

#[test]
fn test_solver_fingerprint_is_path_independent() {
    // The same solver bytes installed at two different paths (as on two
    // different machines) must produce the SAME fingerprint — this is the
    // property that lets cache entries be shared across machines.
    let bytes = b"\x7fELF fake solver binary contents v1";
    let path_a = write_temp_solver("loc-a", bytes);
    let path_b = write_temp_solver("loc-b", bytes);

    let fp_a = compute_solver_fingerprint("ay", Some(&path_a));
    let fp_b = compute_solver_fingerprint("ay", Some(&path_b));

    let _ = std::fs::remove_file(&path_a);
    let _ = std::fs::remove_file(&path_b);

    assert_ne!(path_a, path_b, "test setup: paths must differ");
    assert!(fp_a.is_some());
    assert_eq!(fp_a, fp_b, "identical solver bytes at different paths must match");
}

#[test]
fn test_solver_fingerprint_changes_with_content() {
    // A solver rebuild that changes the binary's bytes must rotate the
    // fingerprint, so stale proofs are not reused.
    let path_v1 = write_temp_solver("content", b"solver build v1");
    let fp_v1 = compute_solver_fingerprint("ay", Some(&path_v1));

    std::fs::write(&path_v1, b"solver build v2 -- different bytes").unwrap();
    let fp_v2 = compute_solver_fingerprint("ay", Some(&path_v1));

    let _ = std::fs::remove_file(&path_v1);

    assert_ne!(fp_v1, fp_v2, "different solver contents must produce different fingerprints");
}

#[cfg(unix)]
#[test]
fn test_solver_snapshot_fingerprint_matches_exact_copied_bytes() {
    use std::os::unix::fs::PermissionsExt;

    let source = write_temp_solver("snapshot-source", b"#!/bin/sh\nexit 7\n");
    std::fs::set_permissions(&source, std::fs::Permissions::from_mode(0o755)).unwrap();
    let snapshot = source.with_extension("immutable-snapshot");

    let identity = snapshot_solver_binary("ay", &source, &snapshot).expect("snapshot solver");
    assert_eq!(std::fs::read(&snapshot).unwrap(), b"#!/bin/sh\nexit 7\n");
    assert_eq!(
        std::fs::metadata(&snapshot).unwrap().permissions().mode() & 0o222,
        0,
        "the execution snapshot must not remain writable"
    );
    assert_eq!(
        fingerprint_solver_binary("ay", &snapshot).unwrap(),
        identity,
        "the returned digest must identify the exact executable snapshot"
    );

    // Mutating the selected source after identity construction cannot change
    // either the command bytes or the key of the snapshot that will execute.
    std::fs::write(&source, b"#!/bin/sh\nexit 99\n").unwrap();
    assert_eq!(std::fs::read(&snapshot).unwrap(), b"#!/bin/sh\nexit 7\n");
    assert_eq!(fingerprint_solver_binary("ay", &snapshot).unwrap(), identity);

    let _ = std::fs::remove_file(source);
    let _ = std::fs::remove_file(snapshot);
}

#[cfg(unix)]
#[test]
fn test_solver_snapshot_never_follows_existing_destination_symlink() {
    use std::os::unix::fs::{PermissionsExt, symlink};

    let source = write_temp_solver("snapshot-symlink-source", b"#!/bin/sh\nexit 0\n");
    std::fs::set_permissions(&source, std::fs::Permissions::from_mode(0o755)).unwrap();
    let victim = write_temp_solver("snapshot-victim", b"do not overwrite");
    let snapshot = source.with_extension("snapshot-link");
    symlink(&victim, &snapshot).unwrap();

    assert!(
        snapshot_solver_binary("ay", &source, &snapshot).is_err(),
        "create_new must reject a pre-existing symlink"
    );
    assert_eq!(std::fs::read(&victim).unwrap(), b"do not overwrite");

    let _ = std::fs::remove_file(source);
    let _ = std::fs::remove_file(snapshot);
    let _ = std::fs::remove_file(victim);
}

#[test]
fn test_solver_fingerprint_missing_path_is_ineligible() {
    let missing = std::env::temp_dir().join("trust-fp-test-definitely-missing-xyz");
    let _ = std::fs::remove_file(&missing);
    let fp = compute_solver_fingerprint("ay", Some(&missing));
    assert_eq!(fp, None, "a read failure must never fall back to a weak size key");
}

#[cfg(unix)]
#[test]
fn test_same_size_unreadable_solver_is_uncacheable() {
    use std::os::unix::fs::PermissionsExt;

    let readable = write_temp_solver("readable-same-size", b"solver bytes A");
    let unreadable = write_temp_solver("unreadable-same-size", b"solver bytes B");
    assert_eq!(
        std::fs::metadata(&readable).unwrap().len(),
        std::fs::metadata(&unreadable).unwrap().len(),
        "test setup: the old size fallback would collide"
    );
    std::fs::set_permissions(&unreadable, std::fs::Permissions::from_mode(0o111)).unwrap();

    let readable_identity = fingerprint_solver_binary("ay", &readable).expect("readable solver");
    let unreadable_identity = fingerprint_solver_binary("ay", &unreadable);

    std::fs::set_permissions(&unreadable, std::fs::Permissions::from_mode(0o600)).unwrap();
    let _ = std::fs::remove_file(&readable);
    let _ = std::fs::remove_file(&unreadable);

    assert_eq!(readable_identity.cache_key().len(), 64);
    assert!(
        unreadable_identity.is_err(),
        "same file size must not rescue an unreadable solver into cache eligibility"
    );
}

// Ensure CacheError variants are reachable in test code paths.
#[allow(dead_code)]
fn _force_error_use() -> Result<(), CacheError> {
    Ok(())
}
