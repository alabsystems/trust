// trust-router/solver_cache.rs: VC-level solver result caching
//
// Wraps the Router to intercept verify_one/verify_all calls and check a
// ResultCache before dispatching to backends. Cache key is (formula_hash,
// solver_name) — the same VC sent to the same solver returns the cached
// result without invoking the solver.
//
// Wire trust-cache into production verification path.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::sync::Mutex;

use trust_cache::result_cache::{
    CachePolicy, CacheStats, CachedResult, ResultCache, ResultCacheKey, hash_formula,
};
use trust_types::fx::FxHashMap;
use trust_types::{Formula, ProofStrength, Sort, VerificationCondition, VerificationResult};

// Import from trust-cache (canonical location) instead of crate re-export.
use crate::Router;

/// Reserved canonical-name prefix used by free-variable alpha-normalization.
///
/// Free variables are rewritten to `__trust_fv0`, `__trust_fv1`, ... in first
/// occurrence (structural pre-order) order. The prefix is deliberately long and
/// `trustc`-specific so it cannot collide with a real MIR-local (`_3`) or a
/// vcgen-synthesized symbol; if a source formula nevertheless already contains a
/// name with this prefix, normalization FAILS CLOSED (see
/// [`alpha_canonicalize_free_vars`]) rather than risk merging two distinct
/// variables onto one canonical name.
const FV_CANON_PREFIX: &str = "__trust_fv";

/// Compute a deterministic SHA-256 hash of a `VerificationCondition`'s formula.
///
/// # Soundness contract
///
/// This hash is the result-cache key (`ResultCacheKey::formula_hash`). Two VCs
/// share a cached verdict **iff** their formulas hash equal. Therefore two
/// distinct formulas may map to the same hash ONLY when they are genuinely
/// equivalent — here, alpha-equivalent: identical structure up to a consistent
/// bijective renaming of the free variables (same constants, operators, widths,
/// sorts, and structure). A hash collision between non-equivalent formulas would
/// replay one obligation's verdict for the other — a false proof.
///
/// We first attempt a conservative free-variable alpha-normalization
/// ([`alpha_canonicalize_free_vars`]) so that two functions whose obligations are
/// identical up to MIR-local renaming (`_0`/`_1` in `f` vs `g`) collide
/// intentionally and share a verdict. When normalization is not provably sound
/// for a given formula (it contains a quantifier, or already uses a reserved
/// canonical name), we FALL BACK to hashing the raw, un-renamed SMT-LIB — which
/// is exactly the legacy behavior and never over-merges. Correctness over
/// hit-rate: a missed merge only costs a re-solve; a wrong merge is unsound.
///
/// The hash is over serde's exact structural representation of the canonical
/// `Formula`, not SMT-LIB text. The SMT renderer deliberately omits some AST
/// payloads that a solver recovers from declarations or context; those omissions
/// are valid for printing but not for proof-cache identity. Derived serialization
/// automatically covers every current and future formula variant and all of its
/// sort/width/format payloads. SHA-256 provides collision resistance to ~2^128.
/// See #692, #754.
#[must_use]
pub fn vc_formula_hash(vc: &VerificationCondition) -> String {
    // Prefer the alpha-normalized form so structurally-identical obligations
    // across functions (which differ only in MIR-local naming) collide and share
    // a verdict. Fall back to the raw SMT-LIB on any case we cannot normalize
    // soundly — falling back can only *reduce* hits, never produce a wrong one.
    let canonical = alpha_canonicalize_free_vars(&vc.formula);
    let hashed_formula = canonical.as_ref().unwrap_or(&vc.formula);
    let structural = serde_json::to_string(hashed_formula)
        .expect("Formula serialization contains no fallible data model");
    hash_formula(&structural)
}

/// Alpha-normalize the **free** variables of a quantifier-free formula to a
/// canonical, position-determined order, or return `None` if it cannot do so
/// soundly.
///
/// MIR-locals (`_0`, `_1`, …) and most vcgen-synthesized operands appear in VC
/// formulas as *free* `Var`/`SymVar` leaves. Two functions can emit the same
/// obligation up to a consistent renaming of these locals (`_0 < _1` in `f` is
/// the same proof problem as `_3 < _7` in `g`). Renaming each distinct free
/// variable to `__trust_fvN` by first structural occurrence makes such
/// obligations share a result-cache verdict.
///
/// # Why this is sound (and where it deliberately bails)
///
/// The whole game is: the returned formula must be alpha-EQUIVALENT to the input
/// — its canonical SMT-LIB must be equal to another formula's canonical SMT-LIB
/// *only* when the two are identical up to a consistent **bijective** renaming of
/// free variables. The transform preserves that because:
///
/// * It is **quantifier-free**: if the formula contains any `Forall`/`Exists`,
///   we return `None`. With no binders, every `Var`/`SymVar` leaf is free, so we
///   never need binder-scope tracking and can never accidentally capture a bound
///   variable or treat a bound variable as free. (Quantified VCs are rare; the
///   raw-hash fallback is always sound for them.)
/// * The rename is a **bijection**: distinct source names map to distinct
///   `__trust_fvN` names (one entry per name in `mapping`, never merged), and the
///   numbering is injective. So two *different* free variables can never collapse
///   onto one canonical name.
/// * Numbering is by **first occurrence in a fixed structural pre-order**, the
///   same total order for any two alpha-equivalent formulas, so equivalent inputs
///   produce *identical* renamed forms (and thus equal hashes), while any
///   structural difference (a different constant, operator, width, sort, or
///   shape) survives into the renamed form and keeps the hashes apart.
/// * Sorts and all non-variable payload (widths, constants, predicate names) are
///   carried through unchanged by reusing the trusted `Formula::map`; only the
///   *name* of a free `Var`/`SymVar` is rewritten.
/// * If any source variable already uses the reserved [`FV_CANON_PREFIX`], we
///   return `None`: a pre-existing `__trust_fvK` could otherwise alias a name we
///   generate and merge two distinct variables. Fail closed.
fn alpha_canonicalize_free_vars(formula: &Formula) -> Option<Formula> {
    // Bail on quantifiers: with binders present, distinguishing free from bound
    // occurrences requires scope tracking that this conservative pass does not do.
    // Bail too if a reserved canonical name is already in use (collision risk).
    let mut has_quantifier = false;
    let mut reserved_name_in_use = false;
    formula.visit(&mut |f| match f {
        Formula::Forall(..) | Formula::Exists(..) => has_quantifier = true,
        Formula::Var(name, _) => {
            if name.starts_with(FV_CANON_PREFIX) {
                reserved_name_in_use = true;
            }
        }
        Formula::SymVar(sym, _) => {
            if sym.as_str().starts_with(FV_CANON_PREFIX) {
                reserved_name_in_use = true;
            }
        }
        _ => {}
    });
    if has_quantifier || reserved_name_in_use {
        return None;
    }

    // Assign canonical names by first structural occurrence (depth-first
    // pre-order). `mapping` is an injective name->name bijection.
    let mut mapping: FxHashMap<String, String> = FxHashMap::default();
    assign_canonical_names(formula, &mut mapping);

    // Rewrite every free Var/SymVar leaf to its canonical Var, preserving sort.
    // SymVar is normalized to Var so that two formulas that differ only in
    // String-vs-interned representation of the *same* variable still collide;
    // `to_smtlib` renders both identically anyway, but normalizing the node keeps
    // the canonical AST representation-independent.
    let canonical = formula.clone().map(&mut |node| match node {
        Formula::Var(name, sort) => rename_leaf(&name, sort, &mapping),
        Formula::SymVar(sym, sort) => rename_leaf(sym.as_str(), sort, &mapping),
        other => other,
    });
    Some(canonical)
}

/// Walk `formula` in depth-first pre-order, inserting a canonical name for each
/// distinct free-variable name the first time it is seen.
///
/// Pre-order over `Formula::children()` is a fixed total order shared by any two
/// alpha-equivalent formulas, so the resulting `name -> __trust_fvN` map is
/// identical for equivalent inputs. Caller has already verified the formula is
/// quantifier-free, so every `Var`/`SymVar` encountered is free.
fn assign_canonical_names(formula: &Formula, mapping: &mut FxHashMap<String, String>) {
    match formula {
        Formula::Var(name, _) => intern_canonical(name, mapping),
        Formula::SymVar(sym, _) => intern_canonical(sym.as_str(), mapping),
        _ => {
            for child in formula.children() {
                assign_canonical_names(child, mapping);
            }
        }
    }
}

/// Insert a fresh `__trust_fvN` canonical name for `name` if not already mapped.
fn intern_canonical(name: &str, mapping: &mut FxHashMap<String, String>) {
    if !mapping.contains_key(name) {
        let canonical = format!("{FV_CANON_PREFIX}{}", mapping.len());
        mapping.insert(name.to_string(), canonical);
    }
}

/// Rewrite a variable leaf to its canonical `Var(__trust_fvN__<sort>, sort)`.
///
/// `mapping` always contains `name` because [`assign_canonical_names`] visits the
/// exact same leaves before the rewrite; the `unwrap_or_else` is a defensive
/// identity fallback that preserves soundness (it never merges names).
///
/// SOUNDNESS: the canonical NAME embeds the variable's `sort` (`{position}__{sort}`).
/// `Formula::to_smtlib` renders a `Var` as its bare symbol and DROPS the sort, so
/// without this two leaves that are structurally identical but differently sorted
/// (`_0 : BitVec(1)` vs `_0 : Int`) would render to the same symbol and collide on
/// one cache key — even though e.g. `distinct(a,b,c)` is UNSAT over `BitVec(1)`
/// (pigeonhole) but SAT over `Int`. Folding the sort into the symbol forces the
/// difference into the hashed SMT-LIB text. (Position numbering still comes from
/// the by-name `mapping`, so the rename stays a bijection over names; appending the
/// sort can only ever *split* a would-be collision, never merge two distinct vars.)
fn rename_leaf(name: &str, sort: Sort, mapping: &FxHashMap<String, String>) -> Formula {
    let position = mapping.get(name).cloned().unwrap_or_else(|| name.to_string());
    let canonical = format!("{position}__{}", sort.to_smtlib());
    Formula::Var(canonical, sort)
}

/// Convert a `VerificationResult` to a verdict string for cache storage.
///
/// Stored verdicts are read back by the parse below, so the two must name the
/// same conclusions. Both go through the shared outcome vocabulary, which is
/// what makes that agreement a property of the type rather than of two lists
/// staying in sync.
fn verdict_string(result: &VerificationResult) -> &'static str {
    result.outcome().as_str()
}

/// Convert a `VerificationResult` to an optional model string for cache storage.
fn model_string(result: &VerificationResult) -> Option<String> {
    match result {
        VerificationResult::Failed { counterexample: Some(cex), .. } => Some(format!("{cex:?}")),
        _ => None,
    }
}

/// Extract the `ProofStrength` from a proved result as JSON for cache storage.
///
/// Preserves the original proof strength through the cache
/// instead of always defaulting to `smt_unsat()`.
fn strength_json(result: &VerificationResult) -> Option<String> {
    match result {
        VerificationResult::Proved { strength, .. } => serde_json::to_string(strength).ok(),
        _ => None,
    }
}

/// Extract the proof-certificate bytes from a proved result for cache storage,
/// so a later replay is evidence-equivalent to the fresh solve (see
/// [`CachedResult::proof_certificate`]).
fn certificate_bytes(result: &VerificationResult) -> Option<Vec<u8>> {
    match result {
        VerificationResult::Proved { proof_certificate, .. } => proof_certificate.clone(),
        _ => None,
    }
}

/// Convert a cached entry back to a `VerificationResult`.
///
/// Reconstructs the result from the stored verdict, solver name, and timing.
/// Counterexamples are not preserved through the cache (the model string is
/// informational only). This is acceptable because cache hits on Failed
/// results correctly report the failure — the counterexample can be
/// regenerated by re-running the solver if needed.
fn result_from_cached(entry: &CachedResult) -> VerificationResult {
    // A verdict this vocabulary does not recognize — a corrupt entry, or one
    // written by a toolchain that knows outcomes this one does not — reads as
    // `None` and falls through to `Unknown`, so a cache replay can never mint a
    // conclusion the reader cannot name.
    match trust_types::Outcome::parse(&entry.verdict) {
        Some(trust_types::Outcome::Proved) => {
            // Restore original ProofStrength from cache if available.
            // if a "proved" entry's strength is absent or
            // un-deserializable, that is a cache-integrity gap — stamp the HONEST
            // unvalidated level (`Unchecked`), NOT `smt_unsat()` (which is
            // `Sound` and would PASS the report-boundary assurance gate, minting
            // a forged `Proved` from a tampered/corrupt cache). The gate then
            // downgrades this `Unchecked` proved to `Unknown` and it re-verifies.
            let strength = entry
                .strength_json
                .as_deref()
                .and_then(|json| serde_json::from_str::<ProofStrength>(json).ok())
                .unwrap_or_else(ProofStrength::smt_unsat_unvalidated);
            VerificationResult::Proved {
                solver: format!("cached:{}", entry.key.solver_name).into(),
                time_ms: 0,
                strength,
                // Restore the certificate bytes captured at solve time, so a
                // replay is evidence-equivalent to the fresh solve: the `-full`
                // evidence lane is fail-closed (no retained bytes -> no
                // evidence), and dropping the certificate here silently
                // weakened the evidence DAG of every deduplicated obligation.
                proof_certificate: entry.proof_certificate.clone(),
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
        Some(trust_types::Outcome::Failed) => VerificationResult::Failed {
            solver: format!("cached:{}", entry.key.solver_name).into(),
            time_ms: 0,
            counterexample: None,
        },
        Some(trust_types::Outcome::Timeout) => VerificationResult::Timeout {
            solver: format!("cached:{}", entry.key.solver_name).into(),
            timeout_ms: entry.time_ms,
        },
        _ => VerificationResult::Unknown {
            solver: format!("cached:{}", entry.key.solver_name).into(),
            time_ms: 0,
            reason: format!("cached result: {}", entry.verdict),
        },
    }
}

/// A Router wrapper that caches solver results at the VC dispatch level.
///
/// Before dispatching a VC to a solver backend, checks the `ResultCache` for
/// a previous result with the same formula hash and solver name. On cache hit,
/// returns the cached result without invoking the solver. On cache miss,
/// dispatches to the solver and stores the result.
///
/// Thread-safe: the inner `ResultCache` is protected by a `Mutex` so that
/// `verify_all_parallel` can share it across threads.
pub struct SolverCachedRouter {
    router: Router,
    cache: Mutex<ResultCache>,
}

struct PendingCacheMiss {
    cache_keys: Vec<ResultCacheKey>,
    vc: VerificationCondition,
    result_indices: Vec<usize>,
}

impl SolverCachedRouter {
    /// Create a new solver-cached router wrapping the given router.
    #[must_use]
    pub fn new(router: Router, policy: CachePolicy) -> Self {
        Self { router, cache: Mutex::new(ResultCache::new(policy)) }
    }

    /// Create with a pre-populated cache (e.g., loaded from disk).
    #[must_use]
    pub fn with_cache(router: Router, cache: ResultCache) -> Self {
        Self { router, cache: Mutex::new(cache) }
    }

    /// Access the underlying router.
    #[must_use]
    pub fn router(&self) -> &Router {
        &self.router
    }

    /// Return current cache statistics.
    #[must_use]
    pub fn cache_stats(&self) -> CacheStats {
        self.cache.lock().expect("cache mutex poisoned").cache_stats()
    }

    /// Return the number of cached entries.
    #[must_use]
    pub fn cache_entry_count(&self) -> usize {
        self.cache.lock().expect("cache mutex poisoned").entry_count()
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        let stats = self.cache_stats();
        let mut s = String::new();
        let _ = write!(
            s,
            "solver-cache: {} entries, {} hits, {} misses",
            stats.total_entries, stats.hits, stats.misses
        );
        if stats.hits + stats.misses > 0 {
            let rate = stats.hits as f64 / (stats.hits + stats.misses) as f64;
            let _ = write!(s, " ({:.0}% hit rate)", rate * 100.0);
        }
        s
    }

    /// Verify a single VC, checking the cache first.
    ///
    /// The cache key is `(formula_hash, solver_name)` where `solver_name` is
    /// determined by the router's backend selection for this VC. If the cache
    /// has a result for this key, it is returned without invoking the solver.
    pub fn verify_one(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "solver-cache", 0) {
            return result;
        }

        let (cache_keys, plan) = self.cache_keys_and_plan_for(vc);

        // Check cache.
        {
            let mut cache = self.cache.lock().expect("cache mutex poisoned");
            if let Some(cached) = cache.replay_first_result(&cache_keys) {
                return result_from_cached(cached);
            }
        }

        // Cache miss: dispatch to solver.
        let result = self.router.verify_one_with_plan(vc, &plan);

        // Store result in cache.
        if let Some(cache_key) = cache_key_for_result(&cache_keys[0].formula_hash, &result) {
            let mut cache = self.cache.lock().expect("cache mutex poisoned");
            cache.cache_result_with_certificate(
                cache_key,
                verdict_string(&result),
                model_string(&result),
                result.time_ms(),
                strength_json(&result),
                certificate_bytes(&result),
            );
        }

        result
    }

    /// Verify all VCs, checking the cache for each.
    pub fn verify_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|vc| {
                let result = self.verify_one(vc);
                (vc.clone(), result)
            })
            .collect()
    }

    /// Verify all VCs under an optional per-batch wall-clock deadline.
    ///
    /// Once `deadline` has passed, remaining obligations fail closed to
    /// `Unknown` without touching the cache or dispatching to a backend.
    pub fn verify_all_with_deadline(
        &self,
        vcs: &[VerificationCondition],
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|vc| {
                let result = if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                    budget_exceeded_unknown(vc)
                } else {
                    self.verify_one(vc)
                };
                (vc.clone(), result)
            })
            .collect()
    }

    /// Verify all VCs with bounded parallelism, checking the cache for each.
    ///
    /// Falls back to sequential for single VCs or `max_threads <= 1`.
    pub fn verify_all_parallel(
        &self,
        vcs: &[VerificationCondition],
        max_threads: usize,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.verify_all_parallel_with_deadline(vcs, max_threads, None)
    }

    /// Verify all VCs with bounded parallelism under an optional wall-clock deadline.
    ///
    /// Once `deadline` has passed, remaining cache misses fail closed to `Unknown`
    /// without dispatching new backend work. Already-started backend calls still
    /// rely on their per-VC timeout, matching `verify_all_with_deadline`.
    pub fn verify_all_parallel_with_deadline(
        &self,
        vcs: &[VerificationCondition],
        max_threads: usize,
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        if vcs.len() <= 1 || max_threads <= 1 {
            return self.verify_all_with_deadline(vcs, deadline);
        }

        // For parallel dispatch, check cache sequentially first, group unique
        // misses, dispatch one representative per miss key, then store and
        // replay fresh results into every matching placeholder.
        let mut results: Vec<(VerificationCondition, VerificationResult)> =
            Vec::with_capacity(vcs.len());
        let mut pending_misses: Vec<PendingCacheMiss> = Vec::new();
        let mut pending_miss_by_key: HashMap<Vec<ResultCacheKey>, usize> = HashMap::new();

        // Phase 1: Check cache for all VCs.
        {
            let mut cache = self.cache.lock().expect("cache mutex poisoned");
            for vc in vcs {
                if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                    results.push((vc.clone(), budget_exceeded_unknown(vc)));
                    continue;
                }
                if let Some(result) =
                    crate::backend_trait::unsupported_mir_unknown(vc, "solver-cache", 0)
                {
                    results.push((vc.clone(), result));
                    continue;
                }

                let (cache_keys, _) = self.cache_keys_and_plan_for(vc);

                if let Some(cached) = cache.replay_first_result(&cache_keys) {
                    results.push((vc.clone(), result_from_cached(cached)));
                } else {
                    let result_index = results.len();
                    results.push((
                        vc.clone(),
                        VerificationResult::Unknown {
                            solver: "pending".into(),
                            time_ms: 0,
                            reason: "cache miss, pending dispatch".to_string(),
                        },
                    ));
                    if let Some(&pending_index) = pending_miss_by_key.get(&cache_keys) {
                        pending_misses[pending_index].result_indices.push(result_index);
                    } else {
                        let pending_index = pending_misses.len();
                        pending_miss_by_key.insert(cache_keys.clone(), pending_index);
                        pending_misses.push(PendingCacheMiss {
                            cache_keys,
                            vc: vc.clone(),
                            result_indices: vec![result_index],
                        });
                    }
                }
            }
        }

        // Phase 2: Dispatch cache misses in parallel.
        if !pending_misses.is_empty() {
            if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                for pending in pending_misses {
                    for result_index in pending.result_indices {
                        let vc = results[result_index].0.clone();
                        results[result_index].1 = budget_exceeded_unknown(&vc);
                    }
                }
                return results;
            }
            let cache_miss_vcs: Vec<VerificationCondition> =
                pending_misses.iter().map(|pending| pending.vc.clone()).collect();
            let fresh_results = self.router.verify_all_parallel_with_deadline(
                &cache_miss_vcs,
                max_threads,
                deadline,
            );

            // Phase 3: Store results and fill in placeholders.
            let mut cache = self.cache.lock().expect("cache mutex poisoned");
            for (pending, (_, fresh_result)) in pending_misses.into_iter().zip(fresh_results) {
                if let Some(cache_key) =
                    cache_key_for_result(&pending.cache_keys[0].formula_hash, &fresh_result)
                {
                    cache.cache_result_with_certificate(
                        cache_key,
                        verdict_string(&fresh_result),
                        model_string(&fresh_result),
                        fresh_result.time_ms(),
                        strength_json(&fresh_result),
                        certificate_bytes(&fresh_result),
                    );
                }

                for result_index in pending.result_indices {
                    results[result_index].1 = fresh_result.clone();
                }
            }
        }

        results
    }

    fn cache_keys_and_plan_for(
        &self,
        vc: &VerificationCondition,
    ) -> (Vec<ResultCacheKey>, Vec<crate::BackendSelection>) {
        let formula_hash = vc_formula_hash(vc);
        let plan = self.router.backend_plan(vc);
        let property = crate::termination_dispatch::classify_property(vc);
        let mut keys: Vec<ResultCacheKey> = plan
            .iter()
            .filter(|entry| {
                entry.can_handle
                    && !crate::termination_dispatch::validate_dispatch(
                        property,
                        entry.name.as_str(),
                    )
                    .is_invalid()
            })
            .map(|entry| ResultCacheKey {
                formula_hash: formula_hash.clone(),
                solver_name: entry.name.to_string(),
            })
            .collect();

        if keys.is_empty() {
            keys.push(ResultCacheKey { formula_hash, solver_name: "none".to_string() });
        }

        (keys, plan)
    }
}

fn cache_key_for_result(formula_hash: &str, result: &VerificationResult) -> Option<ResultCacheKey> {
    let solver_name = result.solver_name().strip_prefix("cached:").unwrap_or(result.solver_name());
    if matches!(solver_name, "trust-budget" | "router-parallel") {
        return None;
    }
    Some(ResultCacheKey {
        formula_hash: formula_hash.to_string(),
        solver_name: solver_name.to_string(),
    })
}

fn budget_exceeded_unknown(vc: &VerificationCondition) -> VerificationResult {
    VerificationResult::Unknown {
        solver: "trust-budget".into(),
        time_ms: 0,
        reason: format!(
            "per-function wall-clock verification budget exceeded before dispatching obligation for `{}`",
            vc.function
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use trust_types::*;

    use super::*;
    use crate::VerificationBackend;
    use crate::constant_folder::ConstantFolderBackend;

    struct CountingBackend {
        can_handle_calls: Arc<AtomicUsize>,
        verify_calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for CountingBackend {
        fn name(&self) -> &str {
            "counting"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            self.can_handle_calls.fetch_add(1, Ordering::SeqCst);
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.verify_calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Proved {
                solver: "counting".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    struct StaticBackend {
        result: VerificationResult,
        verify_calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for StaticBackend {
        fn name(&self) -> &str {
            "static"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.verify_calls.fetch_add(1, Ordering::SeqCst);
            self.result.clone()
        }
    }

    struct NamedStaticBackend {
        name: &'static str,
        result: VerificationResult,
        verify_calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for NamedStaticBackend {
        fn name(&self) -> &str {
            self.name
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.verify_calls.fetch_add(1, Ordering::SeqCst);
            self.result.clone()
        }
    }

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn unsupported_mir_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "TerminatorKind::Yield".to_string(),
                detail: "valid MIR terminator preserved as opaque TrustIr".to_string(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }
    }

    // -----------------------------------------------------------------------
    // Basic cache hit/miss
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_miss_then_hit() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vc = make_vc(Formula::Bool(false));

        // First call: cache miss, dispatches to mock backend.
        let result1 = cached_router.verify_one(&vc);
        assert!(result1.is_proved());
        assert_eq!(result1.solver_name(), "constant-folder");

        // Second call: cache hit.
        let result2 = cached_router.verify_one(&vc);
        assert!(result2.is_proved());
        assert!(
            result2.solver_name().starts_with("cached:"),
            "should be served from cache, got: {}",
            result2.solver_name()
        );

        let stats = cached_router.cache_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn test_cache_replay_preserves_proof_certificate() {
        // A session-cache replay must be EVIDENCE-EQUIVALENT to the fresh
        // solve: the `-full` evidence lane is fail-closed (no retained
        // certificate bytes -> no evidence artifact), so a replay that drops
        // `proof_certificate` silently weakens the evidence DAG of every
        // deduplicated obligation. Regression for the old behavior where
        // `result_from_cached` hard-coded `proof_certificate: None`.
        let lrat: Vec<u8> = b"p lrat test certificate bytes".to_vec();
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(StaticBackend {
            result: VerificationResult::Proved {
                solver: "static".into(),
                time_ms: 3,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(lrat.clone()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vc = make_vc(Formula::Var("cert_x".into(), Sort::Bool));

        // Fresh solve carries the certificate.
        let fresh = cached_router.verify_one(&vc);
        let VerificationResult::Proved { proof_certificate: Some(fresh_cert), .. } = &fresh else {
            panic!("fresh solve must be Proved with a certificate, got {fresh:?}");
        };
        assert_eq!(fresh_cert, &lrat);

        // Replay must carry the SAME bytes, not None.
        let replayed = cached_router.verify_one(&vc);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1, "second call must replay");
        assert!(
            replayed.solver_name().starts_with("cached:"),
            "expected replay, got {}",
            replayed.solver_name()
        );
        let VerificationResult::Proved { proof_certificate, .. } = &replayed else {
            panic!("replay must be Proved, got {replayed:?}");
        };
        assert_eq!(
            proof_certificate.as_ref(),
            Some(&lrat),
            "replayed result must carry the certificate bytes captured at solve time"
        );
    }

    #[test]
    fn test_cache_replay_drops_native_proof_envelope() {
        // Blueprint S2 battery pin: the session cache does NOT persist the
        // zero-authority native proof envelope — `result_from_cached`
        // hardcodes `native_proof_envelope: None` — so a replayed row can
        // never resurrect (or forge) replay-input material that was not
        // captured at solve time. Unlike `proof_certificate` (evidence the
        // `-full` lane is fail-closed on), the envelope is pure replay input:
        // dropping it is fail-closed; persisting it would open an untracked
        // side channel through the cache.
        let envelope = NativeProofEnvelope {
            schema: NATIVE_PROOF_ENVELOPE_SCHEMA.to_string(),
            kind: NativeProofEnvelopeKind::ChcInductiveInvariant,
            claim_payload: r#"{"schema":"trustc.transport-exact-vc-claim.v2"}"#.to_string(),
            claim_digest_sha256: "ab".repeat(32),
            normalized_input_sha256: "cd".repeat(32),
            transport_identity: NativeProofTransportIdentity {
                suite: "trust-mc-native".to_string(),
                request_id: 1,
                proof_id: 1,
                native_id: "chc-row-0".to_string(),
            },
            artifacts: vec![NativeProofArtifact {
                kind: "pdr-invariant-model".to_string(),
                sha256: "ef".repeat(32),
                bytes: vec![1, 2, 3],
            }],
        };
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(StaticBackend {
            result: VerificationResult::Proved {
                solver: "static".into(),
                time_ms: 3,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: Some(envelope),
            },
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vc = make_vc(Formula::Var("envelope_x".into(), Sort::Bool));

        // Fresh solve carries the envelope.
        let fresh = cached_router.verify_one(&vc);
        let VerificationResult::Proved { native_proof_envelope: Some(_), .. } = &fresh else {
            panic!("fresh solve must be Proved with an envelope, got {fresh:?}");
        };

        // Replay must NOT carry it.
        let replayed = cached_router.verify_one(&vc);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1, "second call must replay");
        assert!(
            replayed.solver_name().starts_with("cached:"),
            "expected replay, got {}",
            replayed.solver_name()
        );
        let VerificationResult::Proved { native_proof_envelope, .. } = &replayed else {
            panic!("replay must be Proved, got {replayed:?}");
        };
        assert!(
            native_proof_envelope.is_none(),
            "cache replay must drop the native proof envelope"
        );
    }

    #[test]
    fn test_warmed_forged_proof_is_revalidated_before_replay() {
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(StaticBackend {
            result: VerificationResult::Failed {
                solver: "static".into(),
                time_ms: 1,
                counterexample: None,
            },
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let vc = make_vc(Formula::Var("x".into(), Sort::Bool));
        let key = ResultCacheKey {
            formula_hash: vc_formula_hash(&vc),
            solver_name: "static".to_string(),
        };
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        cache.warm_cache(vec![CachedResult {
            key,
            verdict: "proved".to_string(),
            model: None,
            time_ms: 0,
            cached_at: u64::MAX,
            strength_json: Some(
                serde_json::to_string(&ProofStrength::smt_unsat())
                    .expect("proof strength serializes"),
            ),
            proof_certificate: None,
        }]);
        let cached_router = SolverCachedRouter::with_cache(router, cache);

        let result = cached_router.verify_one(&vc);

        assert!(result.is_failed(), "warm cache data must not mint a proof");
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1);
        assert_eq!(cached_router.cache_stats().hits, 0);
        assert_eq!(cached_router.cache_stats().misses, 1);
    }

    #[test]
    fn test_cache_miss_reuses_routing_preflight_for_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let first = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let second = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![first, second]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let result = cached_router.verify_one(&make_vc(Formula::Bool(false)));

        assert!(result.is_proved());
        assert_eq!(
            can_handle_calls.load(Ordering::SeqCst),
            2,
            "solver-cache miss should reuse the cache-key routing plan instead of preflighting every backend twice"
        );
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_unsupported_mir_never_hits_cache_or_backend() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let result = cached_router.verify_one(&unsupported_mir_vc());

        assert!(
            matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
        );
        let stats = cached_router.cache_stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_different_formulas_miss_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vc1 = make_vc(Formula::Bool(false));
        let vc2 = make_vc(Formula::Bool(true));

        cached_router.verify_one(&vc1);
        cached_router.verify_one(&vc2);

        let stats = cached_router.cache_stats();
        assert_eq!(stats.misses, 2, "different formulas should both miss");
        assert_eq!(stats.hits, 0);
    }

    #[test]
    fn test_same_formula_hits_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vc = make_vc(Formula::Bool(false));

        cached_router.verify_one(&vc);
        cached_router.verify_one(&vc);
        cached_router.verify_one(&vc);

        let stats = cached_router.cache_stats();
        assert_eq!(stats.misses, 1, "first call misses");
        assert_eq!(stats.hits, 2, "subsequent calls hit");
    }

    // -----------------------------------------------------------------------
    // Cache policy
    // -----------------------------------------------------------------------

    #[test]
    fn test_never_cache_always_dispatches() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::NeverCache);

        let vc = make_vc(Formula::Bool(false));

        let r1 = cached_router.verify_one(&vc);
        let r2 = cached_router.verify_one(&vc);

        assert_eq!(r1.solver_name(), "constant-folder");
        assert_eq!(r2.solver_name(), "constant-folder"); // NOT cached
        assert_eq!(cached_router.cache_entry_count(), 0);
    }

    #[test]
    fn test_cache_on_success_does_not_cache_failed_or_unknown_results() {
        let failed_calls = Arc::new(AtomicUsize::new(0));
        let failed_backend = Arc::new(StaticBackend {
            result: VerificationResult::Failed {
                solver: "static".into(),
                time_ms: 1,
                counterexample: None,
            },
            verify_calls: Arc::clone(&failed_calls),
        });
        let failed_router = Router::with_arc_backends(vec![failed_backend]);
        let failed_cached_router =
            SolverCachedRouter::new(failed_router, CachePolicy::CacheOnSuccess);
        let vc = make_vc(Formula::Var("x".into(), Sort::Bool));

        failed_cached_router.verify_one(&vc);
        failed_cached_router.verify_one(&vc);

        assert_eq!(failed_calls.load(Ordering::SeqCst), 2);
        assert_eq!(failed_cached_router.cache_entry_count(), 0);

        let unknown_calls = Arc::new(AtomicUsize::new(0));
        let unknown_backend = Arc::new(StaticBackend {
            result: VerificationResult::Unknown {
                solver: "static".into(),
                time_ms: 1,
                reason: "not proved".to_string(),
            },
            verify_calls: Arc::clone(&unknown_calls),
        });
        let unknown_router = Router::with_arc_backends(vec![unknown_backend]);
        let unknown_cached_router =
            SolverCachedRouter::new(unknown_router, CachePolicy::CacheOnSuccess);

        unknown_cached_router.verify_one(&vc);
        unknown_cached_router.verify_one(&vc);

        assert_eq!(unknown_calls.load(Ordering::SeqCst), 2);
        assert_eq!(unknown_cached_router.cache_entry_count(), 0);
    }

    // -----------------------------------------------------------------------
    // verify_all
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_all_uses_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vcs = vec![make_vc(Formula::Bool(false)), make_vc(Formula::Bool(true))];

        // First pass: all miss.
        let results1 = cached_router.verify_all(&vcs);
        assert_eq!(results1.len(), 2);

        // Second pass: all hit.
        let results2 = cached_router.verify_all(&vcs);
        assert_eq!(results2.len(), 2);
        for (_, result) in &results2 {
            assert!(
                result.solver_name().starts_with("cached:"),
                "expected cached result, got: {}",
                result.solver_name()
            );
        }
    }

    #[test]
    fn test_verify_all_with_deadline_future_deadline_uses_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vc = make_vc(Formula::Bool(false));
        let deadline = std::time::Instant::now()
            .checked_add(std::time::Duration::from_secs(60))
            .expect("future deadline should be representable");

        let first =
            cached_router.verify_all_with_deadline(std::slice::from_ref(&vc), Some(deadline));
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].1.solver_name(), "constant-folder");

        let second =
            cached_router.verify_all_with_deadline(std::slice::from_ref(&vc), Some(deadline));
        assert_eq!(second.len(), 1);
        assert!(second[0].1.solver_name().starts_with("cached:"));

        let stats = cached_router.cache_stats();
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.hits, 1);
    }

    #[test]
    fn test_verify_all_with_deadline_past_deadline_does_not_cache_or_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let deadline = std::time::Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("past deadline should be representable");
        let vcs = vec![make_vc(Formula::Bool(false)), make_vc(Formula::Bool(false))];

        let results = cached_router.verify_all_with_deadline(&vcs, Some(deadline));

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|(_, result)| {
            matches!(
                result,
                VerificationResult::Unknown { solver, reason, .. }
                    if solver.as_str() == "trust-budget"
                        && reason.contains("wall-clock verification budget exceeded")
            )
        }));
        let stats = cached_router.cache_stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    // -----------------------------------------------------------------------
    // verify_all_parallel
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_all_parallel_uses_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vcs: Vec<_> = (0..4).map(|i| make_vc(Formula::Bool(i % 2 == 0))).collect();

        // First pass: 2 unique formulas = 2 misses + 2 hits (duplicates).
        let results1 = cached_router.verify_all_parallel(&vcs, 2);
        assert_eq!(results1.len(), 4);

        // Second pass: all should hit.
        let results2 = cached_router.verify_all_parallel(&vcs, 2);
        assert_eq!(results2.len(), 4);
        for (_, result) in &results2 {
            assert!(result.solver_name().starts_with("cached:"));
        }
    }

    #[test]
    fn test_verify_all_parallel_coalesces_duplicate_misses() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vcs = vec![
            make_vc(Formula::Bool(false)),
            make_vc(Formula::Bool(false)),
            make_vc(Formula::Bool(false)),
            make_vc(Formula::Bool(false)),
        ];

        let first = cached_router.verify_all_parallel(&vcs, 4);
        assert_eq!(first.len(), 4);
        assert!(first.iter().all(|(_, result)| result.is_proved()));
        assert_eq!(
            verify_calls.load(Ordering::SeqCst),
            1,
            "duplicate cache misses should dispatch one representative VC"
        );

        let second = cached_router.verify_all_parallel(&vcs, 4);
        assert_eq!(second.len(), 4);
        assert!(second.iter().all(|(_, result)| result.solver_name().starts_with("cached:")));
        assert_eq!(
            verify_calls.load(Ordering::SeqCst),
            1,
            "cached duplicates should not dispatch again"
        );
        assert_eq!(cached_router.cache_entry_count(), 1);
    }

    #[test]
    fn test_verify_one_replays_fallback_result_under_actual_solver_key() {
        let unknown_calls = Arc::new(AtomicUsize::new(0));
        let prover_calls = Arc::new(AtomicUsize::new(0));
        let unknown = Arc::new(NamedStaticBackend {
            name: "planned-unknown",
            result: VerificationResult::Unknown {
                solver: "planned-unknown".into(),
                time_ms: 1,
                reason: "try fallback".to_string(),
            },
            verify_calls: Arc::clone(&unknown_calls),
        });
        let prover = Arc::new(NamedStaticBackend {
            name: "fallback-prover",
            result: VerificationResult::Proved {
                solver: "fallback-prover".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
            verify_calls: Arc::clone(&prover_calls),
        });
        let router = Router::with_arc_backends(vec![unknown, prover]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vc = make_vc(Formula::Bool(false));

        let first = cached_router.verify_one(&vc);
        assert_eq!(first.solver_name(), "fallback-prover");

        let second = cached_router.verify_one(&vc);
        assert_eq!(second.solver_name(), "cached:fallback-prover");
        assert_eq!(unknown_calls.load(Ordering::SeqCst), 1);
        assert_eq!(prover_calls.load(Ordering::SeqCst), 1);
        assert_eq!(cached_router.cache_entry_count(), 1);
    }

    #[test]
    fn test_verify_all_parallel_reuses_fallback_result_under_actual_solver_key() {
        let unknown_calls = Arc::new(AtomicUsize::new(0));
        let prover_calls = Arc::new(AtomicUsize::new(0));
        let unknown = Arc::new(NamedStaticBackend {
            name: "planned-unknown",
            result: VerificationResult::Unknown {
                solver: "planned-unknown".into(),
                time_ms: 1,
                reason: "try fallback".to_string(),
            },
            verify_calls: Arc::clone(&unknown_calls),
        });
        let prover = Arc::new(NamedStaticBackend {
            name: "fallback-prover",
            result: VerificationResult::Proved {
                solver: "fallback-prover".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
            verify_calls: Arc::clone(&prover_calls),
        });
        let router = Router::with_arc_backends(vec![unknown, prover]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vcs = vec![make_vc(Formula::Bool(false)), make_vc(Formula::Bool(true))];

        let first = cached_router.verify_all_parallel(&vcs, 2);
        assert_eq!(first.len(), 2);
        assert!(first.iter().all(|(_, result)| result.solver_name() == "fallback-prover"));

        let second = cached_router.verify_all_parallel(&vcs, 2);
        assert_eq!(second.len(), 2);
        assert!(second.iter().all(|(_, result)| result.solver_name() == "cached:fallback-prover"));
        assert_eq!(unknown_calls.load(Ordering::SeqCst), 2);
        assert_eq!(prover_calls.load(Ordering::SeqCst), 2);
        assert_eq!(cached_router.cache_entry_count(), 2);
    }

    #[test]
    fn test_verify_all_parallel_unsupported_mir_never_hits_cache_or_backend() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vcs = vec![unsupported_mir_vc(), unsupported_mir_vc()];

        let results = cached_router.verify_all_parallel(&vcs, 2);

        assert_eq!(results.len(), 2);
        assert!(
            results
                .iter()
                .all(|(_, result)| matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR")))
        );
        let stats = cached_router.cache_stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_verify_all_parallel_with_deadline_past_does_not_cache_or_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let deadline = std::time::Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("past deadline should be representable");
        let vcs = vec![make_vc(Formula::Bool(false)), make_vc(Formula::Bool(false))];

        let results = cached_router.verify_all_parallel_with_deadline(&vcs, 2, Some(deadline));

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|(_, result)| {
            matches!(
                result,
                VerificationResult::Unknown { solver, reason, .. }
                    if solver.as_str() == "trust-budget"
                        && reason.contains("wall-clock verification budget exceeded")
            )
        }));
        let stats = cached_router.cache_stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_verify_all_parallel_with_deadline_future_uses_cache() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);
        let vcs: Vec<_> = (0..4).map(|i| make_vc(Formula::Bool(i % 2 == 0))).collect();
        let deadline = std::time::Instant::now()
            .checked_add(std::time::Duration::from_secs(60))
            .expect("future deadline should be representable");

        let first = cached_router.verify_all_parallel_with_deadline(&vcs, 2, Some(deadline));
        assert_eq!(first.len(), 4);

        let second = cached_router.verify_all_parallel_with_deadline(&vcs, 2, Some(deadline));
        assert_eq!(second.len(), 4);
        for (_, result) in &second {
            assert!(result.solver_name().starts_with("cached:"));
        }
    }

    // -----------------------------------------------------------------------
    // Summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_format() {
        let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
        let cached_router = SolverCachedRouter::new(router, CachePolicy::AlwaysCache);

        let vc = make_vc(Formula::Bool(false));
        cached_router.verify_one(&vc);
        cached_router.verify_one(&vc);

        let summary = cached_router.summary();
        assert!(summary.contains("solver-cache:"));
        assert!(summary.contains("1 entries"));
        assert!(summary.contains("1 hits"));
        assert!(summary.contains("1 misses"));
    }

    // -----------------------------------------------------------------------
    // vc_formula_hash determinism
    // -----------------------------------------------------------------------

    #[test]
    fn test_vc_formula_hash_deterministic() {
        let vc = make_vc(Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));

        let h1 = vc_formula_hash(&vc);
        let h2 = vc_formula_hash(&vc);
        assert_eq!(h1, h2, "formula hash must be deterministic");
    }

    #[test]
    fn test_vc_formula_hash_differs_for_different_formulas() {
        let vc1 = make_vc(Formula::Bool(true));
        let vc2 = make_vc(Formula::Bool(false));

        assert_ne!(
            vc_formula_hash(&vc1),
            vc_formula_hash(&vc2),
            "different formulas should have different hashes"
        );
    }

    // -----------------------------------------------------------------------
    // Free-variable alpha-normalization (audit rec 3)
    //
    // SOUNDNESS CONTRACT under test: two VCs hash EQUAL iff their formulas are
    // alpha-equivalent (identical structure up to a consistent bijective free-
    // variable rename). Over-merging non-equivalent formulas would be a FALSE
    // cached verdict, so each "differ" test below guards a distinct way the
    // canonicalizer could otherwise conflate two formulas.
    // -----------------------------------------------------------------------

    fn ivar(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    /// Reproduce exactly what [`vc_formula_hash`] hashes for a formula taken via
    /// the raw (un-canonicalized) fallback path: serde's complete structural
    /// representation, including every sort/width/format payload.
    fn raw_fallback_hash(formula: &Formula) -> String {
        hash_formula(&serde_json::to_string(formula).expect("Formula serializes"))
    }

    /// (a) Two alpha-equivalent VCs (same structure, free vars renamed by a
    /// consistent bijection — `_0`/`_1` in `f` vs `_3`/`_7` in `g`) hash EQUAL.
    #[test]
    fn test_alpha_equivalent_vcs_hash_equal() {
        // `_0 < _1`  vs  `_3 < _7`   (consistent bijection _0->_3, _1->_7)
        let f1 = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        let f2 = make_vc(Formula::Lt(Box::new(ivar("_3")), Box::new(ivar("_7"))));
        assert_eq!(
            vc_formula_hash(&f1),
            vc_formula_hash(&f2),
            "alpha-equivalent obligations must share a cache key"
        );
    }

    /// (a') Repeated-variable structure is preserved: `_0 < _0` and `_5 < _5`
    /// are alpha-equivalent, but `_0 < _0` and `_0 < _1` are NOT.
    #[test]
    fn test_alpha_repeated_var_structure_preserved() {
        let same_a = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_0"))));
        let same_b = make_vc(Formula::Lt(Box::new(ivar("_5")), Box::new(ivar("_5"))));
        assert_eq!(
            vc_formula_hash(&same_a),
            vc_formula_hash(&same_b),
            "`x < x` shapes are alpha-equivalent regardless of the local's name"
        );

        let distinct = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        assert_ne!(
            vc_formula_hash(&same_a),
            vc_formula_hash(&distinct),
            "`x < x` (1 var) must NOT collide with `x < y` (2 vars)"
        );
    }

    /// (b) Differing in a CONSTANT yields different hashes (a constant must not
    /// be ignored by normalization).
    #[test]
    fn test_differing_constant_hashes_differ() {
        let f1 = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(0))));
        let f2 = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(1))));
        assert_ne!(
            vc_formula_hash(&f1),
            vc_formula_hash(&f2),
            "formulas differing only in a constant must not share a verdict"
        );
    }

    /// (b') Differing in STRUCTURE (operator) yields different hashes.
    #[test]
    fn test_differing_structure_hashes_differ() {
        let lt = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        let gt = make_vc(Formula::Gt(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        assert_ne!(
            vc_formula_hash(&lt),
            vc_formula_hash(&gt),
            "`a < b` and `a > b` are not equivalent and must not collide"
        );
    }

    /// Swapping two free variables IS a valid alpha-renaming: `_0 < _1` and
    /// `_1 < _0` are the same obligation under the bijection {_0<->_1}, so they
    /// MUST collide. (Each VC's free vars are arbitrary/fresh; "is `a < b` valid
    /// for all a,b?" and "is `b < a` valid for all b,a?" have the same verdict.
    /// Models are dropped on replay — see `result_from_cached` — so no
    /// counterexample mismatch can leak.) This is the intended merge, not a bug.
    #[test]
    fn test_swapped_free_vars_collide_alpha_equivalent() {
        let ab = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        let ba = make_vc(Formula::Lt(Box::new(ivar("_1")), Box::new(ivar("_0"))));
        assert_eq!(
            vc_formula_hash(&ab),
            vc_formula_hash(&ba),
            "`a < b` and `b < a` over fresh free vars are alpha-equivalent obligations"
        );
    }

    /// Swapping a free var with a CONSTANT is NOT an alpha-renaming and must NOT
    /// collide: `_0 < 5` ("is x < 5 valid for all x?" — false) versus `5 < _0`
    /// ("is 5 < x valid for all x?" — also false, but a *different* obligation
    /// with a different model). A constant pins the position, so the structural
    /// asymmetry must survive normalization.
    #[test]
    fn test_var_constant_swap_hashes_differ() {
        let var_lt_const = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(5))));
        let const_lt_var = make_vc(Formula::Lt(Box::new(Formula::Int(5)), Box::new(ivar("_0"))));
        assert_ne!(
            vc_formula_hash(&var_lt_const),
            vc_formula_hash(&const_lt_var),
            "swapping a free var with a constant changes the obligation; must not collide"
        );
    }

    /// (c) A VC with two DISTINCT vars must NOT normalize to one where they are
    /// merged. `_0 + _1` (two locals) and `_0 + _0` (one local used twice) are
    /// different obligations and must hash differently.
    #[test]
    fn test_distinct_vars_not_merged() {
        let two_distinct = make_vc(Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_1"))));
        let one_repeated = make_vc(Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_0"))));
        assert_ne!(
            vc_formula_hash(&two_distinct),
            vc_formula_hash(&one_repeated),
            "two distinct free vars must never be merged into one canonical name"
        );
    }

    /// Differing SORT on an otherwise identical leaf yields different hashes,
    /// because the canonical form preserves the sort. (`to_smtlib` itself drops
    /// the sort, matching legacy behavior, but the renamed-Var sort is carried so
    /// we never *gain* a conflation relative to the raw-hash baseline.)
    #[test]
    fn test_normalization_preserves_repeated_var_count_across_sorts() {
        // Same shape, same single var, different sort widths render structurally;
        // the key property is that normalization is a no-op-shaped bijection and
        // does not collapse a 2-var formula to a 1-var one (covered above). Here we
        // assert determinism + alpha-equivalence for bitvector-sorted locals.
        let f1 = make_vc(Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("_1".into(), Sort::BitVec(32))),
        ));
        let f2 = make_vc(Formula::Eq(
            Box::new(Formula::Var("_9".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("_4".into(), Sort::BitVec(32))),
        ));
        assert_eq!(
            vc_formula_hash(&f1),
            vc_formula_hash(&f2),
            "alpha-equivalent bitvector obligations must collide"
        );
    }

    /// Quantified formulas FAIL CLOSED to the raw hash: the canonicalizer returns
    /// `None` for any `Forall`/`Exists`, so two quantified formulas that are NOT
    /// alpha-equivalent must still hash differently (no over-merge), and the hash
    /// must equal the raw SMT-LIB hash (proving the fallback path is taken).
    #[test]
    fn test_quantified_formula_falls_back_to_raw_hash() {
        let quant = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(ivar("_0")),
            )),
        );
        let vc = make_vc(quant.clone());
        // Fallback path => hash equals the raw structural hash, with no
        // free-variable canonicalization applied.
        assert_eq!(
            vc_formula_hash(&vc),
            raw_fallback_hash(&quant),
            "quantified VCs must use the raw structural fallback, not free-var rename"
        );
        assert!(
            super::alpha_canonicalize_free_vars(&quant).is_none(),
            "canonicalizer must bail (return None) on quantifiers"
        );

        // And two non-equivalent quantified formulas must not collide.
        let other = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Lt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(ivar("_0")),
            )),
        );
        assert_ne!(
            vc_formula_hash(&vc),
            vc_formula_hash(&make_vc(other)),
            "distinct quantified formulas must not share a verdict via fallback"
        );
    }

    /// A formula already using the reserved canonical prefix FAILS CLOSED to the
    /// raw hash, so a pre-existing `__trust_fvK` can never alias a generated name
    /// and merge two distinct variables.
    #[test]
    fn test_reserved_prefix_name_falls_back_to_raw_hash() {
        let collides = Formula::Lt(
            Box::new(Formula::Var(format!("{FV_CANON_PREFIX}0"), Sort::Int)),
            Box::new(ivar("_1")),
        );
        assert!(
            super::alpha_canonicalize_free_vars(&collides).is_none(),
            "canonicalizer must bail when a reserved-prefix name is already present"
        );
        let vc = make_vc(collides.clone());
        assert_eq!(
            vc_formula_hash(&vc),
            raw_fallback_hash(&collides),
            "reserved-prefix VCs must use the raw structural fallback"
        );
    }

    /// `SymVar` and `Var` referring to the same variable in alpha-equivalent
    /// positions collide (the canonicalizer normalizes both leaf kinds).
    #[test]
    fn test_symvar_and_var_same_position_collide() {
        let with_var = make_vc(Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(5))));
        let with_symvar = make_vc(Formula::Lt(
            Box::new(Formula::SymVar(trust_types::Symbol::intern("_0"), Sort::Int)),
            Box::new(Formula::Int(5)),
        ));
        assert_eq!(
            vc_formula_hash(&with_var),
            vc_formula_hash(&with_symvar),
            "Var and SymVar of the same local in the same position must collide"
        );
    }

    /// Uninterpreted predicate ARGUMENTS are canonicalized, but the predicate
    /// NAME is preserved. Two applications of the *same* predicate to alpha-
    /// equivalent argument lists collide; applications of *different* predicates
    /// never collide (renaming a predicate symbol would conflate distinct
    /// uninterpreted functions — unsound).
    #[test]
    fn test_pred_args_canonicalized_name_preserved() {
        let p_a = make_vc(Formula::Pred(trust_types::Symbol::intern("dir_open"), vec![ivar("_0")]));
        let p_b = make_vc(Formula::Pred(trust_types::Symbol::intern("dir_open"), vec![ivar("_9")]));
        assert_eq!(
            vc_formula_hash(&p_a),
            vc_formula_hash(&p_b),
            "same predicate over alpha-equivalent args must collide"
        );

        let q = make_vc(Formula::Pred(trust_types::Symbol::intern("file_open"), vec![ivar("_0")]));
        assert_ne!(
            vc_formula_hash(&p_a),
            vc_formula_hash(&q),
            "different predicate symbols must never collide"
        );
    }

    #[test]
    fn test_structural_hash_covers_new_term_family_payloads() {
        let fp32 = make_vc(Formula::FpNaN { eb: 8, sb: 24 });
        let fp64 = make_vc(Formula::FpNaN { eb: 11, sb: 53 });
        assert_ne!(
            vc_formula_hash(&fp32),
            vc_formula_hash(&fp64),
            "floating-point format payload is part of cache identity"
        );

        let int_app = make_vc(Formula::FnApp {
            func: "model".to_string(),
            args: vec![ivar("_0")],
            sort: Sort::Int,
        });
        let bool_app = make_vc(Formula::FnApp {
            func: "model".to_string(),
            args: vec![ivar("_0")],
            sort: Sort::Bool,
        });
        assert_ne!(
            vc_formula_hash(&int_app),
            vc_formula_hash(&bool_app),
            "uninterpreted function result sort is part of cache identity"
        );
    }

    // -----------------------------------------------------------------------
    // Regression: the cache key MUST preserve every structural AST payload.
    //
    // `Formula::to_smtlib` renders a `Var` as its bare symbol (no sort) and a
    // width-bearing bitvector operator with no width, so two NON-equivalent
    // formulas that differ ONLY in a leaf sort or an operator width render to the
    // same text. Before the fix the cache key was that text plus a manually
    // maintained partial signature, so new term families could silently omit
    // identity-bearing payload. These tests pin exact derived serialization while
    // still colliding genuinely alpha-equivalent VCs.
    // -----------------------------------------------------------------------

    /// `distinct(a,b,c)` (encoded as pairwise `a≠b ∧ a≠c ∧ b≠c`) is UNSAT over a
    /// `BitVec(1)` domain (pigeonhole: three values, two slots) → the obligation is
    /// PROVED, but the same structure over `Int` is SAT → the obligation FAILS.
    /// The two formulas have IDENTICAL SMT-LIB text (only the leaf sorts differ),
    /// so the key must fold the sort in or it would replay the UNSAT verdict onto
    /// the SAT obligation. The two VCs must therefore hash DIFFERENTLY.
    #[test]
    fn test_distinct3_bitvec1_vs_int_do_not_collide() {
        fn distinct3(sort: Sort) -> VerificationCondition {
            let a = || Formula::Var("_0".into(), sort.clone());
            let b = || Formula::Var("_1".into(), sort.clone());
            let c = || Formula::Var("_2".into(), sort.clone());
            make_vc(Formula::And(vec![
                Formula::Not(Box::new(Formula::Eq(Box::new(a()), Box::new(b())))),
                Formula::Not(Box::new(Formula::Eq(Box::new(a()), Box::new(c())))),
                Formula::Not(Box::new(Formula::Eq(Box::new(b()), Box::new(c())))),
            ]))
        }
        let over_bv1 = distinct3(Sort::BitVec(1));
        let over_int = distinct3(Sort::Int);

        // Sanity: the bare SMT-LIB text really is identical (the hole being closed).
        assert_eq!(
            over_bv1.formula.to_smtlib(),
            over_int.formula.to_smtlib(),
            "precondition of this test: to_smtlib drops the sort, so the text matches"
        );
        assert_ne!(
            vc_formula_hash(&over_bv1),
            vc_formula_hash(&over_int),
            "distinct-3 over BitVec(1) (UNSAT→Proved) must NOT share a cache key with \
             distinct-3 over Int (SAT→Failed); the dropped sort would be a false proof"
        );
    }

    /// A `bvadd` at width 8 and at width 16 render to identical SMT-LIB text but
    /// wrap at different moduli, so they can decide differently. The cache key must
    /// fold the operator width in. (Same hole, BV-operator flavor.)
    #[test]
    fn test_bvadd_width8_vs_width16_do_not_collide() {
        fn bvadd_vc(width: u32) -> VerificationCondition {
            let x = Formula::Var("_0".into(), Sort::BitVec(width));
            let y = Formula::Var("_1".into(), Sort::BitVec(width));
            make_vc(Formula::BvAdd(Box::new(x), Box::new(y), width))
        }
        let w8 = bvadd_vc(8);
        let w16 = bvadd_vc(16);
        assert_ne!(
            vc_formula_hash(&w8),
            vc_formula_hash(&w16),
            "bvadd at width 8 and width 16 wrap differently and must NOT share a cache key"
        );
    }

    /// The fix must NOT regress the intended merge: two genuinely alpha-equivalent
    /// VCs (same structure, same sorts and widths, free vars renamed by a
    /// consistent bijection) must still hash EQUAL so they share a verdict.
    #[test]
    fn test_alpha_equivalent_vcs_still_collide_after_sort_width_fold() {
        // `bvadd(_0, _1) : BitVec(8)`  vs  `bvadd(_4, _9) : BitVec(8)`.
        let f1 = make_vc(Formula::BvAdd(
            Box::new(Formula::Var("_0".into(), Sort::BitVec(8))),
            Box::new(Formula::Var("_1".into(), Sort::BitVec(8))),
            8,
        ));
        let f2 = make_vc(Formula::BvAdd(
            Box::new(Formula::Var("_4".into(), Sort::BitVec(8))),
            Box::new(Formula::Var("_9".into(), Sort::BitVec(8))),
            8,
        ));
        assert_eq!(
            vc_formula_hash(&f1),
            vc_formula_hash(&f2),
            "alpha-equivalent obligations (same sorts and widths) must still collide"
        );
    }

    /// The transform is idempotent: structurally hashing an already-canonical
    /// formula equals hashing its canonicalization.
    #[test]
    fn test_alpha_normalization_idempotent() {
        let f = Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let canon = super::alpha_canonicalize_free_vars(&f).expect("quantifier-free");
        let canon2 = super::alpha_canonicalize_free_vars(&canon);
        // Second pass bails (reserved prefix now present) -> raw hash of canon.
        // Either way the canonical structural hash must be stable.
        let serialize = |formula: &Formula| {
            hash_formula(&serde_json::to_string(formula).expect("Formula serializes"))
        };
        let h_once = serialize(&canon);
        let h_twice = canon2.as_ref().map_or_else(|| serialize(&canon), serialize);
        assert_eq!(h_once, h_twice, "canonical structural hash must be idempotent");
    }

    // -----------------------------------------------------------------------
    // Adversarial re-audit: every payload channel dropped by `to_smtlib` must
    // still split the derived structural cache identity.
    // -----------------------------------------------------------------------

    /// `to_smtlib` renders a `Var`/`SymVar` as the bare symbol for EVERY sort, so
    /// the *same-named, same-structure* leaf under two different sorts collapses to
    /// identical text. The fix must split each pair. We exercise every `Sort`
    /// constructor (`Bool`/`Int`/`BitVec(w)`/`Float{eb,sb}`/`Array`/`RoundingMode`)
    /// so no sort flavor silently shares a verdict with another.
    #[test]
    fn test_every_leaf_sort_splits_cache_key() {
        let sorts = [
            Sort::Bool,
            Sort::Int,
            Sort::BitVec(1),
            Sort::BitVec(8),
            Sort::BitVec(32),
            Sort::Float { eb: 8, sb: 24 },  // f32
            Sort::Float { eb: 11, sb: 53 }, // f64
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
            Sort::RoundingMode,
        ];
        // A bare `_0` leaf under each sort. `to_smtlib` is identical text ("_0")
        // for all of them; only the folded sort can keep the keys apart.
        let hashes: Vec<String> = sorts
            .iter()
            .map(|s| vc_formula_hash(&make_vc(Formula::Var("_0".into(), s.clone()))))
            .collect();
        // Confirm the precondition: bare SMT text really is identical for all.
        for s in &sorts {
            assert_eq!(
                Formula::Var("_0".into(), s.clone()).to_smtlib(),
                "_0",
                "precondition: to_smtlib drops the sort of a Var leaf"
            );
        }
        for i in 0..hashes.len() {
            for j in (i + 1)..hashes.len() {
                assert_ne!(
                    hashes[i], hashes[j],
                    "leaf sort {:?} and {:?} render identically but are NOT equivalent; \
                     their cache keys must differ",
                    sorts[i], sorts[j]
                );
            }
        }
    }

    /// `BvToInt(inner, width, signed)` drops the width from `to_smtlib` in the
    /// UNSIGNED case (`(bv2nat …)` with no width token), and the signed/unsigned
    /// flag changes the value (`bv2nat` vs the two's-complement-correcting `ite`).
    /// All three of (unsigned w8), (unsigned w16), (signed w8) are non-equivalent
    /// and must hash distinctly.
    #[test]
    fn test_bvtoint_width_and_signedness_split_cache_key() {
        fn b2i(width: u32, signed: bool) -> VerificationCondition {
            let inner = Box::new(Formula::Var("_0".into(), Sort::BitVec(width)));
            // Wrap in Eq so the top-level formula is a Bool predicate (a realistic VC).
            make_vc(Formula::Eq(
                Box::new(Formula::BvToInt(inner, width, signed)),
                Box::new(Formula::Int(0)),
            ))
        }
        let u8_ = vc_formula_hash(&b2i(8, false));
        let u16_ = vc_formula_hash(&b2i(16, false));
        let s8_ = vc_formula_hash(&b2i(8, true));
        assert_ne!(u8_, u16_, "unsigned bv2nat at width 8 vs 16 must not collide");
        assert_ne!(u8_, s8_, "unsigned vs signed BvToInt at width 8 must not collide");
        assert_ne!(u16_, s8_, "distinct width+signedness must not collide");
    }

    /// `BvExtract { high, low }` picks a different bit slice for different bounds;
    /// `to_smtlib` does render `((_ extract high low) …)` so the text already
    /// differs, but the signature must AGREE (not regress the merge) for identical
    /// slices and DIFFER for distinct slices. We assert the distinct-slice split.
    #[test]
    fn test_bvextract_slice_bounds_split_cache_key() {
        fn ext(high: u32, low: u32) -> VerificationCondition {
            let inner = Box::new(Formula::Var("_0".into(), Sort::BitVec(32)));
            make_vc(Formula::Eq(
                Box::new(Formula::BvExtract { inner, high, low }),
                Box::new(Formula::Var("_1".into(), Sort::BitVec(high - low + 1))),
            ))
        }
        assert_ne!(
            vc_formula_hash(&ext(7, 0)),
            vc_formula_hash(&ext(15, 8)),
            "extract[7:0] and extract[15:8] are different obligations"
        );
    }

    /// `BvZeroExt(_, bits)` and `BvSignExt(_, bits)` extend by `bits`; a zero- vs
    /// sign-extension of the same vector decide differently for negative values,
    /// and a different `bits` changes the result width. Both axes must split.
    #[test]
    fn test_bv_extend_kind_and_amount_split_cache_key() {
        let inner = || Box::new(Formula::Var("_0".into(), Sort::BitVec(8)));
        let zext8 = make_vc(Formula::BvZeroExt(inner(), 8));
        let zext16 = make_vc(Formula::BvZeroExt(inner(), 16));
        let sext8 = make_vc(Formula::BvSignExt(inner(), 8));
        assert_ne!(
            vc_formula_hash(&zext8),
            vc_formula_hash(&zext16),
            "zero_extend by 8 vs 16 must not collide"
        );
        // zero_extend and sign_extend DO render differently in to_smtlib, but the
        // signature folds zext[..]/sext[..] so the keys are doubly distinct; assert
        // they stay apart (no accidental signature aliasing across the two tokens).
        assert_ne!(
            vc_formula_hash(&zext8),
            vc_formula_hash(&sext8),
            "zero_extend vs sign_extend by the same amount must not collide"
        );
    }

    /// A nested width difference DEEP inside an otherwise-identical structure must
    /// still split the key: the signature is a full pre-order walk, not just a
    /// top-level peek. `(and (= (bvadd _0 _1) _2) true)` at width 8 vs 16.
    #[test]
    fn test_nested_bv_width_difference_splits_cache_key() {
        fn nested(width: u32) -> VerificationCondition {
            let bvadd = Formula::BvAdd(
                Box::new(Formula::Var("_0".into(), Sort::BitVec(width))),
                Box::new(Formula::Var("_1".into(), Sort::BitVec(width))),
                width,
            );
            make_vc(Formula::And(vec![
                Formula::Eq(
                    Box::new(bvadd),
                    Box::new(Formula::Var("_2".into(), Sort::BitVec(width))),
                ),
                Formula::Bool(true),
            ]))
        }
        assert_ne!(
            vc_formula_hash(&nested(8)),
            vc_formula_hash(&nested(16)),
            "a width difference nested inside the formula must still split the key"
        );
    }

    /// The sort fold must not INTRODUCE a new conflation: a leaf whose source name
    /// already contains the `__<sort>` shape (`_0__Int`) must still get a fresh,
    /// position-derived canonical name and stay distinct from a genuinely different
    /// formula. Two distinct source vars never merge regardless of name spelling.
    #[test]
    fn test_sort_fold_does_not_merge_distinct_vars_with_suggestive_names() {
        // `_0__Int < _1`  vs  `_0__Int < _0__Int` : two vars vs one repeated.
        let two = make_vc(Formula::Lt(
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
            Box::new(Formula::Var("_1".into(), Sort::Int)),
        ));
        let one = make_vc(Formula::Lt(
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
        ));
        assert_ne!(
            vc_formula_hash(&two),
            vc_formula_hash(&one),
            "a source name that mimics the canonical `name__sort` shape must not \
             cause two distinct vars to merge onto one canonical leaf"
        );
    }

    /// Cross-check: alpha-equivalent formulas over a NON-integer leaf sort still
    /// collide after the fold (hit-rate preserved for float-sorted obligations).
    #[test]
    fn test_alpha_equivalent_float_sorted_vcs_still_collide() {
        let f32_ = Sort::Float { eb: 8, sb: 24 };
        let a = make_vc(Formula::FpEq(
            Box::new(Formula::Var("_0".into(), f32_.clone())),
            Box::new(Formula::Var("_1".into(), f32_.clone())),
        ));
        let b = make_vc(Formula::FpEq(
            Box::new(Formula::Var("_7".into(), f32_.clone())),
            Box::new(Formula::Var("_3".into(), f32_.clone())),
        ));
        assert_eq!(
            vc_formula_hash(&a),
            vc_formula_hash(&b),
            "alpha-equivalent float-sorted obligations must still share a verdict"
        );
    }
}
