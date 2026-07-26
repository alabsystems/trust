// trust-cache/sub_query_splitter.rs: KLEE-style sub-query splitting with caching
//
// Combines constraint independence partitioning with hash-based query caching.
// Given a verification condition, the splitter:
// 1. Partitions the formula into independent sub-queries (no shared variables).
// 2. Checks each sub-query against the cache.
// 3. Returns cached results for hits, and uncached sub-queries for solving.
// 4. After solving, stores results back into the cache.
//
// Inspired by KLEE's IndependentSolver + CachingSolver pipeline
// (refs/klee/lib/Solver/IndependentSolver.cpp,
//  refs/klee/lib/Solver/CachingSolver.cpp).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use sha2::{Digest, Sha256};
use trust_types::{Formula, Symbol, VerificationCondition, VerificationResult};

use crate::independence::{ConstraintIndependence, free_variables, partition_constraints};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the sub-query splitter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitterConfig {
    /// Maximum number of entries in the sub-query cache before LRU eviction.
    pub max_cache_entries: usize,
    /// Minimum number of conjuncts required before attempting to split.
    /// Formulas with fewer conjuncts are not worth splitting.
    pub min_conjuncts_to_split: usize,
    /// Whether to project away irrelevant constraints when caching sub-queries.
    pub enable_projection: bool,
}

impl Default for SplitterConfig {
    fn default() -> Self {
        Self { max_cache_entries: 10_000, min_conjuncts_to_split: 2, enable_projection: true }
    }
}

// ---------------------------------------------------------------------------
// Split result
// ---------------------------------------------------------------------------

/// A sub-query produced by independence splitting.
#[derive(Debug, Clone)]
pub struct SubQuery {
    /// The formula for this independent sub-query.
    pub formula: Formula,
    /// The cache key (SHA-256 hash) for this sub-query.
    pub cache_key: String,
    /// The free variables in this sub-query.
    pub variables: FxHashSet<String>,
    /// Index of this sub-query in the original split (for reassembly).
    pub partition_index: usize,
}

/// Result of splitting a query into independent sub-queries.
#[derive(Debug, Clone)]
pub struct SplitResult {
    /// Sub-queries that were found in the cache (already solved).
    pub cached: Vec<CachedSubQuery>,
    /// Sub-queries that need to be solved.
    pub uncached: Vec<SubQuery>,
    /// Total number of partitions the formula was split into.
    pub total_partitions: usize,
    /// The original function name (for result reassembly).
    pub function: String,
    /// The original VC kind (for result reassembly).
    pub original_vc_kind: trust_types::VcKind,
}

/// A sub-query whose result was found in the cache.
#[derive(Debug, Clone)]
pub struct CachedSubQuery {
    /// The formula that was cached.
    pub formula: Formula,
    /// The cached result.
    pub result: VerificationResult,
    /// Index of this sub-query in the original split.
    pub partition_index: usize,
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Statistics about sub-query splitting and caching.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct SplitterStats {
    /// Total queries processed by the splitter.
    pub queries_processed: usize,
    /// Queries that were actually split (had >1 partition).
    pub queries_split: usize,
    /// Total sub-queries produced across all splits.
    pub total_sub_queries: usize,
    /// Sub-queries satisfied from the cache.
    pub cache_hits: usize,
    /// Sub-queries that required solver invocation.
    pub cache_misses: usize,
    /// Number of cache evictions (LRU).
    pub evictions: usize,
    /// Number of entries currently in the sub-query cache.
    pub cache_entries: usize,
    /// Total solver calls saved (same as cache_hits).
    pub solver_calls_saved: usize,
    /// Average number of partitions per split query.
    pub avg_partitions: f64,
}

impl SplitterStats {
    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        // Statistics sum feeding a diagnostic rate: saturating_add is exact
        // for every reachable counter pair and, at the (unreachable-in-
        // practice) usize::MAX boundary, only clamps a number that is about
        // to be rounded through f64 anyway. Not checked_add: a diagnostic
        // must never become a fallible operation or an abort.
        let total = self.cache_hits.saturating_add(self.cache_misses);
        if total == 0 { 0.0 } else { self.cache_hits as f64 / total as f64 }
    }

    /// Split rate: fraction of queries that were actually split.
    #[must_use]
    pub fn split_rate(&self) -> f64 {
        if self.queries_processed == 0 {
            0.0
        } else {
            self.queries_split as f64 / self.queries_processed as f64
        }
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "processed={}, split={}, sub_queries={}, cache_hits={}, cache_misses={}, \
             evictions={}, hit_rate={:.1}%, split_rate={:.1}%",
            self.queries_processed,
            self.queries_split,
            self.total_sub_queries,
            self.cache_hits,
            self.cache_misses,
            self.evictions,
            self.hit_rate() * 100.0,
            self.split_rate() * 100.0,
        )
    }
}

// ---------------------------------------------------------------------------
// SubQuerySplitter
// ---------------------------------------------------------------------------

/// KLEE-style sub-query splitter with integrated caching.
///
/// Combines constraint independence partitioning (`ConstraintIndependence`)
/// with hash-based query caching (`QueryCache`) to avoid redundant solver
/// calls on independent sub-formulas.
///
/// Usage:
/// ```text
/// let mut splitter = SubQuerySplitter::new(SplitterConfig::default());
///
/// // Split a VC into independent sub-queries, checking cache
/// let split = splitter.split(&vc);
///
/// // Solve uncached sub-queries
/// for sub_query in &split.uncached {
///     let result = solver.check(&sub_query.formula);
///     splitter.store_result(&sub_query.cache_key, result);
/// }
///
/// // Combine all results
/// let combined = splitter.combine_results(&split);
/// ```
pub struct SubQuerySplitter {
    /// Configuration.
    config: SplitterConfig,
    /// Sub-query result cache: maps formula hash -> solver result.
    cache: FxHashMap<String, VerificationResult>,
    /// LRU ordering: maps formula hash -> access counter.
    access_order: FxHashMap<String, u64>,
    /// Monotonically increasing access counter.
    access_counter: u64,
    /// Accumulated statistics.
    stats: SplitterStats,
}

impl SubQuerySplitter {
    /// Create a new splitter with the given configuration.
    #[must_use]
    pub fn new(config: SplitterConfig) -> Self {
        Self {
            config,
            cache: FxHashMap::default(),
            access_order: FxHashMap::default(),
            access_counter: 0,
            stats: SplitterStats::default(),
        }
    }

    /// Split a verification condition into independent sub-queries.
    ///
    /// Partitions the VC's formula by constraint independence, checks
    /// each partition against the cache, and returns the split result
    /// with cached and uncached sub-queries separated.
    pub fn split(&mut self, vc: &VerificationCondition) -> SplitResult {
        self.stats.queries_processed += 1;

        let partitions = partition_constraints(&vc.formula);
        let num_partitions = partitions.len();

        // Track whether this query was actually split
        if num_partitions > 1 {
            self.stats.queries_split += 1;
        }

        // Update average partitions
        self.stats.total_sub_queries += num_partitions;
        if self.stats.queries_split > 0 {
            self.stats.avg_partitions =
                self.stats.total_sub_queries as f64 / self.stats.queries_processed as f64;
        }

        let mut cached = Vec::new();
        let mut uncached = Vec::new();

        for (idx, partition) in partitions.into_iter().enumerate() {
            let key = sub_query_hash(&partition, vc.function.as_str());
            let variables = free_variables(&partition);

            if let Some(result) = self.cache_lookup(&key) {
                cached.push(CachedSubQuery {
                    formula: partition,
                    result: result.clone(),
                    partition_index: idx,
                });
                self.stats.cache_hits += 1;
                self.stats.solver_calls_saved += 1;
            } else {
                uncached.push(SubQuery {
                    formula: partition,
                    cache_key: key,
                    variables,
                    partition_index: idx,
                });
                self.stats.cache_misses += 1;
            }
        }

        SplitResult {
            cached,
            uncached,
            total_partitions: num_partitions,
            function: vc.function.as_str().to_string(),
            original_vc_kind: vc.kind.clone(),
        }
    }

    /// Store a solver result for a sub-query in the cache.
    ///
    /// Performs LRU eviction if the cache exceeds `max_cache_entries`.
    pub fn store_result(&mut self, cache_key: &str, result: VerificationResult) {
        // Evict if at capacity
        if self.cache.len() >= self.config.max_cache_entries && !self.cache.contains_key(cache_key)
        {
            self.evict_lru();
        }

        let order = self.bump_access_counter();
        self.cache.insert(cache_key.to_string(), result);
        self.access_order.insert(cache_key.to_string(), order);
        self.stats.cache_entries = self.cache.len();
    }

    /// Combine results from cached and freshly-solved sub-queries.
    ///
    /// The combined result follows these conservative rules:
    /// - If ALL sub-queries are Proved, the combined result is Proved.
    /// - Every other complete result set is Unknown.
    ///
    /// In particular, partition SAT/`Failed` results are never composed into a
    /// global `Failed`. The current dependency analysis does not track every
    /// semantic symbol (for example uninterpreted predicate identities), so
    /// separately satisfiable partitions are not yet proof that the original
    /// conjunction is satisfiable.
    #[must_use]
    pub fn combine_results(
        &self,
        split: &SplitResult,
        solved_results: &FxHashMap<String, VerificationResult>,
    ) -> Option<VerificationResult> {
        let mut all_proved = true;
        let mut total_time_ms: u64 = 0;
        let mut solver_name: Symbol = "split-cache".into();
        let mut weakest_strength = None;

        // Check cached results
        for cached in &split.cached {
            match &cached.result {
                VerificationResult::Proved { time_ms, solver, strength, .. } => {
                    total_time_ms += time_ms;
                    solver_name = *solver;
                    retain_weaker_strength(&mut weakest_strength, strength);
                }
                VerificationResult::Failed { .. } => {
                    all_proved = false;
                }
                VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                    all_proved = false;
                }
                _ => {
                    all_proved = false;
                }
            }
        }

        // Check solved results
        for sub_query in &split.uncached {
            if let Some(result) = solved_results.get(&sub_query.cache_key) {
                match result {
                    VerificationResult::Proved { time_ms, solver, strength, .. } => {
                        total_time_ms += time_ms;
                        solver_name = *solver;
                        retain_weaker_strength(&mut weakest_strength, strength);
                    }
                    VerificationResult::Failed { .. } => {
                        all_proved = false;
                    }
                    VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                        all_proved = false;
                    }
                    _ => {
                        all_proved = false;
                    }
                }
            } else {
                // Sub-query not yet solved
                return None;
            }
        }

        if all_proved {
            let Some(strength) = weakest_strength else {
                return None;
            };
            Some(VerificationResult::Proved {
                solver: solver_name,
                time_ms: total_time_ms,
                // Composition may never upgrade a component. In particular an
                // Unchecked or bounded `Proved` remains Unchecked/bounded and is
                // rejected by publication gates instead of being relabeled Sound.
                strength,
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            })
        } else {
            Some(VerificationResult::Unknown {
                solver: solver_name,
                time_ms: total_time_ms,
                reason: "some sub-queries could not be proved".to_string(),
            })
        }
    }

    /// Get current splitter statistics.
    #[must_use]
    pub fn stats(&self) -> &SplitterStats {
        &self.stats
    }

    /// Number of entries in the sub-query cache.
    #[must_use]
    pub fn cache_len(&self) -> usize {
        self.cache.len()
    }

    /// Whether the sub-query cache is empty.
    #[must_use]
    pub fn cache_is_empty(&self) -> bool {
        self.cache.is_empty()
    }

    /// Clear the sub-query cache and reset statistics.
    pub fn clear(&mut self) {
        self.cache.clear();
        self.access_order.clear();
        self.access_counter = 0;
        self.stats = SplitterStats::default();
    }

    /// Advance the LRU logical clock and return the new tick.
    ///
    /// Fail closed on clock exhaustion: a wrapped clock would give the
    /// newest access the SMALLEST tick, inverting LRU so the hottest entry
    /// becomes the next eviction victim; a saturated clock would silently
    /// collapse all later accesses into one tie, degrading LRU to arbitrary
    /// eviction. Neither is unsound (eviction only discards cached results,
    /// keyed lookups stay correct), but both silently corrupt the eviction
    /// policy. Exhaustion is unreachable in practice — the clock advances at
    /// most once per cache access, and 2^64 accesses cannot occur in one
    /// process lifetime — so this abort documents the invariant rather than
    /// guarding a reachable path.
    fn bump_access_counter(&mut self) -> u64 {
        self.access_counter = self
            .access_counter
            .checked_add(1)
            .expect("sub-query cache LRU access counter exhausted");
        self.access_counter
    }

    /// Look up a sub-query result in the cache and update LRU order.
    fn cache_lookup(&mut self, key: &str) -> Option<&VerificationResult> {
        if self.cache.contains_key(key) {
            let order = self.bump_access_counter();
            self.access_order.insert(key.to_string(), order);
            self.cache.get(key)
        } else {
            None
        }
    }

    /// Evict the least-recently-used entry from the cache.
    fn evict_lru(&mut self) {
        if let Some(lru_key) =
            self.access_order.iter().min_by_key(|(_, order)| **order).map(|(k, _)| k.clone())
        {
            self.cache.remove(&lru_key);
            self.access_order.remove(&lru_key);
            // Pure statistic: saturating_add is exact for every reachable
            // count and at the usize::MAX bound degrades only the diagnostic,
            // never the eviction itself. Not checked_add: a stats increment
            // must not become a fallible operation.
            self.stats.evictions = self.stats.evictions.saturating_add(1);
        }
        self.stats.cache_entries = self.cache.len();
    }
}

/// Retain a component proof strength that is no stronger than any strength
/// observed so far. `AssuranceLevel::strength_order` is the legacy ordering;
/// bounded evidence wins ties because bounded coverage must never be erased by
/// a same-rung unbounded label.
fn retain_weaker_strength(
    weakest: &mut Option<trust_types::ProofStrength>,
    candidate: &trust_types::ProofStrength,
) {
    let replace = weakest.as_ref().is_none_or(|current| {
        candidate.assurance.strength_order() < current.assurance.strength_order()
            || (candidate.assurance.strength_order() == current.assurance.strength_order()
                && candidate.is_bounded()
                && !current.is_bounded())
    });
    if replace {
        *weakest = Some(candidate.clone());
    }
}

impl Default for SubQuerySplitter {
    fn default() -> Self {
        Self::new(SplitterConfig::default())
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Compute a SHA-256 hash for a sub-query formula, incorporating the function name.
///
/// Uses alpha-normalized hashing via the cache's alpha_normalize module
/// so that structurally equivalent sub-queries with renamed bound variables
/// produce the same key.
#[must_use]
pub fn sub_query_hash(formula: &Formula, function: &str) -> String {
    let normalized = crate::alpha_normalize::alpha_normalize(formula);
    let formula_json = serde_json::to_vec(&normalized).expect(
        "Formula is the canonical serializable Trust IR; refusing to reuse \
         a sub-query after serialization failure",
    );
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cache/subquery/v2\0");
    hasher.update((function.len() as u64).to_be_bytes());
    hasher.update(function.as_bytes());
    hasher.update((formula_json.len() as u64).to_be_bytes());
    hasher.update(&formula_json);
    format!("{:x}", hasher.finalize())
}

/// Analyze a formula and return independence metadata without splitting.
///
/// Useful for diagnostics: reports how many independent partitions exist,
/// what variables are in each, and whether splitting would be beneficial.
#[must_use]
pub fn analyze_independence(formula: &Formula) -> IndependenceAnalysis {
    let ci = ConstraintIndependence::new(formula);
    let partition_count = ci.partition_count();
    let partition_vars = ci.partition_variables();
    let all_vars = ci.all_variables();

    IndependenceAnalysis {
        total_variables: all_vars.len(),
        partition_count,
        partition_sizes: partition_vars.iter().map(|v| v.len()).collect(),
        would_benefit: partition_count > 1,
    }
}

/// Result of analyzing a formula's constraint independence structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndependenceAnalysis {
    /// Total number of free variables across all partitions.
    pub total_variables: usize,
    /// Number of independent partitions.
    pub partition_count: usize,
    /// Number of variables in each partition.
    pub partition_sizes: Vec<usize>,
    /// Whether splitting would reduce solver work (more than 1 partition).
    pub would_benefit: bool,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{AssuranceLevel, ProofStrength, Sort, SourceSpan, VcKind};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn make_vc(name: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: name.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn proved_result_with_time(ms: u64) -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: ms,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn proved_with_strength(strength: ProofStrength) -> VerificationResult {
        VerificationResult::Proved {
            solver: "component".into(),
            time_ms: 1,
            strength,
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn cached_split(results: Vec<VerificationResult>) -> SplitResult {
        SplitResult {
            cached: results
                .into_iter()
                .enumerate()
                .map(|(partition_index, result)| CachedSubQuery {
                    formula: Formula::Bool(true),
                    result,
                    partition_index,
                })
                .collect(),
            uncached: Vec::new(),
            total_partitions: 2,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 5, counterexample: None }
    }

    fn unknown_result() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 100,
            reason: "timeout".to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // SubQuerySplitter basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_splitter_new_empty() {
        let splitter = SubQuerySplitter::new(SplitterConfig::default());
        assert!(splitter.cache_is_empty());
        assert_eq!(splitter.cache_len(), 0);
        assert_eq!(splitter.stats().queries_processed, 0);
    }

    #[test]
    fn test_splitter_default() {
        let splitter = SubQuerySplitter::default();
        assert_eq!(splitter.config.max_cache_entries, 10_000);
        assert_eq!(splitter.config.min_conjuncts_to_split, 2);
        assert!(splitter.config.enable_projection);
    }

    // -----------------------------------------------------------------------
    // Split tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_single_formula_no_splitting() {
        let mut splitter = SubQuerySplitter::default();
        let vc = make_vc("foo", Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));

        let result = splitter.split(&vc);
        assert_eq!(result.total_partitions, 1);
        assert_eq!(result.uncached.len(), 1);
        assert!(result.cached.is_empty());
        assert_eq!(splitter.stats().queries_processed, 1);
        assert_eq!(splitter.stats().queries_split, 0);
    }

    #[test]
    fn test_split_independent_conjuncts() {
        let mut splitter = SubQuerySplitter::default();
        // x == 0 AND y > 1 — no shared variables, should split into 2
        let vc = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
        );

        let result = splitter.split(&vc);
        assert_eq!(result.total_partitions, 2);
        assert_eq!(result.uncached.len(), 2);
        assert!(result.cached.is_empty());
        assert_eq!(splitter.stats().queries_split, 1);
    }

    #[test]
    fn test_split_dependent_conjuncts_no_splitting() {
        let mut splitter = SubQuerySplitter::default();
        // x == 0 AND x > 1 — shared variable x, should NOT split
        let vc = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(1))),
            ]),
        );

        let result = splitter.split(&vc);
        assert_eq!(result.total_partitions, 1);
        assert_eq!(result.uncached.len(), 1);
        assert_eq!(splitter.stats().queries_split, 0);
    }

    #[test]
    fn test_split_three_independent_groups() {
        let mut splitter = SubQuerySplitter::default();
        // x==0, y>1, z<2 — three independent groups
        let vc = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
                Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(2))),
            ]),
        );

        let result = splitter.split(&vc);
        assert_eq!(result.total_partitions, 3);
        assert_eq!(result.uncached.len(), 3);
        assert_eq!(splitter.stats().total_sub_queries, 3);
    }

    #[test]
    fn test_split_mixed_dependent_and_independent() {
        let mut splitter = SubQuerySplitter::default();
        // x==y (dependent), z>0 (independent) => 2 partitions
        let vc = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
                Formula::Gt(Box::new(var("z")), Box::new(Formula::Int(0))),
            ]),
        );

        let result = splitter.split(&vc);
        assert_eq!(result.total_partitions, 2);
        assert_eq!(result.uncached.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Cache integration tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_cache_hit_on_second_query() {
        let mut splitter = SubQuerySplitter::default();

        // First query: x==0 AND y>1
        let vc1 = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
        );
        let split1 = splitter.split(&vc1);
        assert_eq!(split1.uncached.len(), 2);
        assert_eq!(split1.cached.len(), 0);

        // Store results for each sub-query
        for sq in &split1.uncached {
            splitter.store_result(&sq.cache_key, proved_result());
        }

        // Second query: same formula — should be fully cached
        let split2 = splitter.split(&vc1);
        assert_eq!(split2.cached.len(), 2);
        assert_eq!(split2.uncached.len(), 0);
        assert_eq!(splitter.stats().cache_hits, 2);
    }

    #[test]
    fn test_split_partial_cache_hit() {
        let mut splitter = SubQuerySplitter::default();

        // First query: x==0 AND y>1
        let vc1 = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
        );
        let split1 = splitter.split(&vc1);

        // Only store the first sub-query result
        splitter.store_result(&split1.uncached[0].cache_key, proved_result());

        // New query with one overlapping sub-query and one new one:
        // x==0 AND z<5
        let vc2 = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(5))),
            ]),
        );
        let split2 = splitter.split(&vc2);

        // One sub-query (x==0) should be cached, one (z<5) should not
        assert_eq!(split2.cached.len(), 1);
        assert_eq!(split2.uncached.len(), 1);
    }

    #[test]
    fn test_store_and_retrieve_result() {
        let mut splitter = SubQuerySplitter::default();
        let vc = make_vc("foo", Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42))));

        // Split and store
        let split = splitter.split(&vc);
        assert_eq!(split.uncached.len(), 1);
        splitter.store_result(&split.uncached[0].cache_key, proved_result());

        // Second split should cache-hit
        let split2 = splitter.split(&vc);
        assert_eq!(split2.cached.len(), 1);
        assert!(split2.cached[0].result.is_proved());
    }

    // -----------------------------------------------------------------------
    // LRU eviction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lru_eviction() {
        let mut splitter =
            SubQuerySplitter::new(SplitterConfig { max_cache_entries: 2, ..Default::default() });

        // Insert 3 entries — should evict the first
        splitter.store_result("key_a", proved_result());
        splitter.store_result("key_b", proved_result());
        assert_eq!(splitter.cache_len(), 2);

        splitter.store_result("key_c", proved_result());
        assert_eq!(splitter.cache_len(), 2);
        assert_eq!(splitter.stats().evictions, 1);
    }

    #[test]
    fn test_lru_access_refreshes_order() {
        let mut splitter =
            SubQuerySplitter::new(SplitterConfig { max_cache_entries: 2, ..Default::default() });

        splitter.store_result("key_a", proved_result());
        splitter.store_result("key_b", proved_result());

        // Access key_a to refresh it (simulate via split that hits key_a)
        // We'll manually look up to refresh
        assert!(splitter.cache_lookup("key_a").is_some());

        // Now insert key_c — key_b should be evicted (LRU), not key_a
        splitter.store_result("key_c", proved_result());
        assert_eq!(splitter.cache_len(), 2);
        assert!(splitter.cache_lookup("key_a").is_some());
        assert!(splitter.cache_lookup("key_c").is_some());
    }

    #[test]
    fn test_lru_eviction_stats() {
        let mut splitter =
            SubQuerySplitter::new(SplitterConfig { max_cache_entries: 3, ..Default::default() });

        for i in 0..5 {
            splitter.store_result(&format!("key_{i}"), proved_result());
        }

        // 5 inserts into a capacity-3 cache => 2 evictions
        assert_eq!(splitter.stats().evictions, 2);
        assert_eq!(splitter.cache_len(), 3);
    }

    // -----------------------------------------------------------------------
    // Overflow-boundary tests (hardened_panic_boundary sites)
    // -----------------------------------------------------------------------

    #[test]
    fn test_hit_rate_saturates_instead_of_overflowing() {
        // hits + misses at the usize boundary must not wrap (a wrapped total
        // of 0 would report a 0.0 hit rate for a saturated cache).
        let stats = SplitterStats { cache_hits: usize::MAX, cache_misses: 1, ..Default::default() };
        let rate = stats.hit_rate();
        assert!(rate.is_finite());
        assert!((rate - 1.0).abs() < 1e-9, "MAX/(MAX sat) must be ~1.0, got {rate}");

        // Exactness away from the boundary is unchanged.
        let stats = SplitterStats { cache_hits: 3, cache_misses: 1, ..Default::default() };
        assert!((stats.hit_rate() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    #[should_panic(expected = "LRU access counter exhausted")]
    fn test_lru_clock_exhaustion_fails_closed() {
        // A wrapped LRU clock would order the newest access as the oldest
        // (inverted eviction); a saturated one would collapse all later
        // accesses into a tie. The fail-closed path must abort instead.
        let mut splitter =
            SubQuerySplitter { access_counter: u64::MAX, ..SubQuerySplitter::default() };
        splitter.store_result("key_a", proved_result());
    }

    #[test]
    fn test_lru_clock_last_valid_tick_still_orders() {
        // The final representable tick must still be usable: the increment to
        // u64::MAX succeeds and the access-order entry records it.
        let mut splitter =
            SubQuerySplitter { access_counter: u64::MAX - 1, ..SubQuerySplitter::default() };
        splitter.store_result("key_a", proved_result());
        assert_eq!(splitter.access_counter, u64::MAX);
        assert_eq!(splitter.access_order.get("key_a"), Some(&u64::MAX));
        // Inspect without cache_lookup: any FURTHER access would (correctly)
        // abort, since u64::MAX was the last representable tick.
        assert!(splitter.cache.contains_key("key_a"));
    }

    #[test]
    fn test_evictions_stat_saturates_and_eviction_still_happens() {
        // At the statistic's boundary the count clamps, but the eviction
        // itself (the semantics-bearing part) must still occur.
        let mut splitter =
            SubQuerySplitter::new(SplitterConfig { max_cache_entries: 1, ..Default::default() });
        splitter.stats.evictions = usize::MAX;
        splitter.store_result("key_a", proved_result());
        splitter.store_result("key_b", proved_result());

        assert_eq!(splitter.stats().evictions, usize::MAX, "stat clamps, no wrap to 0");
        assert_eq!(splitter.cache_len(), 1, "eviction still enforced capacity");
        assert!(splitter.cache_lookup("key_b").is_some(), "newest entry survives");
        assert!(splitter.cache_lookup("key_a").is_none(), "LRU entry was evicted");
    }

    // -----------------------------------------------------------------------
    // Combine results tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_combine_all_proved() {
        let splitter = SubQuerySplitter::default();
        let split = SplitResult {
            cached: vec![CachedSubQuery {
                formula: Formula::Bool(true),
                result: proved_result_with_time(5),
                partition_index: 0,
            }],
            uncached: vec![SubQuery {
                formula: Formula::Bool(true),
                cache_key: "k1".to_string(),
                variables: FxHashSet::default(),
                partition_index: 1,
            }],
            total_partitions: 2,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        };

        let mut solved = FxHashMap::default();
        solved.insert("k1".to_string(), proved_result_with_time(15));

        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_some());
        let result = combined.unwrap();
        assert!(result.is_proved());
        assert_eq!(result.time_ms(), 20); // 5 + 15
    }

    #[test]
    fn combine_never_upgrades_unchecked_component_to_sound() {
        let splitter = SubQuerySplitter::default();
        let split = cached_split(vec![
            proved_with_strength(ProofStrength::smt_unsat()),
            proved_with_strength(ProofStrength::smt_unsat_unvalidated()),
        ]);

        let result = splitter
            .combine_results(&split, &FxHashMap::default())
            .expect("all component results present");
        assert_eq!(result.assurance(), Some(AssuranceLevel::Unchecked));
    }

    #[test]
    fn combine_never_erases_bounded_component() {
        let splitter = SubQuerySplitter::default();
        for strengths in [
            vec![ProofStrength::smt_unsat(), ProofStrength::bounded(7)],
            vec![ProofStrength::bounded(7), ProofStrength::smt_unsat()],
        ] {
            let split = cached_split(strengths.into_iter().map(proved_with_strength).collect());
            let result = splitter
                .combine_results(&split, &FxHashMap::default())
                .expect("all component results present");
            let VerificationResult::Proved { strength, .. } = result else {
                panic!("all-proved composition must remain a Proved result");
            };
            assert_eq!(strength, ProofStrength::bounded(7));
        }
    }

    #[test]
    fn combine_uses_weakest_unbounded_assurance() {
        let splitter = SubQuerySplitter::default();
        let split = cached_split(vec![
            proved_with_strength(ProofStrength::smt_unsat_certified()),
            proved_with_strength(ProofStrength::smt_unsat_strict_checked()),
        ]);
        let result = splitter
            .combine_results(&split, &FxHashMap::default())
            .expect("all component results present");
        assert_eq!(result.assurance(), Some(AssuranceLevel::SmtBacked));
    }

    #[test]
    fn test_combine_mixed_proved_and_failed_is_unknown() {
        let splitter = SubQuerySplitter::default();
        let split = SplitResult {
            cached: vec![CachedSubQuery {
                formula: Formula::Bool(true),
                result: proved_result(),
                partition_index: 0,
            }],
            uncached: vec![SubQuery {
                formula: Formula::Bool(true),
                cache_key: "k1".to_string(),
                variables: FxHashSet::default(),
                partition_index: 1,
            }],
            total_partitions: 2,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        };

        let mut solved = FxHashMap::default();
        solved.insert("k1".to_string(), failed_result());

        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_some());
        assert!(matches!(combined.unwrap(), VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_combine_one_unknown() {
        let splitter = SubQuerySplitter::default();
        let split = SplitResult {
            cached: vec![CachedSubQuery {
                formula: Formula::Bool(true),
                result: proved_result(),
                partition_index: 0,
            }],
            uncached: vec![SubQuery {
                formula: Formula::Bool(true),
                cache_key: "k1".to_string(),
                variables: FxHashSet::default(),
                partition_index: 1,
            }],
            total_partitions: 2,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        };

        let mut solved = FxHashMap::default();
        solved.insert("k1".to_string(), unknown_result());

        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_some());
        let result = combined.unwrap();
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("could not be proved"));
            }
            other => panic!("expected Unknown, got {other:?}"),
        }
    }

    #[test]
    fn test_combine_missing_result_returns_none() {
        let splitter = SubQuerySplitter::default();
        let split = SplitResult {
            cached: vec![],
            uncached: vec![SubQuery {
                formula: Formula::Bool(true),
                cache_key: "k1".to_string(),
                variables: FxHashSet::default(),
                partition_index: 0,
            }],
            total_partitions: 1,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        };

        // No solved results provided
        let solved = FxHashMap::default();
        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_none(), "should return None when not all sub-queries are solved");
    }

    #[test]
    fn test_combine_cached_failure_does_not_hide_missing_partition() {
        let splitter = SubQuerySplitter::default();
        let split = SplitResult {
            cached: vec![CachedSubQuery {
                formula: Formula::Bool(true),
                result: failed_result(),
                partition_index: 0,
            }],
            uncached: vec![SubQuery {
                formula: Formula::Bool(true),
                cache_key: "k1".to_string(),
                variables: FxHashSet::default(),
                partition_index: 1,
            }],
            total_partitions: 2,
            function: "foo".into(),
            original_vc_kind: VcKind::DivisionByZero,
        };

        // SAT for one conjunct does not decide the whole conjunction while a
        // different independent conjunct is unsolved (it may be UNSAT).
        let solved = FxHashMap::default();
        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_none());
    }

    #[test]
    fn contradictory_predicate_partitions_cannot_synthesize_failed() {
        let splitter = SubQuerySplitter::default();
        // Each partition is satisfiable alone, but their conjunction is not.
        // Predicate identity is semantic shared state that the current free-
        // variable partitioner does not track.
        let p_zero = Formula::Pred("P".into(), vec![Formula::Int(0)]);
        let split = SplitResult {
            cached: vec![
                CachedSubQuery {
                    formula: p_zero.clone(),
                    result: failed_result(),
                    partition_index: 0,
                },
                CachedSubQuery {
                    formula: Formula::Not(Box::new(p_zero)),
                    result: failed_result(),
                    partition_index: 1,
                },
            ],
            uncached: Vec::new(),
            total_partitions: 2,
            function: "forged_predicate_split".into(),
            original_vc_kind: VcKind::Assertion { message: "P(0) and not P(0)".into() },
        };
        let combined = splitter.combine_results(&split, &FxHashMap::default());
        assert!(matches!(combined, Some(VerificationResult::Unknown { .. })));
    }

    // -----------------------------------------------------------------------
    // Statistics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_default() {
        let stats = SplitterStats::default();
        assert_eq!(stats.queries_processed, 0);
        assert_eq!(stats.hit_rate(), 0.0);
        assert_eq!(stats.split_rate(), 0.0);
    }

    #[test]
    fn test_stats_hit_rate() {
        let stats = SplitterStats { cache_hits: 3, cache_misses: 1, ..Default::default() };
        assert!((stats.hit_rate() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_split_rate() {
        let stats = SplitterStats { queries_processed: 10, queries_split: 4, ..Default::default() };
        assert!((stats.split_rate() - 0.4).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_summary_format() {
        let stats = SplitterStats {
            queries_processed: 5,
            queries_split: 2,
            total_sub_queries: 8,
            cache_hits: 3,
            cache_misses: 5,
            evictions: 1,
            cache_entries: 4,
            solver_calls_saved: 3,
            avg_partitions: 1.6,
        };
        let summary = stats.summary();
        assert!(summary.contains("processed=5"));
        assert!(summary.contains("split=2"));
        assert!(summary.contains("cache_hits=3"));
        assert!(summary.contains("evictions=1"));
    }

    // -----------------------------------------------------------------------
    // Clear tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_splitter_clear() {
        let mut splitter = SubQuerySplitter::default();
        splitter.store_result("key_a", proved_result());
        splitter.store_result("key_b", proved_result());

        let vc = make_vc("foo", Formula::Bool(true));
        splitter.split(&vc);

        assert_eq!(splitter.cache_len(), 2);
        assert!(splitter.stats().queries_processed > 0);

        splitter.clear();

        assert!(splitter.cache_is_empty());
        assert_eq!(splitter.stats().queries_processed, 0);
        assert_eq!(splitter.stats().cache_hits, 0);
        assert_eq!(splitter.stats().cache_misses, 0);
    }

    // -----------------------------------------------------------------------
    // sub_query_hash tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sub_query_hash_deterministic() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let h1 = sub_query_hash(&f, "foo");
        let h2 = sub_query_hash(&f, "foo");
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64); // SHA-256 hex
    }

    #[test]
    fn test_sub_query_hash_different_function() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let h1 = sub_query_hash(&f, "foo");
        let h2 = sub_query_hash(&f, "bar");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_sub_query_hash_different_formula() {
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1)));
        let h1 = sub_query_hash(&f1, "foo");
        let h2 = sub_query_hash(&f2, "foo");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_sub_query_hash_alpha_equivalent() {
        // Alpha-equivalent quantified formulas should produce the same hash
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(
            sub_query_hash(&f1, "foo"),
            sub_query_hash(&f2, "foo"),
            "alpha-equivalent formulas should have same sub-query hash"
        );
    }

    // -----------------------------------------------------------------------
    // analyze_independence tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_analyze_independence_single() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let analysis = analyze_independence(&f);
        assert_eq!(analysis.partition_count, 1);
        assert!(!analysis.would_benefit);
    }

    #[test]
    fn test_analyze_independence_two_groups() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let analysis = analyze_independence(&f);
        assert_eq!(analysis.partition_count, 2);
        assert_eq!(analysis.total_variables, 2);
        assert!(analysis.would_benefit);
        assert_eq!(analysis.partition_sizes.len(), 2);
    }

    #[test]
    fn test_analyze_independence_transitive() {
        // x==y AND y==z => one partition with 3 variables
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
            Formula::Eq(Box::new(var("y")), Box::new(var("z"))),
        ]);
        let analysis = analyze_independence(&f);
        assert_eq!(analysis.partition_count, 1);
        assert_eq!(analysis.total_variables, 3);
        assert!(!analysis.would_benefit);
    }

    // -----------------------------------------------------------------------
    // End-to-end integration test
    // -----------------------------------------------------------------------

    #[test]
    fn test_end_to_end_split_solve_combine() {
        let mut splitter = SubQuerySplitter::default();

        // Create a VC with two independent parts: x==0 AND y>1
        let vc = make_vc(
            "test_fn",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
        );

        // Step 1: Split
        let split = splitter.split(&vc);
        assert_eq!(split.total_partitions, 2);
        assert_eq!(split.uncached.len(), 2);

        // Step 2: "Solve" each uncached sub-query
        let mut solved = FxHashMap::default();
        for sq in &split.uncached {
            let result = proved_result_with_time(5);
            solved.insert(sq.cache_key.clone(), result.clone());
            splitter.store_result(&sq.cache_key, result);
        }

        // Step 3: Combine
        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_some());
        assert!(combined.unwrap().is_proved());

        // Step 4: Verify cache works on re-query
        let split2 = splitter.split(&vc);
        assert_eq!(split2.cached.len(), 2);
        assert_eq!(split2.uncached.len(), 0);
        assert_eq!(splitter.stats().cache_hits, 2);
        assert_eq!(splitter.stats().solver_calls_saved, 2);
    }

    #[test]
    fn test_end_to_end_with_mixed_results_is_unknown() {
        let mut splitter = SubQuerySplitter::default();

        let vc = make_vc(
            "test_fn",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
        );

        let split = splitter.split(&vc);

        // First sub-query proves, second fails
        let mut solved = FxHashMap::default();
        solved.insert(split.uncached[0].cache_key.clone(), proved_result_with_time(5));
        solved.insert(split.uncached[1].cache_key.clone(), failed_result());

        let combined = splitter.combine_results(&split, &solved);
        assert!(combined.is_some());
        assert!(matches!(combined.unwrap(), VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_config_custom() {
        let config = SplitterConfig {
            max_cache_entries: 100,
            min_conjuncts_to_split: 3,
            enable_projection: false,
        };
        let splitter = SubQuerySplitter::new(config.clone());
        assert_eq!(splitter.config.max_cache_entries, 100);
        assert_eq!(splitter.config.min_conjuncts_to_split, 3);
        assert!(!splitter.config.enable_projection);
    }

    // -----------------------------------------------------------------------
    // Sub-query variable tracking
    // -----------------------------------------------------------------------

    #[test]
    fn test_sub_query_variables_tracked() {
        let mut splitter = SubQuerySplitter::default();

        let vc = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(var("y")), Box::new(var("z"))),
            ]),
        );

        let split = splitter.split(&vc);
        assert_eq!(split.uncached.len(), 2);

        // One sub-query should have {x}, the other {y, z}
        let var_counts: Vec<usize> = split.uncached.iter().map(|sq| sq.variables.len()).collect();
        assert!(var_counts.contains(&1));
        assert!(var_counts.contains(&2));
    }

    #[test]
    fn test_split_preserves_function_name() {
        let mut splitter = SubQuerySplitter::default();
        let vc = make_vc("my_function", Formula::Bool(true));
        let split = splitter.split(&vc);
        assert_eq!(split.function, "my_function");
    }

    #[test]
    fn test_split_preserves_vc_kind() {
        let mut splitter = SubQuerySplitter::default();
        let vc = make_vc("foo", Formula::Bool(true));
        let split = splitter.split(&vc);
        assert!(
            matches!(split.original_vc_kind, VcKind::DivisionByZero),
            "expected DivisionByZero, got {:?}",
            split.original_vc_kind,
        );
    }
}
