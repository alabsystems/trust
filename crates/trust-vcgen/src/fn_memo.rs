//! Per-function ANALYSIS memo — whole-body analyses computed once per function
//! per VC-generation scope, instead of once per query from inside the walk.
//!
//! # Why this exists (verifier-perf / L0 termination, 2026-09-10)
//!
//! The 2026-09 verifier-on census of `library/core` reported twenty bodies whose
//! VC GENERATION alone exceeded the 5 s per-function budget (`trust_verify.rs`
//! "possible verifier non-termination"): `fmt::num::<impl u32>::_fmt_inner`,
//! `num::imp::int_sqrt::u64_stages`, `slice::ascii::is_ascii`, `escape_ascii`,
//! the grisu/dragon formatters, … None of them is large — `_fmt_inner<u32>` is
//! 68 blocks / 161 statements / 176 locals as the compiler extracts it — and
//! none has an exponential path shape. Reproduced outside the compiler (the
//! bodies transcribed verbatim into `tests/ui/trust/vcgen_budget_census_bodies.rs`,
//! dumped with `-Ztrust-dump=mir:` — the same trustc reports the census error
//! for them at `-Ztrust-verify-function-budget-ms=1000` — then run through
//! `generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`)
//! and sampled, the time was NOT in any one loop; it was in the SAME handful of
//! whole-body analyses being re-derived from scratch inside every inner loop of
//! the obligation walk:
//!
//! * `place_to_var_name` (82 % of samples, inclusive): every call rebuilt an
//!   `FxHashSet` of all local indices, ran `canonicalize_place` (whose
//!   `resolve_referent` → `local_defs::body_unique_value_def` scans the WHOLE
//!   body, fuel 16),
//!   and scanned every local again for a source-name collision — O(locals + body)
//!   per call. It is the vocabulary mint, so it sits under EVERYTHING:
//!   `normalize_ssa_version_tokens` called it `locals × versioned-vars` times per
//!   formula (a linear `find` over `0..locals.len()` minting each whole-local
//!   name), `stmt_writes_name` once per (statement, name) probe, and the havoc
//!   lists once per local per Call terminator.
//! * `StmtVersionCtx::build` → `block_entry_versions` (34 %): the inter-block
//!   reaching-version fixpoint was rebuilt for EVERY obligation — once in
//!   `conjoin_preconditions_versioned_recorded`, once in
//!   `v2_formula_with_block_defs_at_point_recorded`, and again in every lane that
//!   builds its own — and each build re-derived `mutable_pointer_local_names` /
//!   `mutably_borrowed_local_names` (both whole-body walks over
//!   `place_to_var_name`) for every Call block and every gen'd name.
//! * `version_token_at` → `writes_until` (18 %): every `Var` renamed by
//!   `version_rename_at` re-extracted the block's statement prefix to formulas
//!   (`extract_block_definitions_until`, itself re-running the whole-function
//!   `v2_array_version_prepass`) to learn which names the prefix writes.
//!
//! Multiplied out that is roughly O(VCs × blocks × locals × (locals + body)) per
//! function — a fixed-degree polynomial, not non-termination, but degree ~4-5 in
//! the body size, which is exactly what turns a 68-block body into tens of
//! seconds. Measured on the compiler's own dumps in the debug test build
//! (`tests/vcgen_budget_realmir.rs`, fixtures `census_budget_*.json`), before →
//! after this module:
//!
//! | body              | wall     | `place_to_var_name` | `block_entry_versions` | `v2_array_version_prepass` | `writes_until` |
//! |-------------------|----------|---------------------|------------------------|----------------------------|----------------|
//! | `fmt_inner_u32`   | 36.8 s → 0.67 s | 976 786 → 255 | 90 → 1  | 28 425 → 1 | 20 263 → 220 |
//! | `u64_stages`      | 38.6 s → 0.70 s | 1 142 489 → 185 | 109 → 1 | 29 965 → 1 | 21 172 → 192 |
//! | `is_ascii`        | 1.05 s → 0.10 s | 48 465 → 70   | 22 → 1  | 5 121 → 1  | 2 545 → 76   |
//!
//! with the `(solver_vcs, discharged)` result identical in every case (the
//! parity tests there compare them field-for-field).
//!
//! # What it does
//!
//! Each analysis below is a PURE, DETERMINISTIC function of the immutable
//! `VerifiableFunction` body (locals + blocks) and its arguments. This memo
//! computes each of them at most once per (function, argument) inside a VC-gen
//! scope and replays the byte-identical value on every later query. Nothing
//! about WHAT is computed changes — every caller still receives exactly the value
//! the uncached computation returns — so every emitted obligation is unchanged.
//! `tests/vcgen_budget_realmir.rs::memo_is_verdict_identical_on_*`
//! pins that by running the census bodies with the memo disabled
//! ([`with_analysis_memo_disabled`]) and comparing the full `(solver_vcs,
//! discharged)` result byte-for-byte.
//!
//! # Division of labour with `place_memo` / `havoc_memo` (merge, 2026-09-10)
//!
//! `origin/main` reached the SAME diagnosis independently and landed its own
//! caches for four of the analyses above: `place_memo`'s name cache
//! (`place_to_var_name`), and `havoc_memo`'s `version_oracle`
//! (`StmtVersionCtx::build` — which subsumes `block_entry_versions` and ALSO
//! caches the unwind-inclusive `block_entry_versions_full_graph` this module
//! never saw), `writes_until`, and `opaque_pointer`
//! (`deref_pointer_is_opaque`). Those four are theirs; the wrappers that used
//! to live here were retired at the merge rather than stacked on top, because
//! two caches of one pure function is only a second thing to keep coherent.
//! What remains here is what neither of those covers:
//! `v2_array_version_prepass`, `local_versions_collapse_to_bare`, the
//! whole-local base→index table, and the two havoc name lists INDIVIDUALLY
//! (`havoc_memo::havoc_list` caches only their concatenation, which the other
//! callers of each list cannot use).
//!
//! The measurement surface ([`AnalysisMemoStats`]) still reports all of them:
//! the four that moved are counted at their UNCACHED computation site
//! (`count_place_name` and friends), so the census budget regression test pins
//! the same work bound regardless of which module owns the cache.
//!
//! # Scope and identity (the same discipline as `place_memo`)
//!
//! * The memo is INERT outside a `gen_work` scope (every public VC-gen entry
//!   opens one: the metered generations `gen_work::enter`, the row replays the
//!   unmetered scope, and the entries with no meter of their own, the call-site
//!   producers among them, `generate::EntryScope`); an out-of-scope call computes
//!   exactly as before.
//! * It is cleared on every OUTERMOST scope entry and exit (`gen_work::enter`
//!   and `Guard::drop`), so nothing survives from one function's generation into
//!   the next, and nothing lingers while no generation runs.
//! * Entries are bound to a function IDENTITY — the function's address, the
//!   address + length of its `locals` and `blocks` buffers, and its
//!   `name`/`def_path` (owned integers and strings only; no stale pointer is ever
//!   dereferenced). A query for a function with a different identity MISSES and
//!   rebinds. Inside one scope the views a lane derives
//!   (`with_tail_calls_expanded`, `without_unmodeled_contract_arithmetic`) are
//!   either `Cow::Borrowed` (same identity, same body) or a fresh clone held
//!   alive for the whole lane (new buffers ⇒ new identity); tail-call expansion
//!   also changes `blocks.len()`. A stale HIT would therefore need an in-scope
//!   allocator reuse of all three addresses by a DIFFERENT body of identical
//!   shape, and no production path in this crate mutates a body in place (the
//!   `stmts.insert` / `blocks.push` sites are all under `#[cfg(test)]`, and none
//!   runs inside a scope: every scope is opened by a function that holds the body
//!   borrowed for the scope's whole extent). Every cached value depends on the
//!   body only — never on contracts, preconditions, or context — so a
//!   precondition-only derived view sharing a body is served correctly either way.
//!
//!   The identity check is O(1) on purpose: it runs on EVERY lookup, and the
//!   whole-body statement count it once also compared made each lookup
//!   O(blocks) — `local_is_index_operand`, asked once per statement by the write
//!   index and the gen-set walks, turned that into O(statements × blocks) per
//!   function. `place_memo` and `havoc_memo` (which holds the version oracle
//!   itself) bind on the same pointer-and-length identity.
//!
//! # Soundness
//!
//! Memoization of a deterministic function is verdict-identical by construction;
//! there is no fail-closed direction to argue because no value is approximated,
//! dropped, or widened. The one thing to keep true when ADDING an entry here:
//! the cached function must read nothing but `func.body` and its own arguments.
//! An analysis that consults contracts, the ambient `VcgenContext`, summaries, or
//! any other thread-local MUST NOT be routed through this memo.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use trust_types::VerifiableFunction;
use trust_types::fx::FxHashMap;

use super::ArrayVersionCtx;

/// Identity of the function the memo is bound to. See the module docs.
struct Identity {
    func_ptr: usize,
    locals_ptr: usize,
    locals_len: usize,
    blocks_ptr: usize,
    blocks_len: usize,
    name: String,
    def_path: String,
}

impl Identity {
    /// Snapshot `func`'s identity — taken ONLY when (re)binding, so the two
    /// `String` clones are paid once per function, not once per query.
    fn of(func: &VerifiableFunction) -> Identity {
        Identity {
            func_ptr: std::ptr::from_ref(func) as usize,
            locals_ptr: func.body.locals.as_ptr() as usize,
            locals_len: func.body.locals.len(),
            blocks_ptr: func.body.blocks.as_ptr() as usize,
            blocks_len: func.body.blocks.len(),
            name: func.name.clone(),
            def_path: func.def_path.clone(),
        }
    }

    /// Does the bound identity name `func`? Compared by reference — a query is
    /// answered on every place-name mint, so this must allocate nothing — and in
    /// O(1) time (no walk of the body; see the module docs).
    fn matches(&self, func: &VerifiableFunction) -> bool {
        count(|s| s.memo_identity_checks += 1);
        self.func_ptr == std::ptr::from_ref(func) as usize
            && self.locals_ptr == func.body.locals.as_ptr() as usize
            && self.locals_len == func.body.locals.len()
            && self.blocks_ptr == func.body.blocks.as_ptr() as usize
            && self.blocks_len == func.body.blocks.len()
            && self.name == func.name
            && self.def_path == func.def_path
    }
}

/// The memoized tables. Every field is a pure function of `func.body` (+ the
/// key), computed lazily on first query. `Rc` so a hit hands back a shared
/// handle instead of deep-copying a map.
#[derive(Default)]
struct Tables {
    /// Whole-local name → the FIRST local index `l` in `0..locals.len()` that
    /// mints it (the `(0..len).find(..)` the SSA collapse used to run per var).
    whole_local_index_by_base: Option<Rc<FxHashMap<String, usize>>>,
    mut_pointer_names: Option<Rc<Vec<String>>>,
    mut_borrowed_names: Option<Rc<Vec<String>>>,
    /// `generate::path_defs::noalias_mut_params` (D15's disjoint `&mut` arguments).
    noalias_mut_params: Option<Rc<Vec<usize>>>,
    /// `generate::path_defs::escape_havoc_at`'s per-parameter escape reach.
    param_escape_reach: Option<Rc<crate::generate::ParamEscapeReach>>,
    /// `generate::path_defs::escape_havoc_at`'s split, per exempt-parameter set (sorted
    /// locals), so every call with one set shares one payload.
    escape_havoc_exempting: FxHashMap<Vec<usize>, Rc<crate::generate::EscapeHavoc>>,
    collapse_to_bare: FxHashMap<usize, bool>,
    array_prepass: Option<Rc<ArrayVersionCtx>>,
    /// Per-local flag: does the local occur as a `Projection::Index(l)` operand
    /// anywhere in the body (`generate::path_defs::local_is_index_operand`)?
    index_locals: Option<Rc<Vec<bool>>>,
    /// `generate::discriminant_cse_anchor_map`'s tie map.
    discriminant_cse_anchors: Option<Rc<FxHashMap<String, String>>>,
    /// `generate::path_defs::func_has_pointer_laundering`.
    pointer_laundering: Option<bool>,
    /// `generate::path_defs::func_has_writable_pointer_laundering`.
    writable_pointer_laundering: Option<bool>,
    /// `generate::call_facts::body_mentions_opaque_scalar`.
    body_mentions_opaque_scalar: Option<bool>,
    /// `generate::path_defs::stored_ref_pointee_names`.
    stored_ref_pointee_names: Option<Rc<Vec<String>>>,
    /// `generate::path_defs::shared_borrowed_cell_places`, for every local at once.
    shared_cell_borrows: Option<Rc<FxHashMap<usize, Rc<Vec<trust_types::Place>>>>>,
    /// `generate::path_defs::laundered_alias_roots`.
    laundered_alias_roots: Option<Rc<Vec<String>>>,
    /// `lib::symbolic_assignment_sorts`: every place a symbolic assignment sorts.
    symbolic_sorts: Option<Rc<FxHashMap<trust_types::Place, Option<trust_types::Sort>>>>,
    /// `lib::array_theory_local`, per local.
    array_models: FxHashMap<usize, Option<super::ArrayModel>>,
    /// `generate::type_ranges::checked_arith_result_value_vars`.
    checked_arith_result_vars: Option<Rc<trust_types::fx::FxHashSet<String>>>,
    /// `generate::alloc_vcs::conjoin_arg_type_ranges_step` parameter range summary.
    arg_type_ranges: Option<Rc<ArgTypeRangeSummary>>,
    /// `generate::type_ranges::local_scalar_range_map`.
    local_scalar_ranges: Option<Rc<FxHashMap<String, crate::range::RustScalarRange>>>,
    /// `generate::type_ranges::local_value_join_interval_map`.
    local_value_join_intervals: Option<Rc<FxHashMap<String, (Option<i128>, Option<i128>)>>>,
    /// `generate::type_ranges::datatype_field_range_map`.
    datatype_field_ranges: Option<Rc<FxHashMap<String, crate::range::RustScalarRange>>>,
    /// `generate::type_ranges::length_nonneg_base_names`.
    length_nonneg_bases: Option<Rc<trust_types::fx::FxHashSet<String>>>,
    /// `generate::type_ranges::coll_len_bound_vars`.
    coll_len_bound_vars:
        Option<Rc<(trust_types::fx::FxHashSet<String>, trust_types::fx::FxHashSet<String>)>>,
    /// `generate::type_ranges::nonzst_slice_len_vars`.
    nonzst_slice_len_vars: Option<Rc<trust_types::fx::FxHashSet<String>>>,
    /// `guards::local_is_mutably_borrowed`, per local.
    local_is_mutably_borrowed: FxHashMap<usize, bool>,
    /// `guards::local_mut_borrows_may_resize`, per local.
    local_mut_borrows_may_resize: FxHashMap<usize, bool>,
    /// `guards::base_collection_local_unique`, per local.
    base_collection_local: FxHashMap<usize, Option<usize>>,
    /// `guards::base_collection_place_unique`, per local.
    base_collection_place: FxHashMap<usize, Option<trust_types::Place>>,
    /// `guards::bool_switch_semantics`'s base classification, per `(local, scope_id)`.
    bool_switch_base: FxHashMap<(usize, u64), crate::guards::BoolSwitchBase>,
    /// `guards::block_has_sole_predecessor` / `call_facts::sole_predecessor_is` table.
    sole_predecessors: Option<Rc<SolePredecessors>>,
    /// `generate::witness_grounding` / `generate::contract_vcs` normal-flow predecessor index.
    v2_predecessors: Option<Rc<V2Predecessors>>,
}

struct State {
    identity: Identity,
    tables: Tables,
}

/// Per-thread count of how many times each memoized analysis was actually
/// COMPUTED (a miss, or an inert-memo call). Counted whether or not the memo is
/// active, so a disabled run reports the uncached work — the "before" number.
/// Read with [`analysis_memo_stats`]; reset with [`reset_analysis_memo_stats`].
/// Deterministic for a given function and entry point, which is what lets a
/// regression test pin generation to a STEP bound rather than a wall clock.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AnalysisMemoStats {
    /// `place_to_var_name` mints. INSTRUMENTATION ONLY — this analysis is
    /// memoized by `place_memo`'s name cache, not here; the counter is bumped
    /// at the uncached mint so the work bound is measured whichever memo
    /// serves the query.
    pub place_names_computed: u64,
    /// Local-name tables actually BUILT (`LocalNameTable::of`: one pass over the
    /// function's locals). INSTRUMENTATION ONLY — `place_memo::local_names` memoizes
    /// the table inside a generation scope and builds one per ask outside a scope,
    /// where an uncached place name must cost exactly ONE
    /// (`tests/place_name_local_table_once.rs`).
    pub local_name_tables_computed: u64,
    /// Statement-version oracle builds (`StmtVersionCtx::build` — one dominator
    /// index, one write index and one SSA oracle per function).
    /// INSTRUMENTATION ONLY — memoized by `havoc_memo::version_oracle`.
    pub entry_versions_computed: u64,
    /// `writes_until` statement-PREFIX extractions actually performed (the write
    /// index's exact fallback, and the test-only reference form).
    pub writes_until_computed: u64,
    /// `mutable_pointer_local_names` + `mutably_borrowed_local_names` walks.
    pub havoc_lists_computed: u64,
    /// `deref_pointer_is_opaque` referent resolutions. INSTRUMENTATION ONLY —
    /// memoized by `havoc_memo::opaque_pointer`.
    pub deref_opacity_computed: u64,
    /// `local_versions_collapse_to_bare` decisions.
    pub ssa_collapse_computed: u64,
    /// `v2_array_version_prepass` walks.
    pub array_prepass_computed: u64,
    /// Whole-local base → index tables.
    pub base_index_computed: u64,
    /// Index-local tables (`generate::path_defs::local_is_index_operand`).
    pub index_locals_computed: u64,
    /// Discriminant-CSE anchor maps (`generate::discriminant_cse_anchor_map`).
    pub discriminant_cse_anchors_computed: u64,
    /// Laundered alias-root walks (`generate::path_defs::laundered_alias_roots`: one
    /// whole-body walk), memo hits excluded. Asked by every havoc list the semantic
    /// guard map builds, so an unscoped call-site producer ran one per call block.
    pub laundered_alias_roots_computed: u64,
    // ---- Deterministic WORK counters of the statement-version oracle
    // (`generate::cfg_index`, `rebind_index`, `block_writes`, `version_ssa`). Each
    // counts units of work actually performed — never wall time — so a scaling test
    // can assert how the oracle's cost grows with program size
    // (`generate/version_ssa_scaling_tests.rs`).
    /// Dominator-index BUILD work: edges scanned, nodes numbered, compression steps,
    /// SCC and def-list forest nodes.
    pub cfg_work: u64,
    /// Oracle QUERY steps: jump-pointer steps (level ancestor, LCA, deepest listed
    /// dominator) and range-minimum steps — O(log) per resolution.
    pub query_steps: u64,
    /// Rebinder-index probes: hash lookups, range-scan steps, entries indexed.
    pub rebind_probes: u64,
    /// Entries stored by the per-block write index.
    pub block_write_entries: u64,
    /// `writes_until` gate queries that needed the exact prefix extraction.
    pub gate_fallbacks: u64,
    /// Token-set tree NODES created by the SSA oracle's persistent hash-consed sets
    /// (a union creates O(log) of them, sharing the rest).
    pub leafset_elems: u64,
    /// Token-set union steps computed (memo misses, recursive steps included).
    pub leafset_unions: u64,
    /// Bytes of joined version tokens spelled.
    pub token_bytes: u64,
    /// Token-set tree nodes whose Merkle hash was computed (and registered) to spell a
    /// long joined set (`version_ssa::SetStore::set_hash`) — at most once per node per
    /// oracle.
    pub set_hash_nodes: u64,
    /// Set-hash COLLISIONS the registry caught (each falls back to the retired
    /// spelling). Nonzero only under the test seam that truncates the hash.
    pub set_hash_collisions: u64,
    /// SSA resolution steps (`(block, name)` resolutions).
    pub ssa_queries: u64,
    /// SSA joins (phis) resolved.
    pub ssa_phis: u64,
    /// Tracked names (the union of the gen-sets).
    pub tracked_names: u64,
    /// `fn_memo` identity checks (one per lookup of a memoized whole-body analysis).
    /// Each is O(1); the counter makes a per-statement lookup pattern visible to the
    /// scaling gate.
    pub memo_identity_checks: u64,
    /// Pseudo-def (loop-header) list entries materialised per queried name, with the
    /// defs walked to find them (`version_ssa::pseudo_defs`) — resolution work, bounded
    /// by the name's minimal SSA form.
    pub pseudo_defs: u64,
    // ---- Deterministic WORK counters of the interval fixpoint
    // (`abstract_interp::transfer`). INSTRUMENTATION ONLY.
    /// Units of fixpoint work actually DONE — an ascending-phase pop, a narrowing-pass
    /// block, a repair-round block — each one after its ambient-budget poll passed.
    pub interval_fixpoint_units: u64,
    /// Havoc sets derived and indexed (`transfer::CallHavoc`): at most one per
    /// havocking block (a `Call`, a `TailCall`, an `Opaque` terminator) per fixpoint
    /// run.
    pub interval_havoc_sets: u64,
    /// SHARED havoc indexes built by the interval fixpoint (`transfer::CallHavoc`):
    /// per fixpoint run at most one of the whole-function havoc list, shared by every
    /// block that havocs it unrefined, and — under the function's memo scope — one of
    /// the escape arm's kept list, shared by every escape-arm call.
    pub interval_function_havoc_indexes: u64,
    /// Statements visited by the block-definition extraction
    /// (`guards::extract_block_definitions*`): the helper work the version oracle's
    /// write index is BUILT from, invisible to its own counters.
    pub extraction_stmts: u64,
    /// Statements and terminators visited by the whole-body local-write walks of
    /// `local_defs` (`unique_value_def` and its siblings), which the extraction runs
    /// per statement it lowers.
    pub body_scan_items: u64,
    // ---- Deterministic WORK counters of the referent fold's stability walk
    // (`lib.rs::referent_fold`). INSTRUMENTATION ONLY.
    /// Stability walks actually RUN (`referent_fold::walk`) — memo hits excluded.
    pub fold_walks: u64,
    /// States those walks popped, their borrow-time-constant fixpoints included.
    pub fold_walk_steps: u64,
    /// Statements and terminators those walks examined (the per-state inner loop).
    pub fold_stmt_visits: u64,
    /// Nested referent resolutions a walk actually computed (`TaintCache::resolve`
    /// misses) for a store through another pointer in its region.
    pub fold_nested_resolutions: u64,
    /// Stability verdicts served from the certified verdict memo (a nested walk's
    /// included, wherever its stack certificate holds).
    pub fold_memo_hits: u64,
    /// Runs of the outcome enumeration (`referent_fold::outcomes`): one resolution
    /// computed with every stability walk replaced by a choice.
    pub fold_outcome_runs: u64,
    /// Stores through another pointer whose rebinding answer the enumerated outcomes
    /// decided — each one a nested resolution NOT run.
    pub fold_outcome_decisions: u64,
    /// `referent_fold::FoldIndex` builds (one per function inside a VC-gen scope).
    pub fold_index_builds: u64,
}

thread_local! {
    static MEMO: RefCell<Option<State>> = const { RefCell::new(None) };
    /// Test seam: when set, every wrapper computes uncached (and still counts).
    static DISABLED: Cell<bool> = const { Cell::new(false) };
    static STATS: Cell<AnalysisMemoStats> = const { Cell::new(AnalysisMemoStats {
        place_names_computed: 0,
        local_name_tables_computed: 0,
        entry_versions_computed: 0,
        writes_until_computed: 0,
        havoc_lists_computed: 0,
        deref_opacity_computed: 0,
        ssa_collapse_computed: 0,
        array_prepass_computed: 0,
        base_index_computed: 0,
        index_locals_computed: 0,
        discriminant_cse_anchors_computed: 0,
        laundered_alias_roots_computed: 0,
        cfg_work: 0,
        query_steps: 0,
        rebind_probes: 0,
        block_write_entries: 0,
        gate_fallbacks: 0,
        leafset_elems: 0,
        leafset_unions: 0,
        token_bytes: 0,
        set_hash_nodes: 0,
        set_hash_collisions: 0,
        ssa_queries: 0,
        ssa_phis: 0,
        tracked_names: 0,
        memo_identity_checks: 0,
        pseudo_defs: 0,
        interval_fixpoint_units: 0,
        interval_havoc_sets: 0,
        interval_function_havoc_indexes: 0,
        extraction_stmts: 0,
        body_scan_items: 0,
        fold_walks: 0,
        fold_walk_steps: 0,
        fold_stmt_visits: 0,
        fold_nested_resolutions: 0,
        fold_memo_hits: 0,
        fold_outcome_runs: 0,
        fold_outcome_decisions: 0,
        fold_index_builds: 0,
    }) };
}

/// Clear the memo. Called by `gen_work` on every outermost scope entry AND exit
/// so entries can never leak across functions (or linger while no VC-gen runs).
pub(super) fn reset() {
    MEMO.with(|m| *m.borrow_mut() = None);
}

pub(crate) fn is_disabled() -> bool {
    DISABLED.with(Cell::get)
}

fn active() -> bool {
    !is_disabled() && super::gen_work::scope_active()
}

/// Phase 1 of a query: read the bound tables WITHOUT rebinding. `None` when the
/// memo is inert, unbound, or bound to another function. The borrow is released
/// before returning, so the compute that follows a miss may itself query the
/// memo (the analyses nest: `block_entry_versions` mints place names).
fn lookup<R>(func: &VerifiableFunction, get: impl FnOnce(&Tables) -> Option<R>) -> Option<R> {
    if !active() {
        return None;
    }
    MEMO.with(|m| {
        let memo = m.borrow();
        let state = memo.as_ref()?;
        if !state.identity.matches(func) {
            return None;
        }
        get(&state.tables)
    })
}

/// Phase 2 of a query: store a freshly computed value, rebinding (and clearing)
/// first if the memo is unbound or bound to a different function.
fn store(func: &VerifiableFunction, put: impl FnOnce(&mut Tables)) {
    if !active() {
        return;
    }
    MEMO.with(|m| {
        let mut memo = m.borrow_mut();
        let state = match memo.as_mut() {
            Some(state) if state.identity.matches(func) => state,
            _ => memo.insert(State { identity: Identity::of(func), tables: Tables::default() }),
        };
        put(&mut state.tables);
    });
}

/// [`store`] that never REBINDS: it stores only when the memo is unbound or already
/// bound to `func`. For analyses asked about OTHER functions too (a callee's places
/// are sorted during the caller's generation), where rebinding would clear the bound
/// function's tables at every switch; a query for another function then computes
/// uncached, exactly as before the analysis was memoized.
fn store_if_bound(func: &VerifiableFunction, put: impl FnOnce(&mut Tables)) {
    if !active() {
        return;
    }
    MEMO.with(|m| {
        let mut memo = m.borrow_mut();
        match memo.as_mut() {
            Some(state) if state.identity.matches(func) => put(&mut state.tables),
            Some(_) => {}
            None => {
                let mut tables = Tables::default();
                put(&mut tables);
                *memo = Some(State { identity: Identity::of(func), tables });
            }
        }
    });
}

fn count(bump: impl FnOnce(&mut AnalysisMemoStats)) {
    STATS.with(|s| {
        let mut v = s.get();
        bump(&mut v);
        s.set(v);
    });
}

/// Shared shape for the `Option<Rc<T>>` singletons: hit → shared handle; miss →
/// compute outside the borrow, count, store, return.
fn cached_rc<T>(
    func: &VerifiableFunction,
    get: impl FnOnce(&Tables) -> Option<Rc<T>>,
    put: impl FnOnce(&mut Tables, Rc<T>),
    bump: impl FnOnce(&mut AnalysisMemoStats),
    compute: impl FnOnce() -> T,
) -> Rc<T> {
    if let Some(hit) = lookup(func, get) {
        return hit;
    }
    count(bump);
    let value = Rc::new(compute());
    store(func, |t| put(t, Rc::clone(&value)));
    value
}

/// Shared shape for the per-key `bool` tables.
fn cached_flag(
    func: &VerifiableFunction,
    key: usize,
    get: impl FnOnce(&Tables) -> &FxHashMap<usize, bool>,
    put: impl FnOnce(&mut Tables) -> &mut FxHashMap<usize, bool>,
    bump: impl FnOnce(&mut AnalysisMemoStats),
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| get(t).get(&key).copied()) {
        return hit;
    }
    count(bump);
    let value = compute();
    store(func, |t| {
        put(t).insert(key, value);
    });
    value
}

// ---------------------------------------------------------------------------
// The memoized analyses. Each wrapper takes the UNCACHED computation as a
// closure so the analysis itself stays where it is defined and documented.
// ---------------------------------------------------------------------------

/// The first local index `l` in `0..func.body.locals.len()` whose WHOLE-local
/// name (`place_to_var_name` of `Place { local: l, projections: [] }`) is
/// `base` — the `(0..len).find(..)` the SSA-collapse pass runs per versioned
/// variable, answered from a table built once per function. `mint` is the
/// whole-local name mint (so the table is built through the memoized
/// `place_to_var_name`, keeping the two spellings identical by construction).
pub(crate) fn whole_local_index_by_base(
    func: &VerifiableFunction,
    base: &str,
    mint: impl Fn(usize) -> String,
) -> Option<usize> {
    if !active() {
        // Inert: the original linear search, byte-for-byte.
        return (0..func.body.locals.len()).find(|&l| mint(l) == base);
    }
    if let Some(hit) = lookup(func, |t| Some(t.whole_local_index_by_base.as_ref()?.get(base).copied())) {
        return hit;
    }
    count(|s| s.base_index_computed += 1);
    let mut table: FxHashMap<String, usize> =
        FxHashMap::with_capacity_and_hasher(func.body.locals.len(), Default::default());
    for l in 0..func.body.locals.len() {
        // First index wins — `find` semantics.
        table.entry(mint(l)).or_insert(l);
    }
    let found = table.get(base).copied();
    store(func, |t| t.whole_local_index_by_base = Some(Rc::new(table)));
    found
}

/// `mutable_pointer_local_names(func)`.
pub(crate) fn mut_pointer_names(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<String>,
) -> Rc<Vec<String>> {
    cached_rc(
        func,
        |t| t.mut_pointer_names.clone(),
        |t, v| t.mut_pointer_names = Some(v),
        |s| s.havoc_lists_computed += 1,
        compute,
    )
}

/// The noalias `&mut` parameters of `func` (`path_defs::noalias_mut_params`).
pub(crate) fn noalias_mut_params(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<usize>,
) -> Rc<Vec<usize>> {
    cached_rc(
        func,
        |t| t.noalias_mut_params.clone(),
        |t, v| t.noalias_mut_params = Some(v),
        |s| s.havoc_lists_computed += 1,
        compute,
    )
}

/// `mutably_borrowed_local_names(func)`.
pub(crate) fn mut_borrowed_names(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<String>,
) -> Rc<Vec<String>> {
    cached_rc(
        func,
        |t| t.mut_borrowed_names.clone(),
        |t, v| t.mut_borrowed_names = Some(v),
        |s| s.havoc_lists_computed += 1,
        compute,
    )
}

/// `generate::path_defs::escape_havoc_at`'s per-parameter escape reach.
pub(crate) fn param_escape_reach(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> crate::generate::ParamEscapeReach,
) -> Rc<crate::generate::ParamEscapeReach> {
    cached_rc(
        func,
        |t| t.param_escape_reach.clone(),
        |t, v| t.param_escape_reach = Some(v),
        |_| {},
        compute,
    )
}

/// `generate::path_defs::escape_havoc_at`'s split for one exempt-parameter set.
pub(crate) fn escape_havoc_exempting(
    func: &VerifiableFunction,
    exempt: &[usize],
    compute: impl FnOnce() -> crate::generate::EscapeHavoc,
) -> Rc<crate::generate::EscapeHavoc> {
    if let Some(hit) = lookup(func, |t| t.escape_havoc_exempting.get(exempt).cloned()) {
        return hit;
    }
    let value = Rc::new(compute());
    store(func, |t| {
        t.escape_havoc_exempting.insert(exempt.to_vec(), Rc::clone(&value));
    });
    value
}

/// `generate::path_defs::local_is_index_operand`'s per-function table: one whole-body
/// walk marking every local that occurs as an `Index(l)` projection operand.
pub(crate) fn index_locals(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<bool>,
) -> Rc<Vec<bool>> {
    cached_rc(
        func,
        |t| t.index_locals.clone(),
        |t, v| t.index_locals = Some(v),
        |s| s.index_locals_computed += 1,
        compute,
    )
}

/// `generate::discriminant_cse_anchor_map(func)`.
pub(crate) fn discriminant_cse_anchors(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> FxHashMap<String, String>,
) -> Rc<FxHashMap<String, String>> {
    cached_rc(
        func,
        |t| t.discriminant_cse_anchors.clone(),
        |t, v| t.discriminant_cse_anchors = Some(v),
        |s| s.discriminant_cse_anchors_computed += 1,
        compute,
    )
}

/// `lib::symbolic_assignment_sorts(func)`, once per function — `None` outside a
/// generation scope (the caller then scans, as it always did).
pub(crate) fn symbolic_sorts(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> trust_types::fx::FxHashMap<trust_types::Place, Option<trust_types::Sort>>,
) -> Option<Rc<trust_types::fx::FxHashMap<trust_types::Place, Option<trust_types::Sort>>>> {
    if !active() {
        return None;
    }
    if let Some(hit) = lookup(func, |t| t.symbolic_sorts.clone()) {
        return Some(hit);
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.symbolic_sorts = Some(Rc::clone(&value)));
    Some(value)
}

/// `lib::array_theory_local(func, local)`, once per `(function, local)` (it walks the
/// whole body for an array-typed local, and every sort of the bare local asks it).
pub(crate) fn array_model(
    func: &VerifiableFunction,
    local: usize,
    compute: impl FnOnce() -> Option<super::ArrayModel>,
) -> Option<super::ArrayModel> {
    if let Some(hit) = lookup(func, |t| t.array_models.get(&local).cloned()) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| {
        t.array_models.insert(local, value.clone());
    });
    value
}

/// `generate::path_defs::func_has_pointer_laundering`, once per function.
pub(crate) fn pointer_laundering(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| t.pointer_laundering) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| t.pointer_laundering = Some(value));
    value
}

/// `generate::path_defs::func_has_writable_pointer_laundering`, once per function.
pub(crate) fn writable_pointer_laundering(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| t.writable_pointer_laundering) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| t.writable_pointer_laundering = Some(value));
    value
}

/// `generate::call_facts::body_mentions_opaque_scalar`, once per function.
pub(crate) fn body_mentions_opaque_scalar(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| t.body_mentions_opaque_scalar) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| t.body_mentions_opaque_scalar = Some(value));
    value
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BlockPredState {
    Zero,
    One(trust_types::BlockId),
    Many,
}

impl BlockPredState {
    #[inline]
    fn record(&mut self, pred: trust_types::BlockId) {
        match *self {
            Self::Zero => *self = Self::One(pred),
            Self::One(prev) if prev == pred => {}
            Self::One(_) | Self::Many => *self = Self::Many,
        }
    }
}

/// Per-function in-CFG predecessor summary answering both
/// `guards::block_has_sole_predecessor` (0-or-1 predecessor among blocks present in
/// `func.body.blocks`) and `call_facts::sole_predecessor_is` (strictly 1 predecessor,
/// excluding `bb0`).
pub(crate) struct SolePredecessors(SolePredecessorsKind);

enum SolePredecessorsKind {
    Canonical {
        states: Vec<BlockPredState>,
        overflow: FxHashMap<trust_types::BlockId, BlockPredState>,
    },
    NonCanonical,
}

impl SolePredecessors {
    fn build(func: &VerifiableFunction) -> Self {
        let blocks = &func.body.blocks;
        if !blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
            return Self(SolePredecessorsKind::NonCanonical);
        }
        let mut states = vec![BlockPredState::Zero; blocks.len()];
        let mut overflow: FxHashMap<trust_types::BlockId, BlockPredState> = Default::default();
        for b in blocks {
            let from = b.id;
            b.terminator.for_each_in_cfg_successor(|succ| {
                if let Some(slot) = states.get_mut(succ.0) {
                    slot.record(from);
                } else {
                    overflow.entry(succ).or_insert(BlockPredState::Zero).record(from);
                }
            });
        }
        Self(SolePredecessorsKind::Canonical { states, overflow })
    }

    #[inline]
    pub(crate) fn block_has_sole_predecessor(
        &self,
        block: trust_types::BlockId,
        from: trust_types::BlockId,
    ) -> Option<bool> {
        match &self.0 {
            SolePredecessorsKind::NonCanonical => None,
            SolePredecessorsKind::Canonical { states, .. } => Some(match states.get(block.0) {
                Some(BlockPredState::Zero) => true,
                Some(BlockPredState::One(pred)) => *pred == from,
                Some(BlockPredState::Many) | None => false,
            }),
        }
    }

    #[inline]
    pub(crate) fn sole_predecessor_is(
        &self,
        target: trust_types::BlockId,
        from: trust_types::BlockId,
    ) -> Option<bool> {
        if target.0 == 0 {
            return Some(false);
        }
        match &self.0 {
            SolePredecessorsKind::NonCanonical => None,
            SolePredecessorsKind::Canonical { states, overflow } => {
                let state = states
                    .get(target.0)
                    .copied()
                    .or_else(|| overflow.get(&target).copied())
                    .unwrap_or(BlockPredState::Zero);
                Some(matches!(state, BlockPredState::One(pred) if pred == from))
            }
        }
    }

    /// For a non-entry `target`, the unique block `pred` in `func.body.blocks` whose
    /// terminator reaches `target` (normal or cleanup edge, matching
    /// `Terminator::has_exit_block_target`), or `Some(None)` when `target` is `bb0` or
    /// zero / multiple blocks reach `target`. `None` on non-canonical block layouts.
    #[inline]
    pub(crate) fn unique_exit_predecessor(
        &self,
        target: trust_types::BlockId,
    ) -> Option<Option<trust_types::BlockId>> {
        if target.0 == 0 {
            return Some(None);
        }
        match &self.0 {
            SolePredecessorsKind::NonCanonical => None,
            SolePredecessorsKind::Canonical { states, overflow } => {
                let state = states
                    .get(target.0)
                    .copied()
                    .or_else(|| overflow.get(&target).copied())
                    .unwrap_or(BlockPredState::Zero);
                Some(match state {
                    BlockPredState::One(pred) => Some(pred),
                    BlockPredState::Zero | BlockPredState::Many => None,
                })
            }
        }
    }

    /// Whether no block in `func.body.blocks` with `b.id != allowed` has
    /// `b.terminator.has_exit_block_target(target)` — exact O(1) equivalent of
    /// `!func.body.blocks.iter().any(|b| b.id != allowed && b.terminator.has_exit_block_target(target))`.
    #[inline]
    pub(crate) fn no_other_exit_predecessor(
        &self,
        target: trust_types::BlockId,
        allowed: trust_types::BlockId,
    ) -> Option<bool> {
        match &self.0 {
            SolePredecessorsKind::NonCanonical => None,
            SolePredecessorsKind::Canonical { states, overflow } => {
                let state = states
                    .get(target.0)
                    .copied()
                    .or_else(|| overflow.get(&target).copied())
                    .unwrap_or(BlockPredState::Zero);
                Some(match state {
                    BlockPredState::Zero => true,
                    BlockPredState::One(pred) => pred == allowed,
                    BlockPredState::Many => false,
                })
            }
        }
    }
}

pub(crate) fn sole_predecessors(func: &VerifiableFunction) -> Option<Rc<SolePredecessors>> {
    if !active() {
        return None;
    }
    if let Some(hit) = lookup(func, |t| t.sole_predecessors.clone()) {
        return Some(hit);
    }
    let value = Rc::new(SolePredecessors::build(func));
    store_if_bound(func, |t| t.sole_predecessors = Some(Rc::clone(&value)));
    Some(value)
}

/// Per-function normal-flow predecessor index matching
/// `trust_types::terminator_obligations::terminator_has_target` (`v2_terminator_has_target`).
///
/// Predecessor positions in `func.body.blocks` are recorded in strictly ascending
/// `0..blocks.len()` order with multi-edges from the same predecessor block deduplicated,
/// reproducing `func.body.blocks.iter().filter(|pred| v2_terminator_has_target(&pred.terminator, target))`
/// verbatim on both canonical and non-canonical block layouts.
pub(crate) struct V2Predecessors {
    dense: Vec<Vec<u32>>,
    overflow: FxHashMap<trust_types::BlockId, Vec<u32>>,
    exhaustive: bool,
}

impl V2Predecessors {
    fn build(func: &VerifiableFunction) -> Self {
        let blocks = &func.body.blocks;
        if u32::try_from(blocks.len()).is_err() {
            return Self { dense: Vec::new(), overflow: Default::default(), exhaustive: false };
        }
        let mut dense = vec![Vec::new(); blocks.len()];
        let mut overflow: FxHashMap<trust_types::BlockId, Vec<u32>> = Default::default();
        for (pos, pred) in blocks.iter().enumerate() {
            let pos_u32 = pos as u32;
            trust_types::terminator_obligations::for_each_terminator_target(
                &pred.terminator,
                |target| {
                    let list = if let Some(slot) = dense.get_mut(target.0) {
                        slot
                    } else {
                        overflow.entry(target).or_default()
                    };
                    if list.last().copied() != Some(pos_u32) {
                        list.push(pos_u32);
                    }
                },
            );
        }
        Self { dense, overflow, exhaustive: true }
    }

    #[inline]
    fn positions(&self, target: trust_types::BlockId) -> &[u32] {
        if let Some(slot) = self.dense.get(target.0) {
            slot.as_slice()
        } else if let Some(slot) = self.overflow.get(&target) {
            slot.as_slice()
        } else {
            &[]
        }
    }

    #[inline]
    pub(crate) fn predecessors<'a>(
        &self,
        func: &'a VerifiableFunction,
        target: trust_types::BlockId,
    ) -> Vec<&'a trust_types::BasicBlock> {
        if !self.exhaustive {
            return func
                .body
                .blocks
                .iter()
                .filter(|pred| {
                    trust_types::terminator_obligations::terminator_has_target(
                        &pred.terminator,
                        target,
                    )
                })
                .collect();
        }
        self.positions(target)
            .iter()
            .filter_map(|&pos| func.body.blocks.get(pos as usize))
            .collect()
    }

    #[inline]
    pub(crate) fn for_each_predecessor<'a>(
        &self,
        func: &'a VerifiableFunction,
        target: trust_types::BlockId,
        mut f: impl FnMut(&'a trust_types::BasicBlock) -> std::ops::ControlFlow<()>,
    ) {
        if !self.exhaustive {
            for pred in &func.body.blocks {
                if trust_types::terminator_obligations::terminator_has_target(
                    &pred.terminator,
                    target,
                ) && f(pred).is_break()
                {
                    break;
                }
            }
            return;
        }
        for &pos in self.positions(target) {
            if let Some(pred) = func.body.blocks.get(pos as usize)
                && f(pred).is_break()
            {
                break;
            }
        }
    }

    #[inline]
    pub(crate) fn sole_predecessor<'a>(
        &self,
        func: &'a VerifiableFunction,
        target: trust_types::BlockId,
    ) -> Option<&'a trust_types::BasicBlock> {
        if !self.exhaustive {
            let mut preds = func.body.blocks.iter().filter(|pred| {
                trust_types::terminator_obligations::terminator_has_target(&pred.terminator, target)
            });
            return match (preds.next(), preds.next()) {
                (Some(only), None) => Some(only),
                _ => None,
            };
        }
        let &[pos] = self.positions(target) else { return None };
        func.body.blocks.get(pos as usize)
    }
}

pub(crate) fn v2_predecessors(func: &VerifiableFunction) -> Option<Rc<V2Predecessors>> {
    if !active() {
        return None;
    }
    if let Some(hit) = lookup(func, |t| t.v2_predecessors.clone()) {
        return Some(hit);
    }
    let value = Rc::new(V2Predecessors::build(func));
    store_if_bound(func, |t| t.v2_predecessors = Some(Rc::clone(&value)));
    Some(value)
}

pub(crate) fn v2_predecessors_or_build(func: &VerifiableFunction) -> Rc<V2Predecessors> {
    if let Some(memo) = v2_predecessors(func) {
        memo
    } else {
        Rc::new(V2Predecessors::build(func))
    }
}

/// `generate::path_defs::laundered_alias_roots`, once per function.
pub(crate) fn laundered_alias_roots(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<String>,
) -> Rc<Vec<String>> {
    if let Some(hit) = lookup(func, |t| t.laundered_alias_roots.clone()) {
        return hit;
    }
    count(|s| s.laundered_alias_roots_computed += 1);
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.laundered_alias_roots = Some(Rc::clone(&value)));
    value
}

/// `generate::path_defs::stored_ref_pointee_names`, once per function.
pub(crate) fn stored_ref_pointee_names(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> Vec<String>,
) -> Rc<Vec<String>> {
    if let Some(hit) = lookup(func, |t| t.stored_ref_pointee_names.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.stored_ref_pointee_names = Some(Rc::clone(&value)));
    value
}

/// `generate::path_defs::shared_borrowed_cell_places`' per-local map, once per function.
pub(crate) fn shared_cell_borrows(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> trust_types::fx::FxHashMap<usize, Rc<Vec<trust_types::Place>>>,
) -> Rc<trust_types::fx::FxHashMap<usize, Rc<Vec<trust_types::Place>>>> {
    if let Some(hit) = lookup(func, |t| t.shared_cell_borrows.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.shared_cell_borrows = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::checked_arith_result_value_vars`, once per function.
pub(crate) fn checked_arith_result_vars(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> trust_types::fx::FxHashSet<String>,
) -> Rc<trust_types::fx::FxHashSet<String>> {
    if let Some(hit) = lookup(func, |t| t.checked_arith_result_vars.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.checked_arith_result_vars = Some(Rc::clone(&value)));
    value
}

/// Per-function parameter scalar-range summary for
/// `generate::alloc_vcs::conjoin_arg_type_ranges_step`.
pub(crate) struct ArgTypeRangeSummary {
    pub(crate) base_bounds: Vec<trust_types::Formula>,
    pub(crate) base_var_names: Vec<String>,
    pub(crate) param_ranges: FxHashMap<String, crate::range::RustScalarRange>,
    /// Source local names containing `'#'` (empty in normal Rust bodies), used by
    /// the fail-closed collision guard when bounding SSA-versioned parameter names.
    pub(crate) hash_local_names: trust_types::fx::FxHashSet<String>,
}

/// `generate::alloc_vcs::conjoin_arg_type_ranges_step` parameter summary, once per function.
pub(crate) fn arg_type_ranges(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> ArgTypeRangeSummary,
) -> Rc<ArgTypeRangeSummary> {
    if let Some(hit) = lookup(func, |t| t.arg_type_ranges.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.arg_type_ranges = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::local_scalar_range_map`, once per function.
pub(crate) fn local_scalar_ranges(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> FxHashMap<String, crate::range::RustScalarRange>,
) -> Rc<FxHashMap<String, crate::range::RustScalarRange>> {
    if let Some(hit) = lookup(func, |t| t.local_scalar_ranges.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.local_scalar_ranges = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::local_value_join_interval_map`, once per function.
pub(crate) fn local_value_join_intervals(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> FxHashMap<String, (Option<i128>, Option<i128>)>,
) -> Rc<FxHashMap<String, (Option<i128>, Option<i128>)>> {
    if let Some(hit) = lookup(func, |t| t.local_value_join_intervals.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.local_value_join_intervals = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::datatype_field_range_map`, once per function.
pub(crate) fn datatype_field_ranges(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> FxHashMap<String, crate::range::RustScalarRange>,
) -> Rc<FxHashMap<String, crate::range::RustScalarRange>> {
    if let Some(hit) = lookup(func, |t| t.datatype_field_ranges.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.datatype_field_ranges = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::length_nonneg_base_names`, once per function.
pub(crate) fn length_nonneg_bases(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> trust_types::fx::FxHashSet<String>,
) -> Rc<trust_types::fx::FxHashSet<String>> {
    if let Some(hit) = lookup(func, |t| t.length_nonneg_bases.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.length_nonneg_bases = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::coll_len_bound_vars`, once per function.
pub(crate) fn coll_len_bound_vars(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> (trust_types::fx::FxHashSet<String>, trust_types::fx::FxHashSet<String>),
) -> Rc<(trust_types::fx::FxHashSet<String>, trust_types::fx::FxHashSet<String>)> {
    if let Some(hit) = lookup(func, |t| t.coll_len_bound_vars.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.coll_len_bound_vars = Some(Rc::clone(&value)));
    value
}

/// `generate::type_ranges::nonzst_slice_len_vars`, once per function.
pub(crate) fn nonzst_slice_len_vars(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> trust_types::fx::FxHashSet<String>,
) -> Rc<trust_types::fx::FxHashSet<String>> {
    if let Some(hit) = lookup(func, |t| t.nonzst_slice_len_vars.clone()) {
        return hit;
    }
    let value = Rc::new(compute());
    store_if_bound(func, |t| t.nonzst_slice_len_vars = Some(Rc::clone(&value)));
    value
}

/// `guards::local_is_mutably_borrowed(func, local)`, once per `(function, local)`.
pub(crate) fn local_is_mutably_borrowed(
    func: &VerifiableFunction,
    local: usize,
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| t.local_is_mutably_borrowed.get(&local).copied()) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| {
        t.local_is_mutably_borrowed.insert(local, value);
    });
    value
}

/// `guards::local_mut_borrows_may_resize(func, local)`, once per `(function, local)`.
/// Only stored when the ambient budget has not been exhausted so an interrupted
/// conservative `true` is never cached past a budget check.
pub(crate) fn local_mut_borrows_may_resize(
    func: &VerifiableFunction,
    local: usize,
    compute: impl FnOnce() -> bool,
) -> bool {
    if let Some(hit) = lookup(func, |t| t.local_mut_borrows_may_resize.get(&local).copied()) {
        return hit;
    }
    let value = compute();
    if !trust_types::verify_budget::exhausted_readonly() {
        store_if_bound(func, |t| {
            t.local_mut_borrows_may_resize.insert(local, value);
        });
    }
    value
}

/// `guards::base_collection_local_unique(func, start)`, once per `(function, start)`.
pub(crate) fn base_collection_local(
    func: &VerifiableFunction,
    start: usize,
    compute: impl FnOnce() -> Option<usize>,
) -> Option<usize> {
    if let Some(hit) = lookup(func, |t| t.base_collection_local.get(&start).copied()) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| {
        t.base_collection_local.insert(start, value);
    });
    value
}

/// `guards::base_collection_place_unique(func, start)`, once per `(function, start)`.
pub(crate) fn base_collection_place(
    func: &VerifiableFunction,
    start: usize,
    compute: impl FnOnce() -> Option<trust_types::Place>,
) -> Option<trust_types::Place> {
    if let Some(hit) = lookup(func, |t| t.base_collection_place.get(&start).cloned()) {
        return hit;
    }
    let value = compute();
    store_if_bound(func, |t| {
        t.base_collection_place.insert(start, value.clone());
    });
    value
}

/// `guards::bool_switch_semantics`'s base classification for `(local, scope_id)`.
pub(crate) fn bool_switch_base(
    func: &VerifiableFunction,
    key: (usize, u64),
    compute: impl FnOnce() -> crate::guards::BoolSwitchBase,
) -> crate::guards::BoolSwitchBase {
    if let Some(hit) = lookup(func, |t| t.bool_switch_base.get(&key).cloned()) {
        return hit;
    }
    let value = compute();
    if !trust_types::verify_budget::exhausted_readonly() {
        store_if_bound(func, |t| {
            t.bool_switch_base.insert(key, value.clone());
        });
    }
    value
}

/// `local_versions_collapse_to_bare(func, local)`.
pub(crate) fn collapse_to_bare(
    func: &VerifiableFunction,
    local: usize,
    compute: impl FnOnce() -> bool,
) -> bool {
    cached_flag(
        func,
        local,
        |t| &t.collapse_to_bare,
        |t| &mut t.collapse_to_bare,
        |s| s.ssa_collapse_computed += 1,
        compute,
    )
}

/// `v2_array_version_prepass(func)` as a shared handle.
pub(crate) fn array_prepass(
    func: &VerifiableFunction,
    compute: impl FnOnce() -> ArrayVersionCtx,
) -> Rc<ArrayVersionCtx> {
    cached_rc(
        func,
        |t| t.array_prepass.clone(),
        |t, v| t.array_prepass = Some(v),
        |s| s.array_prepass_computed += 1,
        compute,
    )
}

// ---------------------------------------------------------------------------
// Instrumentation for the analyses memoized ELSEWHERE (`place_memo`'s name
// cache and `havoc_memo`). Bumped at the UNCACHED computation, so the census
// budget regression test (`tests/vcgen_budget_realmir.rs`) pins the real work
// bound without depending on which module owns the cache. Diagnostic only —
// never part of a verdict, and never consulted by generation.
// ---------------------------------------------------------------------------

/// One `place_to_var_name` mint was actually performed.
pub(crate) fn count_place_name() {
    count(|s| s.place_names_computed += 1);
}

/// One local-name table (`LocalNameTable::of`) was actually built.
pub(crate) fn count_local_name_table() {
    count(|s| s.local_name_tables_computed += 1);
}

/// One `block_entry_versions` reaching-version fixpoint was actually run.
pub(crate) fn count_entry_versions() {
    count(|s| s.entry_versions_computed += 1);
}

/// One `writes_until` statement-prefix extraction was actually performed.
pub(crate) fn count_writes_until() {
    count(|s| s.writes_until_computed += 1);
}

/// One `deref_pointer_is_opaque` referent resolution was actually run.
pub(crate) fn count_deref_opacity() {
    count(|s| s.deref_opacity_computed += 1);
}

pub(crate) fn count_cfg_work(n: u64) {
    count(|s| s.cfg_work += n);
}

pub(crate) fn count_query_steps(n: u64) {
    count(|s| s.query_steps += n);
}

pub(crate) fn count_rebind_probes(n: u64) {
    count(|s| s.rebind_probes += n);
}

pub(crate) fn count_block_write_entries(n: u64) {
    count(|s| s.block_write_entries += n);
}

pub(crate) fn count_gate_fallbacks() {
    count(|s| s.gate_fallbacks += 1);
}

pub(crate) fn count_leafset_elems(n: u64) {
    count(|s| s.leafset_elems += n);
}

pub(crate) fn count_leafset_unions(n: u64) {
    count(|s| s.leafset_unions += n);
}

pub(crate) fn count_token_bytes(n: u64) {
    count(|s| s.token_bytes += n);
}

pub(crate) fn count_set_hash_nodes(n: u64) {
    count(|s| s.set_hash_nodes += n);
}

pub(crate) fn count_set_hash_collisions(n: u64) {
    count(|s| s.set_hash_collisions += n);
}

pub(crate) fn count_ssa_queries(n: u64) {
    count(|s| s.ssa_queries += n);
}

pub(crate) fn count_ssa_phis(n: u64) {
    count(|s| s.ssa_phis += n);
}

pub(crate) fn count_tracked_names(n: u64) {
    count(|s| s.tracked_names += n);
}

pub(crate) fn count_pseudo_defs(n: u64) {
    count(|s| s.pseudo_defs += n);
}

pub(crate) fn count_interval_fixpoint_units() {
    count(|s| s.interval_fixpoint_units += 1);
}

pub(crate) fn count_interval_havoc_sets() {
    count(|s| s.interval_havoc_sets += 1);
}

pub(crate) fn count_interval_function_havoc_indexes() {
    count(|s| s.interval_function_havoc_indexes += 1);
}

pub(crate) fn count_extraction_stmts(n: u64) {
    count(|s| s.extraction_stmts += n);
}

pub(crate) fn count_body_scan_items(n: u64) {
    count(|s| s.body_scan_items += n);
}

pub(crate) fn count_fold_walks() {
    count(|s| s.fold_walks += 1);
}

pub(crate) fn count_fold_walk_steps(n: u64) {
    count(|s| s.fold_walk_steps += n);
}

pub(crate) fn count_fold_stmt_visits(n: u64) {
    count(|s| s.fold_stmt_visits += n);
}

pub(crate) fn count_fold_nested_resolutions() {
    count(|s| s.fold_nested_resolutions += 1);
}

pub(crate) fn count_fold_memo_hits() {
    count(|s| s.fold_memo_hits += 1);
}

pub(crate) fn count_fold_outcome_runs() {
    count(|s| s.fold_outcome_runs += 1);
}

pub(crate) fn count_fold_outcome_decisions() {
    count(|s| s.fold_outcome_decisions += 1);
}

pub(crate) fn count_fold_index_builds() {
    count(|s| s.fold_index_builds += 1);
}

// ---------------------------------------------------------------------------
// Public measurement / test surface.
// ---------------------------------------------------------------------------

/// Cumulative per-thread analysis computation counts since the last
/// [`reset_analysis_memo_stats`]. Diagnostic only — never part of a verdict.
#[must_use]
pub fn analysis_memo_stats() -> AnalysisMemoStats {
    STATS.with(Cell::get)
}

/// Zero the per-thread analysis computation counts.
pub fn reset_analysis_memo_stats() {
    STATS.with(|s| s.set(AnalysisMemoStats::default()));
}

/// Run `f` with THIS module's analysis memo DISABLED on this thread (every
/// wrapper computes uncached, still counting). A parity seam for tests that
/// prove the memo is verdict-identical; not a user-facing switch and not read
/// from any environment. Restored on unwind.
///
/// It does NOT disable `place_memo` or `havoc_memo` — those are `origin/main`'s
/// caches with their own discipline, and switching them off would make the
/// census fixtures take minutes rather than seconds. The parity seam therefore
/// covers exactly the analyses this module owns.
pub fn with_analysis_memo_disabled<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            DISABLED.with(|d| d.set(self.0));
        }
    }
    let _restore = Restore(DISABLED.with(|d| d.replace(true)));
    // Nothing computed under the previous setting may be served across the
    // switch in either direction: an enabled run after a disabled one would be
    // fine (the values are identical), but clearing keeps the seam simple to
    // reason about.
    reset();
    let out = f();
    reset();
    out
}
