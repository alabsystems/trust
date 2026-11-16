// trust-vcgen/src/generate/legacy_version_oracle.rs: the RETIRED statement-version
// oracle — the two whole-CFG reaching-version fixpoints (`entry_versions_fixpoint`) and
// the dense per-block `name -> {token}` maps `StmtVersionCtx` used to hold — kept
// VERBATIM as a differential for the SSA oracle that replaced them
// (`version_ssa` / `block_writes`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Compiled only for tests and under the `version-oracle-differential` feature. In
// that configuration `StmtVersionCtx` builds this oracle beside the SSA one and
// asserts that EVERY `version_token_at` / `full_graph_union_is_entry_only` answer is
// byte-identical (see `StmtVersionCtx::check_against_legacy`), so running the crate's
// test suite — unit tests by default, integration tests with the feature — is a
// differential over every body those tests build.
//
// Nothing here is reachable from production code. The step cap and budget polls of
// the fixpoint are kept as they were (this is the reference implementation, not a
// maintained one); a run whose fixpoint did not converge is simply not compared.

#![allow(dead_code)]

use std::collections::BTreeSet;

use super::*;

thread_local! {
    /// Test seam: set to skip building the retired oracle beside the SSA one (the
    /// linear-scaling tests measure the SSA oracle alone).
    static DIFFERENTIAL_OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether `StmtVersionCtx::build` also builds the retired oracle and cross-checks
/// every answer. On by default wherever this module is compiled.
pub(crate) fn differential_enabled() -> bool {
    !DIFFERENTIAL_OFF.with(std::cell::Cell::get)
}

thread_local! {
    /// Test seam: answer every oracle query with the RETIRED oracle's answer instead
    /// of the SSA one (and skip the comparison), so a whole generation can be run
    /// once per oracle and the outputs compared byte for byte.
    static LEGACY_ANSWERS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) fn legacy_answers() -> bool {
    LEGACY_ANSWERS.with(std::cell::Cell::get)
}

/// Run `f` with every oracle query answered by the retired oracle (restored on unwind).
pub(crate) fn with_legacy_answers<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            LEGACY_ANSWERS.with(|d| d.set(self.0));
        }
    }
    let _restore = Restore(LEGACY_ANSWERS.with(|d| d.replace(true)));
    f()
}

/// The retired gen-sets and OUT tokens (`entry_version_gen_sets`), as strings, per
/// block — the reference for the write index's gen-sets and `out_token`. `None` iff
/// the ambient verify budget tripped part-way (the precompute returns no partial
/// sets); the parity tests install no budget.
pub(crate) fn legacy_gen_out(func: &VerifiableFunction) -> Option<Vec<FxHashMap<String, String>>> {
    let sets = entry_version_gen_sets(func)?;
    let InternedGenSets { names, toks, gen_ids, .. } = &sets.interned;
    Some(
        gen_ids
            .iter()
            .map(|pairs| {
                pairs
                    .iter()
                    .map(|&(nm, tok)| (names[nm as usize].clone(), toks[tok as usize].clone()))
                    .collect()
            })
            .collect(),
    )
}

/// Run `f` without the differential (restored on unwind).
pub(crate) fn without_differential<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            DIFFERENTIAL_OFF.with(|d| d.set(self.0));
        }
    }
    let _restore = Restore(DIFFERENTIAL_OFF.with(|d| d.replace(true)));
    f()
}

/// Inter-block reaching-version oracle. Maps each block to `{name -> set of
/// STATEMENT-GRANULAR OUT tokens}` reaching its entry. An OUT token is
/// `s{pred}_{k}` — the predecessor block and the LAST statement that wrote (or
/// opaque-deref-store HAVOCED) the name — matching the within-block token format
/// in `version_token_at`. This is what lets a fact threaded from a predecessor and
/// versioned at its establish point connect to a LIVE successor read (same token)
/// yet stay name-disjoint from a HAVOCED one (the havoc's later statement gives a
/// distinct token). A block-id-only token (the old encoding) collapsed a
/// predecessor's establishing write and its havoc to one token, which is why the
/// inter-block threading kill could not be replaced by versioning before.
pub(crate) fn block_entry_versions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        // UNWIND-INCLUSIVE predecessor edges, matching the fact-transport graph
        // (`v2_path_def_fixpoint` transports facts across cleanup edges): a
        // cleanup-only-reachable block must NOT render its reads bare when a
        // normal-path write precedes the unwind — bare is exactly what let a
        // rename-exempt entry precondition unify across a dropped-def write on
        // the unwind shape (`tests/dropped_def_write_visibility.rs`). Extra
        // predecessor edges only ADD reaching tokens, moving reads AWAY from
        // the bare/entry rendering — rename-exempt bare facts can only LOSE
        // unification points (monotone-sound).
        for t in full_graph_terminator_targets(&b.terminator, b.id) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }
    entry_versions_fixpoint(func, &preds).0
}

/// FAIL-CLOSED sibling of [`block_entry_versions`]: the same reaching-version
/// fixpoint over the same unwind-inclusive predecessor relation (since
/// 2026-08-30 both build their edges from `full_graph_terminator_targets`; this
/// one predates that adoption). Under this map, a name whose reaching union at a
/// block is exactly `{e}` has NO writer on ANY runtime path into the block, normal
/// or unwind — the entry-denotation guarantee the `#e` mint gate in
/// `pin_in_place_update_reads` requires. The remaining difference is convergence
/// semantics: `None` when the fixpoint hit its step cap without converging; the
/// sole consumer fails closed on `None` (no `#e` minted), while the v2 caller
/// keeps its historical partial-map behavior.
pub(crate) fn block_entry_versions_full_graph(
    func: &VerifiableFunction,
) -> Option<FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        for t in full_graph_terminator_targets(&b.terminator, b.id) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }
    let (map, converged) = entry_versions_fixpoint(func, &preds);
    converged.then_some(map)
}

/// The shared fixpoint of [`block_entry_versions`] and
/// [`block_entry_versions_full_graph`]; only the predecessor relation differs.
/// The second return is CONVERGENCE: `false` iff the step cap was hit while the
/// in-sets were still changing, OR the ambient verify budget tripped and the
/// walk was abandoned (the v2 caller keeps its historical behavior of using the
/// partial map; the full-graph caller fails closed). On a budget trip the
/// caller's own post-generation checkpoint discards the function's whole
/// inventory, so no row built on a partial map can be kept — see the poll.
fn entry_versions_fixpoint(
    func: &VerifiableFunction,
    preds: &[Vec<usize>],
) -> (FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>>, bool) {
    use std::collections::BTreeSet;
    let n = func.body.blocks.len();
    // The gen-sets, the name universe and the per-block OUT tokens are a pure
    // function of `func` (see `EntryVersionGenSets`), so both callers share one
    // build. `None` = the ambient budget tripped mid-precompute; the whole
    // fixpoint is abandoned rather than run against a short gen-set.
    let Some(precomputed) = entry_version_gen_sets(func) else {
        return (FxHashMap::default(), false);
    };
    // verifier-perf (2026-09-16): the fixpoint runs over INTERNED ids, and each
    // visit reads only what a predecessor GAINED since the visit before.
    //
    // MEASURED on `tests/vcgen_entry_version_fixpoint.rs`'s 192-block rung: the
    // two runs of this loop were over half of VC generation, hashing name
    // strings and comparing token strings inside `BTreeSet<String>` searches,
    // and every round re-tested every (predecessor, name, token) triple although
    // a back-edge CFG needs about one round per block.
    //
    // WHY THIS IS THE SAME COMPUTATION.
    //  * Interning: the ids are a bijection with the strings (see
    //    `InternedGenSets`), so each membership test decides what the string
    //    test decided, and the map handed back is rebuilt from the same
    //    (name, token) pairs.
    //  * Deltas: the in-sets only GROW (see the accumulation note below). A
    //    pass-through pair `(nm, tok)` of `in_sets[p]` that block `b` already
    //    read on an earlier visit was added to `in_sets[b]` on that visit (or was
    //    already there), and is still there. So the only pairs that can be
    //    missing now are the ones `p` gained after that read, which are exactly
    //    `log[p][cursor..]`. A gen pair `(nm, gen_out[p][nm])` is constant, so it
    //    is present after the edge's first visit. Each visit therefore records
    //    the same non-empty-or-empty `additions` as the full re-scan, `changed`
    //    follows the same trajectory, and the round count and every budget
    //    poll below happen at the same points as before.
    let InternedGenSets { names, toks, gen_ids, gen_mask } = &precomputed.as_ref().interned;
    let pair = |nm: u32, tok: u32| (u64::from(nm) << 32) | u64::from(tok);
    // `in_sets[b]`: the (name, token) pairs reaching `b`'s entry.
    let mut in_sets: Vec<FxHashSet<u64>> = vec![FxHashSet::default(); n];
    // `log[b]`: the same pairs, in insertion order (append-only).
    let mut log: Vec<Vec<(u32, u32)>> = vec![Vec::new(); n];
    if n > 0 {
        for nm in 0..names.len() as u32 {
            in_sets[0].insert(pair(nm, ENTRY_TOKEN_ID));
            log[0].push((nm, ENTRY_TOKEN_ID));
        }
    }
    // `cursors[b][i]`: how much of `log[preds[b][i]]` block `b` has read; `None`
    // before the edge's first visit.
    let mut cursors: Vec<Vec<Option<usize>>> =
        preds.iter().map(|ps| vec![None; ps.len()]).collect();
    let mut additions: Vec<(u32, u32)> = Vec::new();
    let mut changed = true;
    let mut guard = 0usize;
    let mut budget_tripped = false;
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    while changed && guard < cap {
        changed = false;
        guard += 1;
        for b in 0..n {
            // BUDGET POLL (`-Ztrust-verify-function-budget-{ms,steps}`). This
            // loop had none, and `cap` alone is `8n^2 + 8n + 4096` ROUNDS over
            // `n` blocks x predecessor edges x live names — measured, a budgeted
            // run of `nn-core` sat 10+ minutes here with the budget LIVE and
            // correctly reporting 'timed out' elsewhere, because the checkpoint
            // that reports an overrun sits AFTER generation returns and
            // generation never returned.
            //
            // Per BLOCK, not merely per round: one round of a large CFG is
            // itself long enough to be the whole overrun.
            //
            // Breaking out is the ONLY sound degradation. A reaching-version
            // oracle may not hand back a truncated answer — a SHORT reaching
            // set is a short kill set, which lets a stale fact survive and
            // vacuously discharge a real obligation (a false PROVE) — so the
            // in-sets are left exactly as computed and the result is reported
            // NOT CONVERGED. `block_entry_versions_full_graph` already fails
            // closed on that (no `#e` is minted anywhere in the function), and
            // the caller in `rustc_mir_transform::trust_verify` observes the
            // spent budget at its existing checkpoint and applies the
            // discipline `d9d9d675e3` landed: advisory warns and substitutes
            // one COUNTED `Unknown` with the partial VCs discarded wholesale,
            // strict/certify/memory-safe keep the located hard error. This adds
            // a poll to an existing mechanism; it does not introduce a second.
            if trust_types::verify_budget::budget_exhausted() {
                budget_tripped = true;
                break;
            }
            // verifier-perf: ACCUMULATE into `in_sets[b]` instead of rebuilding
            // it. This was `let mut new_in = ...; for p { for (nm, s) in
            // out_of(p, &in_sets[p]) { new_in.entry(nm).or_default().extend(s) }
            // }; if new_in != in_sets[b] { in_sets[b] = new_in }` — which, for
            // EVERY (round x block x predecessor edge), materialized a whole
            // intermediate `FxHashMap<String, BTreeSet<String>>` (`out_of`),
            // deep-cloned every name and every token into a second one
            // (`new_in`), and then compared two full maps. That churn was the
            // #1 self-time leaf of a stack sample of the wedged `nn-core`
            // generator, with `HashMap<String, BTreeSet<String>>`'s
            // `reserve_rehash` and `insert` the #2 and #3.
            //
            // WHY ACCUMULATING IS EXACTLY THE SAME COMPUTATION. The transfer is
            // MONOTONE and the in-sets only ever GROW, so `new_in` was always a
            // SUPERSET of the `in_sets[b]` it replaced. Induction: every in-set
            // starts empty (block 0 starts at `entry_in`); block `b`'s stored
            // value is `F_b` applied to an EARLIER, componentwise-smaller state,
            // and `F_b` is monotone, so re-applying it to the current state can
            // only add. Hence `new_in == in_sets[b] union contributions`, and
            // `new_in != in_sets[b]` holds exactly when some contribution was
            // absent — which is what `additions` records. Block 0's `entry_in`
            // seed is already contained in `in_sets[0]` (it is its initial
            // value, and it only grows), so dropping the per-visit reseed drops
            // nothing.
            //
            // The two contribution families are `out_of`'s two arms verbatim:
            // for each name in `all_names`, the singleton `{gen_out[p][nm]}`
            // when `p` gens it, else `in_sets[p][nm]` when present. `gen_sets[p]`
            // is a subset of `all_names` by construction (`all_names` is their
            // union) and every in-set key is an `all_names` key by the same
            // induction, so iterating the two families visits exactly the pairs
            // `out_of` emitted and nothing else.
            //
            // The read phase borrows `in_sets` immutably throughout, so a
            // SELF-LOOP (`p == b`) reads block `b`'s pre-visit value — exactly
            // what `out_of(b, &in_sets[b])` did.
            for (i, &p) in preds[b].iter().enumerate() {
                let cur = &in_sets[b];
                let start = match cursors[b][i] {
                    Some(start) => start,
                    None => {
                        for &(nm, tok) in &gen_ids[p] {
                            if !cur.contains(&pair(nm, tok)) {
                                additions.push((nm, tok));
                            }
                        }
                        0
                    }
                };
                for &(nm, tok) in &log[p][start..] {
                    if !gen_mask[p].contains(&nm) && !cur.contains(&pair(nm, tok)) {
                        additions.push((nm, tok));
                    }
                }
                // Read BEFORE this visit's own additions are applied, so a
                // self-loop re-reads them next time (they are present by then).
                cursors[b][i] = Some(log[p].len());
            }
            if !additions.is_empty() {
                for (nm, tok) in additions.drain(..) {
                    if in_sets[b].insert(pair(nm, tok)) {
                        log[b].push((nm, tok));
                    }
                }
                changed = true;
            }
        }
        if budget_tripped {
            break;
        }
    }
    let map = func
        .body
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| {
            let mut block_map: FxHashMap<String, BTreeSet<String>> = FxHashMap::default();
            for &(nm, tok) in &log[i] {
                block_map
                    .entry(names[nm as usize].clone())
                    .or_default()
                    .insert(toks[tok as usize].clone());
            }
            (b.id, block_map)
        })
        .collect();
    // A budget trip is NOT convergence even when the interrupted round happened
    // to change nothing: the remaining blocks of that round were never visited.
    (map, !changed && !budget_tripped)
}

/// The predecessor-INDEPENDENT half of [`entry_versions_fixpoint`].
///
/// `preds` is consulted nowhere in building these three, yet the fixpoint runs
/// TWICE per function — once from [`block_entry_versions`] and once from
/// [`block_entry_versions_full_graph`], differing ONLY in the predecessor
/// relation — so they were built identically twice. The second build is the
/// expensive one to repeat: `gen_out` is an O(blocks x names x statements)
/// `stmt_writes_name` scan.
struct EntryVersionGenSets {
    /// The gen-sets, name universe and OUT tokens, as interned ids.
    interned: InternedGenSets,
}

/// Id of [`ENTRY_VERSION_SENTINEL`] in [`InternedGenSets::toks`].
const ENTRY_TOKEN_ID: u32 = 0;

/// The fixpoint's inputs with every name and token replaced by a dense id.
///
/// `names` is the fixpoint's whole name universe (the union of every block's
/// `block_written_names`), each name exactly once; `toks` is every distinct
/// token, each exactly once, with the entry sentinel at [`ENTRY_TOKEN_ID`]. Two
/// ids are equal iff their strings are equal, so a set of ids and the set of
/// the strings they stand for answer every membership query identically.
struct InternedGenSets {
    names: Vec<String>,
    toks: Vec<String>,
    /// Each block's `(name, OUT token)` pairs: one per gen'd name, the token
    /// constant across the fixpoint.
    gen_ids: Vec<Vec<(u32, u32)>>,
    /// The name ids of `gen_ids[b]`, for the pass-through skip.
    gen_mask: Vec<FxHashSet<u32>>,
}

impl InternedGenSets {
    fn new(gen_sets: &[FxHashSet<String>], gen_out: &[FxHashMap<String, String>]) -> Self {
        let mut names: Vec<String> = Vec::new();
        let mut name_ids: FxHashMap<&str, u32> = FxHashMap::default();
        let mut toks: Vec<String> = vec![ENTRY_VERSION_SENTINEL.to_string()];
        let mut tok_ids: FxHashMap<&str, u32> = FxHashMap::default();
        tok_ids.insert(ENTRY_VERSION_SENTINEL, ENTRY_TOKEN_ID);
        let mut gen_ids: Vec<Vec<(u32, u32)>> = Vec::with_capacity(gen_sets.len());
        let mut gen_mask: Vec<FxHashSet<u32>> = Vec::with_capacity(gen_sets.len());
        for (set, out) in gen_sets.iter().zip(gen_out) {
            let mut pairs: Vec<(u32, u32)> = Vec::with_capacity(set.len());
            let mut mask: FxHashSet<u32> = FxHashSet::default();
            for nm in set {
                let nm_id = *name_ids.entry(nm.as_str()).or_insert_with(|| {
                    names.push(nm.clone());
                    (names.len() - 1) as u32
                });
                let tok = &out[nm];
                let tok_id = *tok_ids.entry(tok.as_str()).or_insert_with(|| {
                    toks.push(tok.clone());
                    (toks.len() - 1) as u32
                });
                pairs.push((nm_id, tok_id));
                mask.insert(nm_id);
            }
            gen_ids.push(pairs);
            gen_mask.push(mask);
        }
        InternedGenSets { names, toks, gen_ids, gen_mask }
    }
}

/// Build (or reuse) the precompute above. `None` iff the ambient verify budget
/// tripped part-way, in which case NOTHING is memoized — see
/// the retired `havoc_memo::entry_gen_sets` slot for why a truncated one was never
/// stored or returned.
fn entry_version_gen_sets(func: &VerifiableFunction) -> Option<std::rc::Rc<EntryVersionGenSets>> {
    (|| {
        // BUDGET POLL, per block: `block_written_names` is a whole-block walk that
        // consults the function-wide deref-store havoc set, so this `map` is its own
        // overrun channel and had none.
        let mut gen_sets: Vec<FxHashSet<String>> = Vec::with_capacity(func.body.blocks.len());
        for b in func.body.blocks.iter() {
            if trust_types::verify_budget::budget_exhausted() {
                return None;
            }
            gen_sets.push(block_written_names(func, b));
        }
        // Precompute each block's OUT token per gen'd name (constant across the
        // fixpoint): the last statement writing/havocing the name, else a terminator
        // marker `s{b}_t` for a name the block's TERMINATOR defines (Call dest).
        let mut gen_out: Vec<FxHashMap<String, String>> =
            Vec::with_capacity(func.body.blocks.len());
        for (bi, b) in func.body.blocks.iter().enumerate() {
            // BUDGET POLL: this walk is O(names x statements) per block with a
            // whole-block `stmt_writes_name` scan inside, so it is its own
            // overrun channel. Abandoning it returns `None` all the way out —
            // a PARTIAL `gen_out` is not a cheaper answer, it is a WRONG one
            // (a missing OUT token is a missing kill), so it is never built,
            // never cached, and never handed to the fixpoint.
            if trust_types::verify_budget::budget_exhausted() {
                return None;
            }
            // The block's TERMINATOR writes (a `Call` dest + escaping `&mut`s) run
            // AFTER every statement, so a name it reassigns has its OUT token pinned
            // to the terminator marker `s{b}_t` — DISTINCT from any statement
            // establish token, so a fact established at a statement and threaded to a
            // successor is name-disjoint from the post-terminator value. Without this
            // the OUT token would be the last STATEMENT write (`stmt_writes_name`
            // cannot see the terminator), and a stale pre-call fact would re-unify
            // with the post-call read (the case `terminator_def_names` defends).
            let term_defs = terminator_def_names(func, b);
            // The per-BLOCK poll above cannot interrupt ONE block: this is
            // O(names x statements) with a whole-block `stmt_writes_name` scan
            // inside each probe, so a single wide block is the whole overrun.
            // MEASURED 2026-09-09 on `first-party/ty`'s tla-cli (seal
            // trust-e0d24ca8, the run that first got PAST the once-reentrancy
            // ICE): both binaries sat at 100% CPU for 25 minutes with this
            // closure as the deepest frame, having emitted nothing for 20 of
            // them. Written as loops so the poll reaches every NAME and every
            // STATEMENT probe. Degradation is unchanged and is the strong one:
            // `None` all the way out — a PARTIAL `gen_out` is not a cheaper
            // answer but a WRONG one (a missing OUT token is a missing kill),
            // so it is never built, never cached, never handed to the fixpoint.
            let mut out: FxHashMap<String, String> = FxHashMap::default();
            for nm in gen_sets[bi].iter() {
                if trust_types::verify_budget::budget_exhausted() {
                    return None;
                }
                let tok = if term_defs.iter().any(|t| write_rebinds(t, nm)) {
                    format!("s{}_t", b.id.0)
                } else {
                    let mut found = None;
                    for k in (0..b.stmts.len()).rev() {
                        if trust_types::verify_budget::budget_exhausted() {
                            return None;
                        }
                        if stmt_writes_name(func, b, k, nm) {
                            found = Some(k);
                            break;
                        }
                    }
                    match found {
                        Some(k) => format!("s{}_{k}", b.id.0),
                        None => format!("s{}_t", b.id.0),
                    }
                };
                out.insert(nm.clone(), tok);
            }
            gen_out.push(out);
        }
        Some(EntryVersionGenSets { interned: InternedGenSets::new(&gen_sets, &gen_out) })
    })()
    .map(std::rc::Rc::new)
}

/// The ROOT of a place name: the prefix before its first projection separator
/// (`.`, `[`, `*` or `@` — [`crate::is_projection_segment_lead`], the SAME set
/// [`path_defs::place_names_overlap`] reads; the two must agree or the lemma below
/// fails for a downcast payload `r@1.0`), or the whole name when it has none.
///
/// `place_names_overlap(a, b)` implies `place_root(a) == place_root(b)`, so a
/// name-to-root bucketing never separates two overlapping names:
///  * `a == b`: trivially.
///  * one is a projection descendant, `long = anc + sep + ..` with `sep` a
///    separator: when `anc` contains a separator, `long`'s first one is at the
///    same position; when it has none, `long`'s first one is at `anc.len()` and
///    both roots are `anc`.
///  * symbolic-index aliasing, `a[..i] == b[..j]` with `i`, `j` the first `[`:
///    both roots are the prefix of that common string before its first `.` or
///    `*`, or the whole common string when there is none.
///
/// The separators are ASCII, so the byte position is a char boundary.
pub(crate) fn place_root(name: &str) -> &str {
    match name.bytes().position(crate::is_projection_segment_lead) {
        Some(i) => &name[..i],
        None => name,
    }
}

fn names_by_root<'a>(names: impl Iterator<Item = &'a String>) -> FxHashMap<String, Vec<String>> {
    let mut unique: Vec<&String> = names.collect();
    unique.sort_unstable();
    unique.dedup();
    let mut by_root: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for name in unique {
        by_root.entry(place_root(name).to_string()).or_default().push(name.clone());
    }
    by_root
}

/// EVERY root bucket that can hold a tracked WRITTEN name `k` with
/// [`path_defs::write_rebinds`]`(k, name)` true — `name`'s own root, PLUS the
/// fallback spelling `_<l>` of every `[_<l>]` index segment `name` carries.
///
/// MERGE HAZARD, 2026-09-17 (rounds A9/A10 meeting the verifier-perf root index).
/// The bucket index's own lemma — "`place_names_overlap(a, b)` implies
/// `place_root(a) == place_root(b)`", proved in [`place_root`]'s doc and pinned by
/// `version_oracle_index_tests::place_root_never_separates_overlapping_names` — is
/// a statement about the SYMMETRIC overlap relation ONLY. The union loops below
/// scan the DIRECTIONAL [`path_defs::write_rebinds`], whose second disjunct
/// [`path_defs::write_covers_index_segment`] relates names in DIFFERENT buckets:
/// the written `_3` has `place_root("_3") == "_3"`, the read `s*[_3]` has
/// `place_root("s*[_3]") == "s"`. Substituting `write_rebinds` for
/// `place_names_overlap` inside a `place_root(name)`-only bucket loop therefore
/// SILENTLY drops the index-segment channel and re-opens the measured false proof
/// that channel closes (`index_local_min_bug`: two reads of `s*[_3]__slice_len`
/// across a reseat `j = k` tied as ONE unversioned name, and a panicking program
/// PROVED kernel-certified — see [`path_defs::write_rebinds`]). Hence the extra
/// candidate per index segment; with it the enumeration is COMPLETE for both
/// disjuncts:
///  * `place_names_overlap(k, name)` ⇒ `place_root(k) == place_root(name)`, so `k`
///    is in the first bucket;
///  * `write_covers_index_segment(k, name)` ⇒ `k` IS a fallback `_<digits>` and
///    `name` carries the segment `[k]`, and `place_root(k) == k` (a fallback holds
///    no separator), so `k` is in the bucket this enumeration yields for that
///    segment.
///
/// The segment scan mirrors [`path_defs::write_covers_index_segment`]'s own scan
/// exactly — every `[`, the text up to the first following `]`, whole-segment,
/// so `[_3]` never answers for `[_30]` and a nested `a[b[_3]]` still yields `_3`.
/// A root may be visited twice (`name == "_3[_3]"`); the callers union into a set,
/// so that is idempotent. Alloc-free: this sits on the version oracle's hot path.
fn for_each_candidate_root(name: &str, mut visit: impl FnMut(&str)) {
    visit(place_root(name));
    let mut from = 0usize;
    while let Some(off) = name[from..].find('[') {
        let start = from + off + 1;
        if let Some(close) = name[start..].find(']') {
            let seg = &name[start..start + close];
            if let Some(digits) = seg.strip_prefix('_')
                && !digits.is_empty()
                && digits.bytes().all(|b| b.is_ascii_digit())
            {
                visit(seg);
            }
        }
        from = start;
    }
}

/// Every tracked name in `by_root` that [`path_defs::write_rebinds`] relates to the
/// READ name `name`, visited once per bucket hit. The bucket-restricted twin of
/// `for (k, _) in em { if write_rebinds(k, name) { .. } }`: identical answers by
/// [`for_each_candidate_root`]'s completeness argument, without the full scan.
fn for_each_rebinding_name<'a>(
    by_root: &'a FxHashMap<String, Vec<String>>,
    name: &str,
    mut visit: impl FnMut(&'a String),
) {
    for_each_candidate_root(name, |root| {
        for k in by_root.get(root).into_iter().flatten() {
            // `k` is a tracked WRITTEN name; `name` the read — directional.
            if write_rebinds(k, name) {
                visit(k);
            }
        }
    });
}

/// The RETIRED statement-granular version oracle (dense per-block maps from the two
/// reaching-version fixpoints), kept verbatim as the differential the SSA oracle is
/// checked against.
pub(crate) struct LegacyStmtVersions {
    entry: FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>>,
    /// UNWIND-INCLUSIVE sibling of `entry` (see `block_entry_versions_full_graph`):
    /// predecessor edges additionally include every `UnwindEdge::cleanup_target()`
    /// edge, mirroring `v2_path_def_fixpoint`'s enqueue set. Consulted ONLY by the
    /// `#e` mint gate; `None` = the fixpoint did not converge, and the gate fails
    /// closed (no `#e` anywhere in this function).
    entry_full: Option<FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>>>,
    /// Every name tracked anywhere in `entry`, bucketed by [`place_root`]. Only
    /// the bucket of a query's root can hold a name that
    /// [`path_defs::place_names_overlap`] relates to it (see [`place_root`]), so the
    /// overlap unions below scan that bucket instead of every tracked name.
    ///
    /// Those unions run the DIRECTIONAL [`path_defs::write_rebinds`], which is
    /// WIDER than that overlap and does cross buckets: they enumerate their
    /// candidate buckets through [`for_each_candidate_root`], never through
    /// `place_root` alone. Its MERGE HAZARD note is the argument.
    entry_by_root: FxHashMap<String, Vec<String>>,
    /// The same index over `entry_full`'s names.
    entry_full_by_root: FxHashMap<String, Vec<String>>,
    /// `version_token_at`'s INTER-BLOCK arm, memoized per `(block, name)`. That
    /// arm reads only the immutable `entry` map, so its answer is a pure function
    /// of the pair; the sampled 192-block rung asked it once per `Var` occurrence
    /// of every renamed formula.
    inter_block_tokens: std::cell::RefCell<FxHashMap<BlockId, FxHashMap<String, Option<String>>>>,
    /// The retired `v2_may_reassigned_per_block` map, built on first probe.
    may_reassigned: std::cell::OnceCell<FxHashMap<BlockId, FxHashSet<String>>>,
    func: VerifiableFunction,
}

impl LegacyStmtVersions {
    /// Build the retired oracle (both fixpoints) for `func`. Unmemoized: it exists only
    /// as the differential.
    pub(crate) fn build(func: &VerifiableFunction) -> Self {
        let entry = block_entry_versions(func);
        let entry_full = block_entry_versions_full_graph(func);
        let entry_by_root = names_by_root(entry.values().flat_map(|em| em.keys()));
        let entry_full_by_root = names_by_root(
            entry_full.iter().flat_map(|full| full.values()).flat_map(|em| em.keys()),
        );
        LegacyStmtVersions {
            entry,
            entry_full,
            entry_by_root,
            entry_full_by_root,
            inter_block_tokens: Default::default(),
            may_reassigned: Default::default(),
            func: func.clone(),
        }
    }

    /// Whether both fixpoints ran to convergence (no budget trip): only then is the
    /// retired oracle's answer the reference.
    pub(crate) fn converged(&self) -> bool {
        self.entry_full.is_some()
    }

    /// The retired kill-set membership probe over the least fixpoint of the retired
    /// may-reassigned dataflow (`v2_may_reassigned_per_block`, whose reference form
    /// has no step cap and so no overflow fallback to answer with).
    pub(crate) fn may_reassigned_rebinds(&self, block: BlockId, name: &str) -> bool {
        let map = self.may_reassigned.get_or_init(|| v2_may_reassigned_per_block(&self.func));
        map.get(&block).is_some_and(|set| set.iter().any(|n| dest_write_rebinds(n, name)))
    }

    pub(crate) fn entry_map(&self) -> &FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>> {
        &self.entry
    }

    pub(crate) fn entry_full_map(
        &self,
    ) -> Option<&FxHashMap<BlockId, FxHashMap<String, BTreeSet<String>>>> {
        self.entry_full.as_ref()
    }

    /// `#token` for `name` read at `(block, stmt_idx)`, or `None` when the value
    /// there is the entry/parameter value (so unversioned names stay byte-identical
    /// on the flip). A same-block write in `stmts[..stmt_idx]` versions it; a write
    /// LATER in the block does NOT (the block-level oracle gets this wrong).
    pub(crate) fn version_token_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<String> {
        // Trust (lane-A CSE): id==index invariant (held by direct `blocks[id.0]`
        // indexing elsewhere) lets the linear find be an O(1) indexed lookup. The
        // `.filter(|b| b.id == block)` keeps it BEHAVIORALLY IDENTICAL — same
        // `Option<&BasicBlock>`, same `None` were the invariant ever violated.
        let bb = func.body.blocks.get(block.0).filter(|b| b.id == block)?;
        // In-block write before the read point wins (the live value at stmt_idx).
        // Trust #soundness (callee-write false-accept sweep): the gate is
        // OVERLAP-aware, matching the `stmt_writes_name` token search below — the
        // old exact-name `.contains(name)` let an overlapping statement write
        // (whole-place `s = ..` before a field read `s.v`; a havoc of `r` before
        // a pointee read `r*`) pass the search yet be gated out here, silently
        // falling through to the entry map with the write invisible.
        // Trust #soundness (2026-08-26): the gate must admit EXACTLY what the
        // `stmt_writes_name` search below admits, which is
        // `place_names_overlap(dest, name) || write_covers_derived_slice_len(dest, name)`.
        // Testing only the first left a write of `p` invisible for the DERIVED name
        // `p__slice_len` (`place_names_overlap("p", "p__slice_len")` is FALSE — `_` is
        // not a projection separator), so a same-block reassignment fell through to the
        // inter-block entry map and the read kept its PRE-reassignment token.
        //
        // MEASURED via TRUST_DUMP_V2_VC on
        // `let mut p=&raw const *sa; if sa.len()>2 { p=&raw const *sb; (*p)[2] }`:
        //     Eq(p__slice_len#s0_1, sa__slice_len)   <- tie, at its establish token
        //     Eq(p#s2_3, _7)                         <- reassignment DOES bump `p`
        //     Eq(_10, p__slice_len#s0_1)             <- but the READ still reads #s0_1
        // The base name is versioned and the derived one is not, so the stale length
        // unified with the read and the bounds row shipped `proved` while the binary
        // panics "index out of bounds: the len is 1 but the index is 2".
        //
        // Mirroring the search is what makes this safe rather than a widening: the
        // `s{b}_pre` phantom-token arm below (the hazard `writes_until`'s own doc warns
        // about) is unreachable for a name admitted here, because the search tests the
        // same disjunction statement-by-statement and must therefore find one.
        // Trust (round A10): `dest_write_rebinds(written, read)` — the directional
        // relation (`place_names_overlap` + the derived `__slice_len` and `[_l]`
        // index-segment channels), the same one `stmt_writes_name` tests
        // statement-by-statement for a destination.
        if writes_until(func, bb, stmt_idx).iter().any(|w| dest_write_rebinds(w, name)) {
            // P-A: the LATEST single statement < stmt_idx that ITSELF writes an
            // overlap of `name` gives a point-distinct token. Test each statement
            // directly (`stmt_writes_name`), NOT the cumulative `writes_until` delta —
            // that delta is nonzero only at the FIRST write, so two same-block writes
            // (and def-then-deref-havoc) collapsed to one token, defeating the
            // statement-granular distinction the oracle exists to provide.
            let j = (0..stmt_idx.min(bb.stmts.len()))
                .rev()
                .find(|&k| stmt_writes_name(func, bb, k, name));
            if let Some(k) = j {
                return Some(format!("s{}_{k}", block.0));
            }
            // The gate fired but NO statement in the prefix writes `name`. Fall
            // through ONLY when the sole reason it fired is the derived
            // `__slice_len` channel -- i.e. nothing in the union `write_rebinds`
            // the name under the narrow relation. Every other divergence keeps the
            // fail-closed phantom, because `is_versioned_stale_at` decides
            // staleness with `write_rebinds` over this same union: a name it calls
            // stale must NOT be minted bare, or the fact's var unifies with the
            // read and the guard bound transfers. That mint-consistency invariant
            // is pinned by `flip_matches_kill_stmt`, which caught a broader form
            // of this fix with 4 disagreements on `sem_stale_blockdef`. Under this
            // condition staleness can come only from the ENTRY set, which the
            // inter-block lookup below consults through that same relation and
            // answers with a real token -- so a stale name is never minted bare.
            let admitted_only_via_slice_len =
                !writes_until(func, bb, stmt_idx).iter().any(|w| write_rebinds(w, name));
            if !admitted_only_via_slice_len {
                return Some(format!("s{}_pre", block.0));
            }
            // Trust #false-refutation (2026-09-21, WRITE-THEN-READ on a `&mut [T]`):
            // the gate above is an OVER-APPROXIMATE pre-filter, and where the
            // statement-granular search disagrees with it, the SEARCH is right. This
            // used to mint `s{b}_pre` here, and that phantom is the bug.
            //
            // The two oracles were not testing the same thing, and this file already
            // says which is correct. `writes_until` unions two provenances: direct
            // destinations, which `extend_with_derived_slice_len` DOES extend with
            // `{dest}__slice_len`, and the opaque deref-store HAVOC names, which it
            // deliberately does NOT -- see that function's doc: "Apply to the
            // DIRECT-WRITE channel only ... extending those would havoc a `&mut [T]`
            // parameter's live tie at every call, which is the false REFUTATION
            // `write_covers_derived_slice_len` exists to prevent." The gate then
            // tested `dest_write_rebinds` -- which CARRIES that `__slice_len` channel
            // -- across the whole union, so a havoc name `s` re-admitted the derived
            // `s__slice_len` that the set builder had withheld. The search does not:
            // its deref-store arm tests `write_rebinds`, honouring
            // `write_covers_derived_slice_len`'s ANCESTOR-ONLY ruling that "an
            // ELEMENT/pointee store (`dst*[i] = v`, a DESCENDANT of `dst`) preserves
            // the length metadata and must NOT count as a write of `dst__slice_len`".
            //
            // MEASURED on stage1 before the fix:
            //     pub fn f(s: &mut [u8], i: usize) -> u8 {
            //         if i < s.len() { s[i] = 7; s[i] } else { 0 }   // 1 proved, 1 FAILED
            //     }
            // the model binding the true `s__slice_len = 1` beside an unpinnable
            // phantom `s__slice_len#s2_pre = 0`, so the guard was pruned from the
            // bounds VC. Four controls isolate the store as the sole cause: the same
            // body with NO store proves; reading BEFORE the store proves; a local
            // `[u8; 4]` (no deref store at all) proves; and re-reading `s.len()` after
            // the store proves. `tests/guarded_mut_slice_index.rs` missed it by one
            // statement -- it pins the guarded STORE, never a read after it.
            //
            // SOUND, and this is the direction that needs the argument: falling
            // through is NOT "assume unwritten". When no statement in
            // `stmts[..stmt_idx]` writes `name`, the live value at the read IS the
            // block-entry value, so the inter-block reaching map below is the
            // CORRECT token -- it was the phantom that nothing could pin. And the
            // guard above is what keeps that true. Staleness is decided by
            // `is_versioned_stale_at` with `write_rebinds` over `writes_until` UNION
            // the entry-reassigned set. Under `admitted_only_via_slice_len` nothing
            // in `writes_until` rebinds the name under that relation, so staleness
            // can come only from the ENTRY set -- and the inter-block lookup below
            // consults that same set through the same overlap relation, so it
            // returns a real token rather than a bare read. A stale name is
            // therefore never minted bare here.
            //
            // AN EARLIER, BROADER FORM OF THIS FIX WAS WRONG, and the tree caught
            // it. Falling through whenever the per-statement search disagreed --
            // justified by an enumeration claiming the `__slice_len`-over-havoc
            // channel was the ONLY possible divergence -- produced 4 disagreements
            // on `sem_stale_blockdef` in `flip_matches_kill_stmt`, the
            // mint-consistency witness: `flip_stale && version_token_at(..).is_none()`
            // is exactly the false-accept class that once let a guard bound transfer
            // across a callee write. So the enumeration was incomplete, there IS a
            // second divergence class, and the narrow guard above is what separates
            // them. Left MEASURABLE rather than asserted: set
            // `TRUST_VERSION_GATE_TRACE` to print every name reaching this point.
            if crate::trust_vcgen_env_var_present("TRUST_VERSION_GATE_TRACE") {
                eprintln!(
                    "[VERSION_GATE] fall-through: fn={} block={} stmt={stmt_idx} name={name}",
                    func.name, block.0,
                );
            }
        }
        // Else the inter-block reaching set at block entry. The tokens are already
        // statement-granular `s{pred}_{k}` strings (`e` = entry/param value).
        //
        // Trust #soundness (callee-write false-accept sweep — THE CORE FIX): the
        // lookup is an OVERLAP UNION, not an exact-key get. The confirmed silent
        // false-accept: `if *r < 1000 { bump(r); t = *r + 1 }` where `bump` sets
        // `*r = u32::MAX` — the Call havocs the BASE name "r" (entry map of the
        // successor holds {"r" -> {s1_t}}), but the post-call READ spells "r*";
        // the exact-key get missed it, both `*r` reads stayed the SAME bare SMT
        // var, and the guard bound falsely transferred across the call (verified
        // "1 proved" yet panics at runtime). With the overlap union, the
        // entry-versioned base "r" versions the pointee read to `r*#s1_t`,
        // name-disjoint from the pre-call bare guard read — the transfer is
        // severed. Deterministic per (block, name): the BTreeSet-sorted join
        // gives two post-call reads at the same block ONE shared token, so a
        // post-call guard still discharges a post-call use (no over-splitting).
        // An all-entry union stays `None` (bare, never-havoced parameter reads
        // stay byte-identical). A MIXED union keeps the entry sentinel IN the
        // join (`e_s1_t`): a partially-entry-valued read has a DIFFERENT
        // reaching-value set than a definitely-post-write read (`s1_t`), and
        // collapsing the two names would assert a false cross-path equality.
        //
        // Trust: 2026-09-16 (round A11), RESTATED 2026-09-17 (round A12) — WHAT A
        // JOINED TOKEN MAY CARRY. The union below ranges over every tracked name
        // `k` that rebinds `name`, so its components come from DIFFERENT tracked
        // names — an own write of `s*[_4]` (`s1_0`), the index local's reseat
        // `_4`/`j` (`s1_1`), the havoc of the base `s` — and the joined spelling
        // `s*[_4]#s1_0_s1_1` is minted at the READ side, by this rename. A
        // DEFINITION does reach it: `conjoin_preconditions_versioned_recorded` /
        // `version_rename_at` re-spell a predecessor's path def at the successor's
        // use point, and when that def is the predecessor's LAST write of `name`
        // it lands on exactly this union (`Eq(s*[_4]#s3_1_s3_2, 3)` on the sound
        // `br_store_ctl` shape: `j = k` at `s3_1`, the store at `s3_2`). The
        // round-A11 wording "no definition may ever be spelled onto a joined
        // token" was therefore not what the code enforces. The guarantee that IS
        // enforced, and that makes the landing sound, is: THE DEF'S WRITE IS THE
        // LAST WRITE OF EVERY UNION COMPONENT ON EVERY PATH into the successor.
        // Two premises carry it:
        //  (1) the KILLS. `v2_path_def_fixpoint` threads a block's own defs in
        //      statement order and kills each by every later write of the block
        //      (`thread_own_defs_in_statement_order`), and the extraction drops a
        //      def whose subject a later statement rebinds
        //      (`extract_block_definitions_until_impl`); so a def that survives to
        //      the boundary is one no later write of the predecessor rebinds — its
        //      write IS the last one of every component the predecessor
        //      contributes. The MEASURED A10 violation (`Eq(s*[_4]#s1_0_s1_1, 3)`
        //      on `store_reseat_read_bug`, the reseat AFTER the store) is
        //      impossible by (1) alone.
        //  (2) a CORRECT NAME for the def's destination. (1) kills by NAME, so it
        //      is only as good as the spelling of the write. A store through a
        //      reference `*r = 3` is spelled by `r`'s folded referent
        //      (`lib.rs::resolve_referent`), and until round A12 that fold was
        //      taken whatever had happened to the referent's locals since the
        //      borrow: `let r = &mut s[j]; j = k; *r = 3` spelled the store
        //      `s*[_4]` AFTER the reseat, so (1) saw the store as the last write
        //      of `s*[_4]` — which it is, of the NAME — while the storage it hit
        //      was `s[0]`, and the def landed on the read's union
        //      (`br_store_bug`, `-O1`, PROVED kernel-certified on a panicking
        //      program). `referent_fold::is_stable` now refuses the fold whenever a
        //      guard of the referent (a `Deref`-prefix pointer, an `Index` local)
        //      is rebound between the borrow and a use, so the store is spelled
        //      opaque (`r*`) and havocs instead of defining; (2) is what makes
        //      (1)'s "last write" a statement about STORAGE and not only about a
        //      spelling.
        // Establish-versioned defs (`version_block_def_at_establish`) are pinned
        // at their own statement and carry a single-component `s{b}_{k}` token,
        // never a join.
        if let Some(memo) = self.inter_block_tokens.borrow().get(&block)
            && let Some(hit) = memo.get(name)
        {
            return hit.clone();
        }
        let token = self.inter_block_token(block, name);
        self.inter_block_tokens
            .borrow_mut()
            .entry(block)
            .or_default()
            .insert(name.to_string(), token.clone());
        token
    }

    /// The inter-block arm of [`Self::version_token_at`], uncached: the reaching set,
    /// spelled as the SSA oracle spells it (`version_ssa::spell_token_texts` — the
    /// retired `_`-joined list when it is short, a collision-checked hash when not), so
    /// the differential compares SETS through one spelling.
    pub(crate) fn inter_block_token(&self, block: BlockId, name: &str) -> Option<String> {
        let toks = self.inter_block_set(block, name)?;
        super::version_ssa::spell_token_texts(toks.iter().map(String::as_str))
    }

    /// [`Self::inter_block_token`] in the RETIRED spelling (the sorted `_`-joined list
    /// at every length) — the reference the spelling's partition identity is checked
    /// against.
    #[cfg(test)]
    pub(crate) fn inter_block_token_retired(&self, block: BlockId, name: &str) -> Option<String> {
        let toks = self.inter_block_set(block, name)?;
        if toks.is_empty()
            || toks == std::collections::BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()])
        {
            return None;
        }
        Some(toks.iter().cloned().collect::<Vec<_>>().join("_"))
    }

    /// The union the inter-block arm spells.
    fn inter_block_set(&self, block: BlockId, name: &str) -> Option<BTreeSet<String>> {
        let em = self.entry.get(&block)?;
        let mut toks: BTreeSet<String> = std::collections::BTreeSet::new();
        // The union ranges over the DIRECTIONAL `write_rebinds` (a tracked WRITTEN
        // name `k` against the read `name`), restricted to the candidate root
        // buckets. `name`'s OWN root bucket is not enough on its own — see
        // `for_each_candidate_root`'s MERGE HAZARD note.
        for_each_rebinding_name(&self.entry_by_root, name, |k| {
            if let Some(s) = em.get(k) {
                toks.extend(s.iter().cloned());
            }
        });
        Some(toks)
    }

    /// True iff `block`'s entry-version map TRACKS a name overlapping `name`.
    ///
    /// Where it does NOT, [`Self::version_token_at`]'s `None` does not mean "the
    /// entry value". Since 2026-08-30 `block_entry_versions` builds its
    /// predecessor lists from `full_graph_terminator_targets` (unwind-inclusive,
    /// matching the fact-transport graph), so a cleanup-only-reachable block now
    /// versions its reads like any other; but a block unreachable from bb0 across
    /// full-graph edges still gets an EMPTY map, and a never-written name is
    /// simply untracked. A caller that reads a bare (or `#e`) spelling AS the
    /// entry value must consult this first.
    // MERGE NOTE (integrate-e6-perfield-20260831): the non-test caller went with
    // the other line; the tie-subsumption tests still exercise it.
    pub(crate) fn entry_map_covers(&self, block: BlockId, name: &str) -> bool {
        self.entry
            .get(&block)
            .is_some_and(|em| em.keys().any(|tracked| write_rebinds(tracked, name)))
    }

    /// THE `#e` MINT GATE's oracle: true iff EVERY runtime path into `block` —
    /// normal or unwind — delivers `name`'s function-ENTRY value, i.e. the
    /// UNWIND-INCLUSIVE reaching-version union at `block`'s entry is exactly
    /// `{e}`. Same overlap-union lookup as `version_token_at`'s inter-block arm,
    /// but over the full-graph map: `{e}` tokens are seeded only at bb0 and any
    /// gen replaces them, so with unwind edges IN the predecessor relation an
    /// exactly-`{e}` union means no writer of `name` on ANY path into the block.
    ///
    /// Fails closed three ways, each toward "not entry" (no `#e` mint):
    ///  * the full-graph fixpoint hit its step cap (`entry_full` is `None`);
    ///  * `block` is unreachable from bb0 across full-graph edges (empty union);
    ///  * ANY overlapping tracked name contributes a non-`e` token.
    pub(crate) fn full_graph_union_is_entry_only(&self, block: BlockId, name: &str) -> bool {
        let Some(full) = &self.entry_full else { return false };
        let Some(em) = full.get(&block) else { return false };
        let mut toks: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        // Same union as `inter_block_token`, over the full-graph map: the
        // DIRECTIONAL `write_rebinds` over the candidate root buckets. The
        // `place_root(name)` bucket alone would miss the `[_l]` index-segment
        // channel and mint `#e` for a read some reseat of `_l` rebinds — see
        // `for_each_candidate_root`'s MERGE HAZARD note.
        for_each_rebinding_name(&self.entry_full_by_root, name, |tracked| {
            if let Some(s) = em.get(tracked) {
                toks.extend(s.iter().map(String::as_str));
            }
        });
        toks.len() == 1 && toks.contains(ENTRY_VERSION_SENTINEL)
    }

    /// Overlap-aware staleness at a precise point: is a fact whose sole free var is
    /// `name` stale at `(block, stmt_idx)`? True iff some name written in
    /// `stmts[..stmt_idx]` OR entry-versioned overlaps `name`.
    pub(crate) fn is_versioned_stale_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> bool {
        let entry_only = std::collections::BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]);
        // Trust (lane-A CSE): id==index invariant → O(1) indexed lookup; the
        // `.filter` preserves the exact `None`-on-violation behavior of the find.
        let Some(bb) = func.body.blocks.get(block.0).filter(|b| b.id == block) else {
            return false;
        };
        let mut redefined = writes_until(func, bb, stmt_idx).as_ref().clone();
        if let Some(em) = self.entry.get(&block) {
            redefined.extend(em.iter().filter(|(_, v)| **v != entry_only).map(|(k, _)| k.clone()));
        }
        redefined.iter().any(|n| write_rebinds(n, name))
    }
}
