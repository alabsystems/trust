// trust_vcgen/generate/recipes.rs: block-def recipes, and the rows that join as Spines
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust (T3 L4, C08, 2026-10-17; plan `docs/design/2026-10-11-t3-l4-commit-plan.md` C08
//! and L4-RECIPE-1, design `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md`
//! D-VC-3): a generation that writes into a context joins its block-def rows as Spine rows.
//!
//! # Recipes
//!
//! The three block-def builders (`v2_formula_with_block_defs_at_point_recorded`,
//! `v2_formula_with_slice_len_ties_recorded`, `v2_formula_with_copy_ties_at_point_recorded`)
//! combine a block's candidate facts with a row's body by the relevance rule of
//! `combine_relevant_block_defs_recorded`. While a generation that writes into its caller's
//! context runs ([`RecipeScope`], [`Spines::Join`]), each combination is recorded in this
//! thread's recipe log ([`record`]): the candidates, and how many of them the rule kept,
//! under the combined formula's [`shape_key`]. The builders still build the conjunction and
//! its kept list, which stay authoritative (L4-ORACLE-1); the recipe is a copy of the
//! candidates beside them, dropped with the generation. A generation whose context drops
//! with it (`generate_vcs`) records nothing ([`Spines::Skip`]): no one reads its Spines.
//!
//! Consecutive combinations share one candidate list ([`CandidateList`]) when one's
//! candidates are a prefix of the other's: the rows of one block at one point, and a
//! block's rows at later points, whose candidates extend the earlier ones statement by
//! statement. A recipe is a prefix of its list, so a dense block's log holds its candidates
//! once, not once per row (L4-C08-2). A block whose earlier facts change at a later point
//! (a bare read rewritten before it) starts a list of its own.
//!
//! A shape key hashes a formula's structure and its literals, and each variable's name up
//! to its first `#`. SSA version-token normalization (`normalize_ssa_version_tokens`) only
//! renames `base#token` to `base`, so a row that was normalized after its combination was
//! recorded (the safety walk normalizes its rows, the sink normalizes every row) has the key
//! its raw combination was recorded under. The key only finds candidates; it decides
//! nothing.
//!
//! # From a recipe to a Spine row
//!
//! The sink looks a row's formula up as the row joins, before the per-row passes, and tries
//! the Spine after them ([`join_block_def_row`]):
//!
//! 1. a row the passes made `UnsupportedMir` (the havoc decline, the self-reference
//!    refusal), or rewrote by term-`Ite` elimination, stays Node;
//! 2. the row's formula must have the recipe's shape: `And([facts.., body])` with as many
//!    facts as the rule kept, or the body alone when it kept none;
//! 3. the candidates are normalized one by one (a per-name renaming, so normalizing a
//!    conjunct is normalizing it inside the conjunction) and interned as one sequence; a
//!    list's candidates are normalized and interned once, as far as its longest recipe
//!    reads, each prefix's sequence pushed onto the last ([`SpineMemo`]);
//! 4. the relevance name (`relevance_var_name`'s collapse) of every variable of the
//!    candidates and the body is listed in the context's table; a name already listed as
//!    another declines the row, so no spine the context already closed changes its kept
//!    list;
//! 5. the context's closure (`VcContext::kept`) must keep exactly the formula's facts, so
//!    the Spine materializes to the row's formula, whatever the recipe said. A row whose
//!    conjoined facts are not all among the normalized candidates is declined as
//!    [`SpineDecline::Normalization`] (a candidate normalized alone is not what the row's
//!    normalization made of it: a normalization that is not a per-name renaming), any other
//!    as [`SpineDecline::Closure`];
//! 6. the record names the spine's kept facts (`WrapperRef::SpineKept`) in place of a
//!    `ConjoinFactsLast` wrapper over exactly those facts, and is interned as it is
//!    otherwise.
//!
//! Then the row oracle reads the row back (`VcContext::check_row`) and substitutes a Node
//! row on any disagreement, counted. A declined row joins as a Node row through
//! `push_checked_row`, as every row did before C08. A Spine row's cone is its one block, so
//! each counts one block in the context's `sum_cone_blocks`.
//!
//! # Which block-def rows stay Node (L4-RECIPE-1)
//!
//! A row whose combination a later step rewrote has another formula, finds no recipe, and
//! joins as a Node row: the safety walk's whole-row wrappers (path definitions, path guards,
//! semantic guards, the type-range battery, the global facts), the separation rows' fact
//! wrappers, and every lane that conjoins more facts around a builder's result. The rows a
//! recipe was found for are the block-def rows; [`RecipeCounts`] counts them, the Spine rows
//! among them, and each decline by reason. Callsite rows join the context in discharge, not
//! through the sink, and stay Node.
//!
//! The recipe log is a thread-local: a generation runs on one thread, and a generation
//! nested in another records into its own log, the outer one restored when it ends.

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use trust_types::fx::{FxHashMap, FxHashSet, FxHasher};
use trust_types::vc_context::{
    MemoSlot, NodeId, RecordRef, RelevanceRule, RowId, SeqId, Spine, SpineRow, VcContext,
    VcContextError, WrapperRef,
};
use trust_types::{
    Formula, ObligationRecord, ObligationWrapper, VerifiableFunction, VerificationCondition,
};

use super::block_defs::relevance_var_name_str;
use super::{normalize_ssa_version_tokens_owned, v2_is_unsupported_mir_vc};

/// How many recipes one row tries, newest first: rows whose keys collide are rare, and each
/// try normalizes a candidate list.
const RECIPE_TRIES: usize = 4;

/// Whether a generation joins its block-def rows as Spine rows (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Spines {
    /// Record the combinations and join block-def rows as Spines: the caller keeps the
    /// context.
    Join,
    /// Record nothing: no context, or one that drops with the generation.
    Skip,
}

/// One recorded combination: the first `len` facts of a candidate list, and how many of
/// them the rule kept.
#[derive(Debug, Clone)]
pub(super) struct Recipe {
    list: Rc<CandidateList>,
    len: usize,
    kept: usize,
}

/// The candidate facts of consecutive combinations, each of which is a prefix of the list
/// (module docs). It is only ever extended, so a recipe's prefix never changes.
#[derive(Debug)]
pub(super) struct CandidateList {
    facts: RefCell<Vec<Formula>>,
}

impl CandidateList {
    fn new(facts: Vec<Formula>) -> Rc<CandidateList> {
        Rc::new(CandidateList { facts: RefCell::new(facts) })
    }

    /// Take `candidates` into this list when one of the two is a prefix of the other,
    /// extending the list by their tail when they are the longer; hand them back, the list
    /// unchanged, when neither is.
    fn share(&self, candidates: Vec<Formula>) -> Result<(), Vec<Formula>> {
        let mut facts = self.facts.borrow_mut();
        let common = facts.len().min(candidates.len());
        if facts.get(..common) != candidates.get(..common) {
            return Err(candidates);
        }
        if candidates.len() > common {
            facts.extend(candidates.into_iter().skip(common));
        }
        Ok(())
    }

    /// Borrowed counterpart to [`Self::share`]: returns `true` when `candidates` and `self`
    /// are prefixes one of the other, cloning only the newly appended tail (zero clones when
    /// `candidates.len() <= facts.len()`).
    fn share_slice(&self, candidates: &[Formula]) -> bool {
        let mut facts = self.facts.borrow_mut();
        let common = facts.len().min(candidates.len());
        if facts.get(..common) != candidates.get(..common) {
            return false;
        }
        if candidates.len() > common {
            facts.extend_from_slice(&candidates[common..]);
        }
        true
    }

    /// The candidate at `index`, cloned out of the list (so nothing holds its borrow while
    /// the candidate is normalized).
    fn fact(&self, index: usize) -> Option<Formula> {
        self.facts.borrow().get(index).cloned()
    }
}

/// The recipes of one generation (module docs).
#[derive(Debug, Default)]
struct RecipeLog {
    by_key: FxHashMap<u64, Vec<Recipe>>,
    /// The list recorded into last, which the next recipe shares when its candidates and
    /// the list's are prefixes one of the other.
    last: Option<Rc<CandidateList>>,
    /// Combinations recorded.
    recorded: u64,
}

thread_local! {
    static LOG: RefCell<Option<RecipeLog>> = const { RefCell::new(None) };
}

/// The recipe log of one generation, open while the scope lives (module docs).
pub(super) struct RecipeScope {
    outer: Option<RecipeLog>,
}

impl RecipeScope {
    /// Open a generation's log, which records only when `on`: when the generation writes
    /// into its caller's context, the one reader of a recipe ([`Spines::Join`]). The
    /// enclosing generation's log is set aside until the scope ends.
    pub(super) fn open(on: bool) -> RecipeScope {
        let log = on.then(RecipeLog::default);
        RecipeScope { outer: LOG.with(|cell| cell.replace(log)) }
    }
}

impl Drop for RecipeScope {
    fn drop(&mut self) {
        let outer = self.outer.take();
        let _ = LOG.try_with(|cell| *cell.borrow_mut() = outer);
    }
}

/// Whether this thread's generation records recipes.
pub(super) fn recording() -> bool {
    LOG.with(|cell| cell.borrow().is_some())
}

/// The combinations this thread's generation recorded.
pub(super) fn recorded() -> u64 {
    LOG.with(|cell| cell.borrow().as_ref().map_or(0, |log| log.recorded))
}

/// Record that `combined` is the block-def combination of `candidates` that keeps `kept`
/// of them, when this thread's generation records recipes.
pub(super) fn record(candidates: Vec<Formula>, kept: usize, combined: &Formula) {
    LOG.with(|cell| {
        let mut log = cell.borrow_mut();
        let Some(log) = log.as_mut() else { return };
        let Some(key) = shape_key(combined, kept) else { return };
        let len = candidates.len();
        let list = match log.last.take() {
            Some(last) => match last.share(candidates) {
                Ok(()) => last,
                Err(candidates) => CandidateList::new(candidates),
            },
            None => CandidateList::new(candidates),
        };
        log.last = Some(Rc::clone(&list));
        log.recorded += 1;
        let bucket = log.by_key.entry(key).or_default();
        let known = bucket.iter().any(|recipe| {
            recipe.kept == kept && recipe.len == len && Rc::ptr_eq(&recipe.list, &list)
        });
        if !known {
            bucket.push(Recipe { list, len, kept });
        }
    });
}

/// Borrowed counterpart to [`record`] for callers holding a slice (such as a memoized
/// [`super::block_defs::VersionedBlockDefs`]): avoids cloning already-shared prefix formulas.
pub(super) fn record_slice(candidates: &[Formula], kept: usize, combined: &Formula) {
    LOG.with(|cell| {
        let mut log = cell.borrow_mut();
        let Some(log) = log.as_mut() else { return };
        let Some(key) = shape_key(combined, kept) else { return };
        let len = candidates.len();
        let list = match log.last.take() {
            Some(last) if last.share_slice(candidates) => last,
            _ => CandidateList::new(candidates.to_vec()),
        };
        log.last = Some(Rc::clone(&list));
        log.recorded += 1;
        let bucket = log.by_key.entry(key).or_default();
        let known = bucket.iter().any(|recipe| {
            recipe.kept == kept && recipe.len == len && Rc::ptr_eq(&recipe.list, &list)
        });
        if !known {
            bucket.push(Recipe { list, len, kept });
        }
    });
}

/// Conjoin late facts while retaining an existing conjunction's prefix.
/// `prefix ∧ B` becomes `prefix ∧ (facts ∧ B)`: precisely the same conjunction as
/// `facts ∧ (prefix ∧ B)`, with every fact and occurrence retained. This uses pure
/// conjunction reassociation and reordering; a prefix earns block-def credit only when
/// an existing recipe names it, with that recipe's original candidates.
/// This layout is independent of recording, so eager and context generation
/// return identical formulas. Only an existing recipe is carried to its new
/// body; no candidate list or construction count is invented. The usual
/// relevance, normalization, record and exact row-oracle checks still decide
/// whether it can join as a Spine.
pub(super) fn conjoin_body_facts(formula: Formula, mut facts: Vec<Formula>) -> Formula {
    if facts.is_empty() {
        return formula;
    }
    let known = recipes_for(&formula);
    let combined = match formula {
        Formula::And(mut conjuncts) if conjuncts.len() >= 2 => {
            let Some(body) = conjuncts.pop() else {
                facts.push(Formula::And(conjuncts));
                return Formula::And(facts);
            };
            facts.push(body);
            conjuncts.push(Formula::And(facts));
            Formula::And(conjuncts)
        }
        body => {
            facts.push(body);
            Formula::And(facts)
        }
    };
    if !known.is_empty() {
        LOG.with(|cell| {
            let mut log = cell.borrow_mut();
            let Some(log) = log.as_mut() else { return };
            // `known` is newest first; preserve that priority when recipes_for
            // reads this bucket in reverse under its bounded attempt count.
            for recipe in known.into_iter().rev() {
                let Some(key) = shape_key(&combined, recipe.kept) else { continue };
                let bucket = log.by_key.entry(key).or_default();
                if !bucket.iter().any(|other| {
                    other.kept == recipe.kept
                        && other.len == recipe.len
                        && Rc::ptr_eq(&other.list, &recipe.list)
                }) {
                    bucket.push(recipe);
                }
            }
        });
    }
    combined
}

/// The candidate facts this thread's log holds, each list counted once.
#[cfg(test)]
pub(super) fn held_facts() -> usize {
    LOG.with(|cell| {
        let log = cell.borrow();
        let Some(log) = log.as_ref() else { return 0 };
        let mut lists: FxHashSet<*const CandidateList> = FxHashSet::default();
        let mut held = 0;
        for list in log.by_key.values().flatten().map(|recipe| &recipe.list).chain(&log.last) {
            if lists.insert(Rc::as_ptr(list)) {
                held += list.facts.borrow().len();
            }
        }
        held
    })
}

/// The recipes `formula` may be the combination of, newest first, at most
/// [`RECIPE_TRIES`]: those keeping all but its last conjunct when it is an `And`, then those
/// keeping nothing.
pub(super) fn recipes_for(formula: &Formula) -> Vec<Recipe> {
    LOG.with(|cell| {
        let log = cell.borrow();
        let Some(log) = log.as_ref() else { return Vec::new() };
        if log.by_key.is_empty() {
            return Vec::new();
        }
        let mut keys = [(0usize, 0u64); 2];
        let mut keys_len = 0usize;
        let whole = match formula {
            Formula::And(conjuncts) if conjuncts.len() >= 2 => {
                if conjuncts.len() <= 16 {
                    let mut buf = [0u64; 16];
                    for (slot, c) in buf.iter_mut().zip(conjuncts) {
                        *slot = shape_hash(c);
                    }
                    let parts = &buf[..conjuncts.len()];
                    keys[keys_len] = (conjuncts.len() - 1, key_of(conjuncts.len() - 1, parts));
                    keys_len += 1;
                    node_hash(formula, parts)
                } else {
                    let parts: Vec<u64> = conjuncts.iter().map(shape_hash).collect();
                    keys[keys_len] = (conjuncts.len() - 1, key_of(conjuncts.len() - 1, &parts));
                    keys_len += 1;
                    node_hash(formula, &parts)
                }
            }
            _ => shape_hash(formula),
        };
        keys[keys_len] = (0, key_of(0, &[whole]));
        keys_len += 1;
        let mut found = Vec::new();
        for &(kept, key) in &keys[..keys_len] {
            let Some(bucket) = log.by_key.get(&key) else { continue };
            found.extend(bucket.iter().rev().filter(|recipe| recipe.kept == kept).cloned());
        }
        found.truncate(RECIPE_TRIES);
        found
    })
}

/// The key a combination that keeps `kept` facts is recorded under: its facts' and body's
/// shape hashes (`formula`'s conjuncts when it keeps some, `formula` itself when it keeps
/// none). `None` when `formula` cannot be such a combination.
pub(super) fn shape_key(formula: &Formula, kept: usize) -> Option<u64> {
    if kept == 0 {
        return Some(key_of(0, &[shape_hash(formula)]));
    }
    match formula {
        Formula::And(conjuncts) if conjuncts.len() == kept + 1 => {
            if conjuncts.len() <= 16 {
                let mut buf = [0u64; 16];
                for (slot, c) in buf.iter_mut().zip(conjuncts) {
                    *slot = shape_hash(c);
                }
                Some(key_of(kept, &buf[..conjuncts.len()]))
            } else {
                let parts: Vec<u64> = conjuncts.iter().map(shape_hash).collect();
                Some(key_of(kept, &parts))
            }
        }
        _ => None,
    }
}

fn key_of(kept: usize, parts: &[u64]) -> u64 {
    let mut hasher = FxHasher::default();
    kept.hash(&mut hasher);
    parts.hash(&mut hasher);
    hasher.finish()
}

const SHAPE_HASH_STACK_CAP: usize = 64;

/// A formula's shape hash (module docs): stack-allocated bottom-up evaluation up to
/// [`SHAPE_HASH_STACK_CAP`], falling back to [`shape_hash_iterative`] on deep ASTs so
/// ordinary formulas allocate zero `Vec`s while deep ones cannot overflow the stack.
pub(super) fn shape_hash(formula: &Formula) -> u64 {
    shape_hash_depth(formula, 0)
}

fn shape_hash_depth(node: &Formula, depth: usize) -> u64 {
    if depth >= SHAPE_HASH_STACK_CAP {
        return shape_hash_iterative(node);
    }
    let mut inline = [0u64; 16];
    let mut len = 0usize;
    let mut spill: Vec<u64> = Vec::new();
    trust_types::for_each_formula_child(node, |child| {
        let h = shape_hash_depth(child, depth + 1);
        if spill.is_empty() {
            if len < inline.len() {
                inline[len] = h;
                len += 1;
            } else {
                spill.reserve(len + 8);
                spill.extend_from_slice(&inline);
                spill.push(h);
            }
        } else {
            spill.push(h);
        }
    });
    if spill.is_empty() {
        node_hash(node, &inline[..len])
    } else {
        node_hash(node, &spill)
    }
}

pub(super) fn shape_hash_iterative(formula: &Formula) -> u64 {
    enum Step<'f> {
        Enter(&'f Formula),
        Leave(&'f Formula, usize),
    }
    let mut steps = vec![Step::Enter(formula)];
    let mut done: Vec<u64> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(node) => {
                let before = steps.len();
                steps.push(Step::Leave(node, 0));
                trust_types::for_each_formula_child(node, |child| {
                    steps.push(Step::Enter(child));
                });
                let arity = steps.len() - before - 1;
                if arity == 0 {
                    steps.pop();
                    done.push(node_hash(node, &[]));
                } else {
                    steps[before] = Step::Leave(node, arity);
                    steps[before + 1..].reverse();
                }
            }
            Step::Leave(node, arity) => {
                let at = done.len().saturating_sub(arity);
                let hash = node_hash(node, &done[at..]);
                done.truncate(at);
                done.push(hash);
            }
        }
    }
    done.pop().unwrap_or_default()
}

/// One node's shape hash from its children's: its variant, and a variable's name up to its
/// first `#`, a leaf's whole value, or the children's hashes.
fn node_hash(node: &Formula, children: &[u64]) -> u64 {
    let mut hasher = FxHasher::default();
    std::mem::discriminant(node).hash(&mut hasher);
    if let Formula::Var(name, _) = node {
        name.split_once('#').map_or(name.as_str(), |(base, _)| base).hash(&mut hasher);
    } else if children.is_empty() {
        node.hash(&mut hasher);
    } else {
        children.hash(&mut hasher);
    }
    hasher.finish()
}

/// Why a block-def row joined as a Node row (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpineDecline {
    /// The per-row passes made the row `UnsupportedMir`.
    Reclassified,
    /// Term-`Ite` elimination rewrote the row.
    Ite,
    /// The row's formula is not its recipe's conjunction.
    Shape,
    /// A variable's relevance name is already listed as another.
    Relevance,
    /// The context's closure keeps other facts than the row's formula conjoins.
    Closure,
    /// A fact the row's formula conjoins is no normalized candidate: a candidate normalized
    /// alone is not what the row's normalization made of it.
    Normalization,
    /// The context refused an id, or a table was full.
    Context,
    /// The row oracle's read-back disagreed, and it substituted a Node row.
    Oracle,
}

impl SpineDecline {
    /// Every reason, in [`RecipeCounts::declines`]' order.
    pub const ALL: [SpineDecline; 8] = [
        SpineDecline::Reclassified,
        SpineDecline::Ite,
        SpineDecline::Shape,
        SpineDecline::Relevance,
        SpineDecline::Closure,
        SpineDecline::Normalization,
        SpineDecline::Context,
        SpineDecline::Oracle,
    ];

    /// The reason's name, for reports.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            SpineDecline::Reclassified => "reclassified",
            SpineDecline::Ite => "ite",
            SpineDecline::Shape => "shape",
            SpineDecline::Relevance => "relevance",
            SpineDecline::Closure => "closure",
            SpineDecline::Normalization => "normalization",
            SpineDecline::Context => "context",
            SpineDecline::Oracle => "oracle",
        }
    }

    fn slot(self) -> usize {
        self as usize
    }
}

/// What the block-def rows of the generations that wrote into one context became (module
/// docs), kept in the context's [`MemoSlot::Recipes`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RecipeCounts {
    /// Combinations the builders recorded, a row's or not.
    pub recorded: u64,
    /// Rows that joined with a recipe: the block-def rows.
    pub block_def_rows: u64,
    /// Block-def rows that joined as Spine rows.
    pub spine_rows: u64,
    /// Block-def rows that joined as Node rows, by reason, in [`SpineDecline::ALL`]'s order.
    pub declines: [u64; SpineDecline::ALL.len()],
}

impl RecipeCounts {
    /// The block-def rows declined for `reason`.
    #[must_use]
    pub fn declined(&self, reason: SpineDecline) -> u64 {
        self.declines.get(reason.slot()).copied().unwrap_or(0)
    }

    /// Add `other`'s counts (a report over several contexts).
    pub fn absorb(&mut self, other: &RecipeCounts) {
        self.recorded += other.recorded;
        self.block_def_rows += other.block_def_rows;
        self.spine_rows += other.spine_rows;
        for (count, more) in self.declines.iter_mut().zip(other.declines) {
            *count += more;
        }
    }
}

/// What the block-def rows of the generations that wrote into `context` became.
#[must_use]
pub fn recipe_counts(context: &VcContext) -> RecipeCounts {
    context.memo().with(MemoSlot::Recipes, |counts: &mut RecipeCounts| *counts).unwrap_or_default()
}

fn count(context: &VcContext, work: impl FnOnce(&mut RecipeCounts)) {
    let _ = context.memo().with(MemoSlot::Recipes, work);
}

/// Count the combinations this thread's generation recorded into `context`'s counts.
pub(super) fn note_recorded(context: &VcContext) {
    let recorded = recorded();
    count(context, |counts| counts.recorded += recorded);
}

/// One candidate list's normalized prefix, interned (module docs, steps 3 and 4).
#[derive(Debug)]
struct NormalizedList {
    /// The list itself, held so that its address, the memo's key, is not reused while the
    /// memo lives: a dropped list's address could be a new list's.
    _list: Rc<CandidateList>,
    /// The list's candidates normalized and interned, in order, as far as a recipe read.
    nodes: Vec<NodeId>,
    /// `seqs[i]` is the sequence of `nodes[..i]`; `seqs[0]` is the empty one.
    seqs: Vec<SeqId>,
    /// `nodes[..listed]` have every variable's relevance name listed.
    listed: usize,
}

/// What one sink's Spine attempts share (module docs): each candidate list's normalized
/// prefix and the sequence of each of its prefixes, by the list's address, and the nodes
/// whose variables' relevance names are listed.
#[derive(Debug, Default)]
pub(super) struct SpineMemo {
    lists: FxHashMap<*const CandidateList, NormalizedList>,
    listed: FxHashSet<NodeId>,
}

impl SpineMemo {
    /// The sequence of `recipe`'s candidates normalized and interned into `rows`, each of
    /// their variables' relevance names listed (module docs, steps 3 and 4). A list's
    /// candidates are normalized, interned and listed once, as far as its longest recipe
    /// reads.
    fn candidates(
        &mut self,
        func: &VerifiableFunction,
        rows: &mut VcContext,
        recipe: &Recipe,
    ) -> Result<SeqId, SpineDecline> {
        let known = match self.lists.entry(Rc::as_ptr(&recipe.list)) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let empty = rows.seq(&[]).map_err(|_| SpineDecline::Context)?;
                entry.insert(NormalizedList {
                    _list: Rc::clone(&recipe.list),
                    nodes: Vec::new(),
                    seqs: vec![empty],
                    listed: 0,
                })
            }
        };
        if known.nodes.len() < recipe.len {
            let extra = recipe.len - known.nodes.len();
            known.nodes.reserve(extra);
            known.seqs.reserve(extra);
        }
        while known.nodes.len() < recipe.len {
            let candidate = recipe.list.fact(known.nodes.len()).ok_or(SpineDecline::Context)?;
            let node = rows.intern(&normalize_ssa_version_tokens_owned(func, candidate));
            let last = known.seqs.last().copied().ok_or(SpineDecline::Context)?;
            let seq = rows.seq_push(last, node).map_err(|_| SpineDecline::Context)?;
            known.nodes.push(node);
            known.seqs.push(seq);
        }
        if known.listed < recipe.len {
            let fresh = known.nodes.get(known.listed..recipe.len).unwrap_or_default();
            list_relevance(&mut self.listed, func, rows, fresh)?;
            known.listed = recipe.len;
        }
        known.seqs.get(recipe.len).copied().ok_or(SpineDecline::Context)
    }

    /// Why the context's closure over `recipe`'s candidates kept other facts than the row
    /// conjoins (`expected`), as module docs step 5 says.
    fn closure_decline(&self, recipe: &Recipe, expected: &[NodeId]) -> SpineDecline {
        let nodes: &[NodeId] = match self.lists.get(&Rc::as_ptr(&recipe.list)) {
            Some(known) => known.nodes.get(..recipe.len).unwrap_or(&known.nodes),
            None => &[],
        };
        let all_in_candidates = if nodes.len() <= 16 || expected.len() <= 2 {
            expected.iter().all(|fact| nodes.contains(fact))
        } else {
            let candidates: FxHashSet<NodeId> = nodes.iter().copied().collect();
            expected.iter().all(|fact| candidates.contains(fact))
        };
        if all_in_candidates {
            SpineDecline::Closure
        } else {
            SpineDecline::Normalization
        }
    }
}

/// List the relevance name of every variable of `nodes` in `rows`' table (module docs,
/// step 4), the nodes listed so far in `done`: nothing is listed when one is already listed
/// as another.
fn list_relevance(
    done: &mut FxHashSet<NodeId>,
    func: &VerifiableFunction,
    rows: &mut VcContext,
    nodes: &[NodeId],
) -> Result<(), SpineDecline> {
    let mut fresh: Vec<(String, String)> = Vec::new();
    let mut reached: Vec<NodeId> = Vec::new();
    for &node in nodes {
        if done.contains(&node) {
            continue;
        }
        let names = rows.formula_var_names(node).map_err(|_| SpineDecline::Context)?;
        for name in names {
            let relevance = relevance_var_name_str(func, &name);
            match rows.vars().listed(&name) {
                Some(listed) if listed == relevance => {}
                Some(_) => return Err(SpineDecline::Relevance),
                None => {
                    let rel_owned = relevance.to_string();
                    fresh.push((name, rel_owned));
                }
            }
        }
        reached.push(node);
    }
    if !fresh.is_empty() {
        let vars = rows.vars_mut();
        for (name, relevance) in fresh {
            vars.insert(name, relevance);
        }
    }
    done.extend(reached);
    Ok(())
}

/// Join `vc`, a row whose formula had `recipes` before its per-row passes, into `rows`: as
/// a Spine row over the first recipe it is the combination of, checked by the row oracle,
/// or else as a Node row through it (module docs). `ite` is whether term-`Ite` elimination
/// rewrote the row.
pub(super) fn join_block_def_row(
    func: &VerifiableFunction,
    rows: &mut VcContext,
    memo: &mut SpineMemo,
    recipes: &[Recipe],
    vc: &mut VerificationCondition,
    ite: bool,
) -> Result<RowId, VcContextError> {
    let tried = if v2_is_unsupported_mir_vc(vc) {
        Err(SpineDecline::Reclassified)
    } else if ite {
        Err(SpineDecline::Ite)
    } else {
        let mut tried = Err(SpineDecline::Shape);
        for recipe in recipes {
            tried = spine_row(func, rows, memo, recipe, vc);
            let another = matches!(
                tried,
                Err(SpineDecline::Shape | SpineDecline::Closure | SpineDecline::Normalization)
            );
            if !another {
                break;
            }
        }
        tried
    };
    match tried {
        Ok(spine) => {
            let checked = rows.check_row(spine, vc);
            let agreed = checked.as_ref().is_ok_and(|id| *id == spine);
            count(rows, |counts| {
                counts.block_def_rows += 1;
                if agreed {
                    counts.spine_rows += 1;
                } else {
                    counts.declines[SpineDecline::Oracle.slot()] += 1;
                }
            });
            if agreed {
                rows.record_cone_blocks(1);
            }
            checked
        }
        Err(reason) => {
            count(rows, |counts| {
                counts.block_def_rows += 1;
                counts.declines[reason.slot()] += 1;
            });
            rows.push_checked_row(vc)
        }
    }
}

/// Push `vc` as a Spine row over `recipe` (module docs, steps 2 to 6), unchecked.
fn spine_row(
    func: &VerifiableFunction,
    rows: &mut VcContext,
    memo: &mut SpineMemo,
    recipe: &Recipe,
    vc: &mut VerificationCondition,
) -> Result<RowId, SpineDecline> {
    let (facts, body): (&[Formula], &Formula) = match (&vc.formula, recipe.kept) {
        (body, 0) => (&[], body),
        (Formula::And(conjuncts), kept) if conjuncts.len() == kept + 1 => {
            let Some((body, facts)) = conjuncts.split_last() else {
                return Err(SpineDecline::Shape);
            };
            (facts, body)
        }
        _ => return Err(SpineDecline::Shape),
    };
    let seq = memo.candidates(func, rows, recipe)?;
    let expected: Vec<NodeId> = facts.iter().map(|fact| rows.intern(fact)).collect();
    let body = rows.intern(body);
    list_relevance(&mut memo.listed, func, rows, &[body])?;
    let spine = Spine { candidates: seq, body, rule: RelevanceRule::BlockDefs };
    if rows.kept(&spine).map_err(|_| SpineDecline::Context)? != expected {
        return Err(memo.closure_decline(recipe, &expected));
    }
    let obligation = match vc.obligation.as_mut() {
        Some(record) => Some(spine_record(rows, record, facts)?),
        None => None,
    };
    let row = SpineRow {
        kind: vc.kind.clone(),
        function: vc.function,
        location: vc.location.clone(),
        spine,
        contract_metadata: vc.contract_metadata,
        obligation,
    };
    rows.push_spine_row(row).map_err(|_| SpineDecline::Context)
}

/// `record` interned, its first `ConjoinFactsLast` wrapper over exactly `facts` (the
/// spine's kept facts) named as [`WrapperRef::SpineKept`].
fn spine_record(
    rows: &mut VcContext,
    record: &mut ObligationRecord,
    facts: &[Formula],
) -> Result<RecordRef, SpineDecline> {
    let names_kept = |wrapper: &ObligationWrapper| {
        matches!(wrapper, ObligationWrapper::ConjoinFactsLast { facts: recorded }
            if recorded.as_slice() == facts)
    };
    let at = if facts.is_empty() { None } else { record.wrappers.iter().position(names_kept) };
    let Some(at) = at else {
        return rows.intern_record(record).map_err(|_| SpineDecline::Context);
    };
    let wrapper = record.wrappers.remove(at);
    let interned = rows.intern_record(record);
    record.wrappers.insert(at, wrapper);
    let mut interned = interned.map_err(|_| SpineDecline::Context)?;
    interned.wrappers.insert(at, WrapperRef::SpineKept);
    Ok(interned)
}
