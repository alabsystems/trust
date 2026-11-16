// trust-vcgen/src/generate/block_writes.rs: the per-block WRITE INDEX — one forward
// pass per block that answers, by lookup, the three statement-granular write
// questions the version oracle asks:
//
//   * `last_writer_before(b, i, name)`: the latest statement `j < i` for which
//     `path_defs::stmt_writes_name(b, j, name)` holds;
//   * `gate(b, i, name)`: whether some name in `path_defs::writes_until(b, i)`
//     `dest_write_rebinds` / `write_rebinds` `name`;
//   * `out_token(b, name)`: the reaching-version OUT token of a gen'd name (the
//     retired `entry_version_gen_sets` `gen_out` scan);
//
// plus each block's gen-set (`path_defs::block_written_names`) with the whole-function
// havoc list and the every-local `CopyNonOverlapping` write list kept SYMBOLIC.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHAT IT REPLACES AND WHY. The retired oracle answered those questions by scanning:
// `version_token_at` materialised `writes_until(b, i)` — a fresh statement-PREFIX
// definition extraction for every queried `(block, stmt_idx)`, memoised up to a
// 400k-name cap — and searched `stmts[..i]` backwards with `stmt_writes_name`; the
// OUT tokens were an O(names x statements) `stmt_writes_name` scan per block; and every
// Call/Drop terminator contributed a private COPY of the whole-function havoc list to
// its block's gen-set, so gen-sets summed to O(calls x pointer locals) — quadratic on
// the `ever-init-many-locals` shape, where every `Box` local is a pointer local and
// every `Box::new`/`drop` is a call.
//
// THE HAVOC LIST STAYS SYMBOLIC EVERYWHERE. A block's gen-set holds the whole-function
// havoc list `h` in one of three ways, and none of them copies it:
//
//   * FULL — an unconfined opaque store, or a terminator that havocs `h` unrefined;
//   * PART — `h` minus an EXCLUSION: a CONFINED opaque store (`(*self).f = v`) havocs
//     `h` minus the names overlapping its pointer's base, and a per-call REFINED
//     havoc (`callee_write_set`, a `path_defs::HavocDelta`) is `h` minus a few names
//     plus a few more (the "plus" names are explicit). Blocks with the same exclusion
//     share one [`ClassTable`] class, and a name's excluded classes are found by
//     lookup (the exclusion is a relation to a handful of base names / removed
//     names, never to the list);
//   * NONE.
//
// Copying `h` minus the exclusion into every such block's gen-set (the previous form of
// this index) made confined-store and refined-call blocks `O(|h|)` each — quadratic on
// a `&mut self` method with many borrows and many field stores or calls.
//
// EXACTNESS. Each answer is a re-expression of the same predicate over the same
// per-statement facts (argued at each query below), so the version tokens are
// byte-identical to the retired ones; `version_ssa_parity_tests` asserts it over every
// block, statement index and name of the corpus. The one place an exact answer is not
// cheap — a prefix whose DEFINITION extraction may carry a synthetic name no
// statement destination accounts for — falls back to the exact prefix extraction
// (`path_defs::writes_until_uncached`), is detected exactly (see `SynNames`), and is
// shared by every read at one point (see `BlockWrites::exact_prefix`).

use std::cell::{OnceCell, RefCell};
use std::ops::ControlFlow;
use std::rc::Rc;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Statement, VerifiableFunction};

use super::rebind_index::{NameId, NameTable, RebindIndex, RebindMode};
use super::{
    IndexLocals, SLICE_LEN_SUFFIX, TermExtra, TermHavoc, dest_write_rebinds, formula_def_name,
    local_fallback_name, place_names_overlap, write_covers_index_segment, write_rebinds,
};

/// How a statement's explicitly-named write relates to a read (`stmt_writes_name`'s
/// three per-name tests).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Chan {
    /// `dest_write_rebinds(w, read)` — an `Assign` / `Deinit` destination.
    Dest,
    /// `write_rebinds(w, read)` — a `SetDiscriminant` place.
    Plain,
    /// `read == w || write_covers_index_segment(w, read)` — the index fallback `_l` of a
    /// whole-local `Assign`.
    Fallback,
}

fn chan_admits(chan: Chan, w: &str, read: &str) -> bool {
    match chan {
        Chan::Dest => dest_write_rebinds(w, read),
        Chan::Plain => write_rebinds(w, read),
        Chan::Fallback => read == w || write_covers_index_segment(w, read),
    }
}

/// Sentinel "no position / no index" for the `u32` arrays below.
const NO_POS: u32 = u32::MAX;

/// How a block's gen-set holds the whole-function havoc list `h` (see the module doc).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HMode {
    None,
    Full,
    /// `h` minus the exclusion of this class of the family's [`ClassTable`].
    Part(u32),
}

/// What a PART block leaves out of `h`: a name `k` of `h` is NOT in the block's
/// gen-set iff every base in `bases` overlaps `k` (or there are no confined stores),
/// AND `k` is in `removed` (or there is no refined terminator havoc). `None` in a
/// field means that source contributes nothing from `h`.
///
/// Why: the confined stores contribute `∪_s (h \ overlapping(base_s))`, which misses
/// `k` exactly when every store's base overlaps `k`; a refined terminator contributes
/// `h \ removed`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Exclusion {
    bases: Option<Rc<[Rc<str>]>>,
    removed: Option<Rc<[NameId]>>,
}

impl Exclusion {
    fn excludes(&self, names: &NameTable, k: NameId) -> bool {
        let text = names.name(k);
        self.bases.as_ref().is_none_or(|bases| bases.iter().all(|b| place_names_overlap(text, b)))
            && self.removed.as_ref().is_none_or(|r| r.binary_search(&k).is_ok())
    }
}

/// The distinct PART exclusions of one gen-set family, and the lookups that find,
/// for a name, the classes that exclude it without testing every class.
#[derive(Default)]
pub(crate) struct ClassTable {
    classes: Vec<Exclusion>,
    ids: FxHashMap<Exclusion, u32>,
    /// Distinct confined-store base names, indexed for the overlap relation.
    base_table: NameTable,
    base_index: RebindIndex,
    classes_by_base: Vec<Vec<u32>>,
    classes_by_removed: FxHashMap<NameId, Vec<u32>>,
}

impl ClassTable {
    fn intern(&mut self, excl: Exclusion) -> u32 {
        if let Some(&c) = self.ids.get(&excl) {
            return c;
        }
        let c = self.classes.len() as u32;
        if let Some(bases) = &excl.bases {
            for b in bases.iter() {
                let id = self.base_table.intern(b) as usize;
                if id == self.classes_by_base.len() {
                    self.classes_by_base.push(Vec::new());
                }
                self.classes_by_base[id].push(c);
            }
        }
        if let Some(removed) = &excl.removed {
            for &k in removed.iter() {
                self.classes_by_removed.entry(k).or_default().push(c);
            }
        }
        self.ids.insert(excl.clone(), c);
        self.classes.push(excl);
        c
    }

    fn finish(&mut self) {
        self.base_index = RebindIndex::build(&self.base_table, 0..self.base_table.len() as NameId);
    }

    pub(crate) fn len(&self) -> usize {
        self.classes.len()
    }

    /// Every class whose exclusion leaves `k` out, sorted. A class with confined-store
    /// bases excludes `k` only if some base overlaps `k` (found through the base
    /// index — `write_rebinds` contains `place_names_overlap`); a class without bases
    /// excludes it only if its removed list holds `k`. Each candidate is then tested
    /// exactly.
    pub(crate) fn excluding(&self, names: &NameTable, k: NameId) -> Vec<u32> {
        let mut cand: Vec<u32> = Vec::new();
        if !self.classes_by_base.is_empty() {
            let text = names.name(k);
            self.base_index.for_each_rebinder(text, RebindMode::Plain, |b| {
                if place_names_overlap(text, self.base_table.name(b)) {
                    cand.extend_from_slice(&self.classes_by_base[b as usize]);
                }
            });
        }
        if let Some(cs) = self.classes_by_removed.get(&k) {
            cand.extend_from_slice(cs);
        }
        if cand.is_empty() {
            return cand;
        }
        if cand.len() > 1 {
            cand.sort_unstable();
            cand.dedup();
        }
        cand.retain(|&c| self.classes[c as usize].excludes(names, k));
        cand
    }
}

/// How the terminator havocs `h`.
#[derive(Clone, Debug)]
enum TermKind {
    None,
    Function,
    /// `h` minus these names (sorted); the names it adds are explicit.
    Refined(Rc<[NameId]>),
}

/// A block's CONFINED opaque stores, in statement order, with their pointer bases, and
/// per-store jump pointers over runs of the same base — so "the latest (earliest)
/// store before `i` whose base is outside a small failing set" costs one jump per
/// failing base met, not one step per store.
#[derive(Default)]
struct Confined {
    pos: Vec<u32>,
    base: Vec<u32>,
    /// Nearest EARLIER store with a different base (`NO_POS` when none).
    prev_diff: Vec<u32>,
    /// Nearest LATER store with a different base (`len` when none).
    next_diff: Vec<u32>,
    bases: NameTable,
    base_index: RebindIndex,
}

impl Confined {
    fn push(&mut self, pos: u32, base: &str) {
        self.pos.push(pos);
        self.base.push(self.bases.intern(base));
    }

    fn finish(&mut self) {
        let n = self.pos.len();
        self.prev_diff = vec![NO_POS; n];
        self.next_diff = vec![n as u32; n];
        for t in 1..n {
            self.prev_diff[t] =
                if self.base[t - 1] != self.base[t] { t as u32 - 1 } else { self.prev_diff[t - 1] };
        }
        for t in (0..n.saturating_sub(1)).rev() {
            self.next_diff[t] =
                if self.base[t + 1] != self.base[t] { t as u32 + 1 } else { self.next_diff[t + 1] };
        }
        self.base_index = RebindIndex::build(&self.bases, 0..self.bases.len() as NameId);
    }

    fn is_empty(&self) -> bool {
        self.pos.is_empty()
    }

    /// The base ids that overlap `name` (exact).
    fn overlapping(&self, name: &str) -> Vec<u32> {
        let mut out: Vec<u32> = Vec::new();
        self.base_index.for_each_rebinder(name, RebindMode::Plain, |b| {
            if place_names_overlap(name, self.bases.name(b)) {
                out.push(b);
            }
        });
        if out.len() > 1 {
            out.sort_unstable();
            out.dedup();
        }
        out
    }

    /// The latest store with position `< i` and base NOT in `failing`, if it is later
    /// than `floor`.
    fn last_before_outside(&self, i: u32, failing: &[u32], floor: Option<u32>) -> Option<u32> {
        let k = self.pos.partition_point(|&p| p < i);
        let mut t = if k == 0 { NO_POS } else { k as u32 - 1 };
        while t != NO_POS {
            let p = self.pos[t as usize];
            if floor.is_some_and(|f| f >= p) {
                return None;
            }
            if !failing.contains(&self.base[t as usize]) {
                return Some(p);
            }
            t = self.prev_diff[t as usize];
        }
        None
    }

    /// Whether some store with position `< i` has a base NOT in `failing`.
    fn any_before_outside(&self, i: u32, failing: &[u32]) -> bool {
        let n = self.pos.len() as u32;
        let mut t = 0u32;
        while t < n && self.pos[t as usize] < i {
            if !failing.contains(&self.base[t as usize]) {
                return true;
            }
            t = self.next_diff[t as usize];
        }
        false
    }

    /// The earliest store with position `< i` and base NOT in `failing`, if it is
    /// earlier than `ceil`.
    fn first_before_outside(&self, i: u32, failing: &[u32], ceil: Option<u32>) -> Option<u32> {
        let bound = ceil.map_or(i, |c| c.min(i));
        let n = self.pos.len() as u32;
        let mut t = 0u32;
        while t < n && self.pos[t as usize] < bound {
            if !failing.contains(&self.base[t as usize]) {
                return Some(self.pos[t as usize]);
            }
            t = self.next_diff[t as usize];
        }
        None
    }
}

/// One block's write index.
pub(crate) struct BlockWrites {
    n_stmts: u32,
    /// `stmt_writes_name`'s explicitly named writes: name -> (statement, channel), in
    /// statement order.
    writer_entries: FxHashMap<NameId, Vec<(u32, Chan)>>,
    writer_index: RebindIndex,
    /// Statements that are OPAQUE deref stores whose effect is NOT confined to the
    /// written place: each havocs the whole-function list. Since 2026-10-11 also every
    /// write `path_defs::write_havocs_function_list` adds (a write into escaped storage a
    /// laundered pointer copy can read; LAUNDERED-ALIAS-STORE).
    h_unconfined: Vec<u32>,
    /// Opaque deref stores whose effect IS confined: each havocs the whole-function
    /// list minus the names overlapping the storing pointer's base.
    confined: Confined,
    /// Memory-writing `CopyNonOverlapping` statements: each writes every local.
    cno: Vec<u32>,
    /// The monotone part of `writes_until`: explicit destination / fallback names and
    /// their derived `__slice_len` twins, each with the FIRST statement contributing
    /// it (the name is in `writes_until(b, i)` iff that statement is `< i`).
    a_first: FxHashMap<NameId, u32>,
    a_index: RebindIndex,
    /// `block_written_names` minus its `h` and every-local parts, sorted.
    gen_explicit: Vec<NameId>,
    /// The statement half of the kill gen-set (`block_entry_fact_kill_names` minus
    /// its `h` part): definition names, destinations, fallbacks, derived twins. Sorted.
    stmt_explicit: Vec<NameId>,
    /// The terminator's explicit write names (`terminator_def_names` minus its `h`
    /// part: the destination extras and the names a refinement adds). Sorted.
    term_explicit: Vec<NameId>,
    /// The gen-set contains every local's write names (a `CopyNonOverlapping`).
    gen_all: bool,
    term: TermKind,
    /// How the statement-version gen-set (`block_written_names`) holds `h`.
    h_versions: HMode,
    /// How the kill gen-set (`block_entry_fact_kill_names` ∪ `terminator_def_names`)
    /// holds `h`: the kill takes the RAW list for any opaque store.
    h_kills: HMode,
    /// The terminator's explicit write names, indexed.
    term_index: RebindIndex,
    /// Lazily: `stmt_explicit`, indexed (the may-reassigned probe's own-block test).
    stmt_index: OnceCell<RebindIndex>,
    /// Lazily: the synthetic definition names a statement-prefix extraction may carry.
    syn: RefCell<Option<Rc<SynNames>>>,
    /// The EXACT prefix write set most recently extracted for this block, with its
    /// statement index (see `BlockWrites::exact_prefix`).
    exact_prefix: RefCell<Option<(u32, Rc<RebindIndex>)>>,
    /// Lazily, per read name: the sorted statement positions of every explicitly
    /// named write that `stmt_writes_name` admits for it (see `last_writer_before`).
    writer_positions: RefCell<FxHashMap<Rc<str>, Rc<[u32]>>>,
}

/// A superset of the definition names `extract_block_definitions_until(b, i)` (plus
/// the set-discriminant definitions) can contribute to `writes_until(b, i)`, with their
/// derived `__slice_len` twins: the names each statement `j` emits IN ISOLATION
/// (`guards::extract_statement_definitions_isolated`), tagged with `j`. A prefix
/// extraction keeps, for statement `j < i`, a subset of those (see that function's
/// doc), so `writes_until(b, i)`'s definition names are among the members with `j < i`.
struct SynNames {
    first: Vec<u32>,
    index: RebindIndex,
    /// The ambient verify budget had tripped by the end of this extraction: the
    /// polled per-statement extraction may have returned FEWER names than the
    /// statements emit, so the superset is not one and the gate must not skip the
    /// exact prefix on its say-so (see [`FnWrites::gate`]).
    truncated: bool,
}

/// The function's write index: every block's [`BlockWrites`] over one name table, and
/// the two symbolic groups.
pub(crate) struct FnWrites {
    pub(crate) names: NameTable,
    /// The whole-function havoc list (`path_defs::function_havoc_names`).
    h: Vec<NameId>,
    h_index: RebindIndex,
    /// Membership in `h`, by name id.
    in_h: Vec<bool>,
    /// Every local's `CopyNonOverlapping` write names (empty when the body has none).
    all: Vec<NameId>,
    all_index: RebindIndex,
    /// The derived twins `writes_until` / the gen-sets add to `all` (`_l__slice_len`).
    all_derived: Vec<NameId>,
    all_derived_index: RebindIndex,
    /// Membership in `all ∪ all_derived`, by name id.
    in_all: Vec<bool>,
    blocks: Vec<BlockWrites>,
    /// The PART exclusions of the statement-version gen-sets and of the kill gen-sets.
    classes_versions: ClassTable,
    classes_kills: ClassTable,
    /// The ambient verify budget had tripped by the end of the build. The gen-sets
    /// come from `guards::extract_block_definitions`, which polls per statement and
    /// hands back FEWER definitions on a trip — so an index built after one may miss
    /// definition names, and every answer that would be read as "nothing reaches but
    /// the entry value" must fail closed ([`super::version_ssa::VersionSsa`]'s `#e`
    /// gate reads this). A trip LATCHES for `exhausted_readonly` (the step counter
    /// saturates and a passed deadline stays passed), so reading it once, after the
    /// last polled extraction, covers every poll the build made.
    tripped: bool,
}

/// Which gen-set family a question is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GenFamily {
    Versions,
    Kills,
}

impl FnWrites {
    pub(crate) fn build(func: &VerifiableFunction) -> FnWrites {
        let mut names = NameTable::default();
        let havoc = super::function_havoc_names(func);
        let h: Vec<NameId> = dedup(havoc.iter().map(|n| names.intern(n)));
        let any_cno = func
            .body
            .blocks
            .iter()
            .any(|b| b.stmts.iter().any(super::copy_nonoverlapping_writes_memory));
        let (all, all_derived) = if any_cno {
            let mut set: FxHashSet<String> = FxHashSet::default();
            super::extend_with_every_local_write_name(func, &mut set);
            let mut sorted: Vec<String> = set.into_iter().collect();
            sorted.sort_unstable();
            let derived: Vec<String> = sorted
                .iter()
                .filter(|n| !n.ends_with(SLICE_LEN_SUFFIX))
                .map(|n| format!("{n}{SLICE_LEN_SUFFIX}"))
                .filter(|d| sorted.binary_search(d).is_err())
                .collect();
            (
                dedup(sorted.iter().map(|n| names.intern(n))),
                dedup(derived.iter().map(|n| names.intern(n))),
            )
        } else {
            (Vec::new(), Vec::new())
        };
        let h_index = RebindIndex::build(&names, h.iter().copied());
        // One fetch of the index-local table for every statement of every block.
        let index_locals = IndexLocals::of(func);
        let mut classes_versions = ClassTable::default();
        let mut classes_kills = ClassTable::default();
        let mut blocks = Vec::with_capacity(func.body.blocks.len());
        for block in &func.body.blocks {
            let mut ctx = BuildCtx {
                names: &mut names,
                h_index: &h_index,
                h_nonempty: !h.is_empty(),
                index_locals: &index_locals,
                classes_versions: &mut classes_versions,
                classes_kills: &mut classes_kills,
            };
            blocks.push(BlockWrites::build(func, block, &mut ctx));
        }
        classes_versions.finish();
        classes_kills.finish();
        let all_index = RebindIndex::build(&names, all.iter().copied());
        let all_derived_index = RebindIndex::build(&names, all_derived.iter().copied());
        let mut in_h = vec![false; names.len()];
        for &k in &h {
            in_h[k as usize] = true;
        }
        let mut in_all = vec![false; names.len()];
        for &k in all.iter().chain(&all_derived) {
            in_all[k as usize] = true;
        }
        let tripped = trust_types::verify_budget::exhausted_readonly();
        FnWrites {
            names,
            h,
            h_index,
            in_h,
            all,
            all_index,
            all_derived,
            all_derived_index,
            in_all,
            blocks,
            classes_versions,
            classes_kills,
            tripped,
        }
    }

    /// Whether the ambient verify budget had tripped when this index was built (see
    /// the field's doc): its gen-sets may be short.
    pub(crate) fn built_after_trip(&self) -> bool {
        self.tripped
    }

    pub(crate) fn block(&self, b: usize) -> Option<&BlockWrites> {
        self.blocks.get(b)
    }

    /// Every block's entry, in block order: one per block of the body this index was
    /// built from.
    pub(crate) fn blocks(&self) -> &[BlockWrites] {
        &self.blocks
    }

    pub(crate) fn havoc_names(&self) -> &[NameId] {
        &self.h
    }

    pub(crate) fn all_names(&self) -> impl Iterator<Item = NameId> + '_ {
        self.all.iter().chain(self.all_derived.iter()).copied()
    }

    /// Whether `name` is in the whole-function havoc list.
    pub(crate) fn in_havoc(&self, name: NameId) -> bool {
        self.in_h.get(name as usize).copied().unwrap_or(false)
    }

    /// Whether the text `name` is in the whole-function havoc list.
    pub(crate) fn in_havoc_text(&self, name: &str) -> bool {
        self.h_index.contains(name).is_some()
    }

    /// Whether `name` is in the every-local group (with its derived twins).
    pub(crate) fn in_all(&self, name: NameId) -> bool {
        self.in_all.get(name as usize).copied().unwrap_or(false)
    }

    /// The id of an interned name.
    pub(crate) fn name_id(&self, name: &str) -> Option<NameId> {
        self.names.get(name)
    }

    /// The PART classes of `family`.
    pub(crate) fn classes(&self, family: GenFamily) -> &ClassTable {
        match family {
            GenFamily::Versions => &self.classes_versions,
            GenFamily::Kills => &self.classes_kills,
        }
    }

    /// Whether class `c` of `family` leaves `k` out of `h`.
    #[cfg(test)]
    pub(crate) fn class_excludes(&self, family: GenFamily, c: u32, k: NameId) -> bool {
        self.classes(family).classes[c as usize].excludes(&self.names, k)
    }

    /// Plain-mode (`write_rebinds`) rebinders of `read` in the whole-function havoc
    /// list exist — the relation a havoc BASE name carries.
    ///
    /// Trust (2026-09-29): the havoc list names memory an opaque store or a call MAY
    /// write — the pointee trees of the mutable-pointer locals, plus every place a
    /// slot-write channel exposes (`path_defs::own_storage_write_borrow`: `&mut`, `&raw
    /// mut`, `&raw const` of an owned place) WITH its `__slice_len` twin minted
    /// explicitly (`mutably_borrowed_havoc_names`). Dest mode would add the derived channel
    /// (`write_covers_derived_slice_len`) and read the base `s` of `s: &mut [u8]` as a
    /// write of `s__slice_len` — the pointer's own length metadata, which lives in
    /// `s`'s slot and which no store THROUGH `s` can change. That is the false
    /// refutation `dest_write_rebinds`' contract names, and it is what severed every
    /// length tie (`_6__slice_len == digits__slice_len`) in a block that stores an
    /// element through `digits` (see `v2_live_path_defs`).
    pub(crate) fn havoc_rebinds(&self, read: &str) -> bool {
        self.h_index.any_rebinder(read, RebindMode::Plain)
    }

    /// Dest-mode rebinders of `read` in the whole-function havoc list exist.
    pub(crate) fn havoc_dest_rebinds(&self, read: &str) -> bool {
        self.h_index.any_rebinder(read, RebindMode::Dest)
    }

    /// A Dest-mode rebinder of `read` in the whole-function havoc list minus `removed`
    /// (sorted) exists. Every member skipped is in `removed` (a member can be visited
    /// once per relation channel it satisfies), so this is `O(|removed|)` beyond the
    /// lookups.
    pub(crate) fn havoc_dest_rebinds_except(&self, read: &str, removed: &[NameId]) -> bool {
        self.h_index
            .try_for_each_rebinder(read, RebindMode::Dest, |w| {
                if removed.binary_search(&w).is_ok() {
                    ControlFlow::Continue(())
                } else {
                    ControlFlow::Break(())
                }
            })
            .is_break()
    }

    /// [`Self::havoc_dest_rebinds_except`] under the PLAIN relation a havoc base name
    /// carries (see [`Self::havoc_rebinds`]): a rebinder of `read` in the
    /// whole-function havoc list minus `removed` (sorted) exists.
    ///
    /// Trust (2026-10-10, SLICE-LEN-CALL-HAVOC-1): the path-definition fixpoint's
    /// terminator kill judges a call's REFINED havoc list with this.
    pub(crate) fn havoc_rebinds_except(&self, read: &str, removed: &[NameId]) -> bool {
        self.h_index
            .try_for_each_rebinder(read, RebindMode::Plain, |w| {
                if removed.binary_search(&w).is_ok() {
                    ControlFlow::Continue(())
                } else {
                    ControlFlow::Break(())
                }
            })
            .is_break()
    }

    /// Dest-mode rebinders of `read` in the every-local group exist.
    pub(crate) fn all_dest_rebinds(&self, read: &str) -> bool {
        self.all_index.any_rebinder(read, RebindMode::Dest)
            || self.all_derived_index.any_rebinder(read, RebindMode::Dest)
    }

    /// `path_defs::stmt_writes_name(b, j, read)` maximised over `j < i`.
    ///
    /// Exact: each statement's descriptor below enumerates `stmt_writes_name`'s cases
    /// (an `Assign` destination under `dest_write_rebinds`; its index fallback under
    /// `read == _l || write_covers_index_segment`; an opaque deref store's havoc list,
    /// minus the storing pointer's own tree when the store is confined, under
    /// `write_rebinds`; a `SetDiscriminant` place under `write_rebinds`; a `Deinit`
    /// place under `dest_write_rebinds`; a memory-writing `CopyNonOverlapping`'s
    /// every-local list under `write_rebinds`), and the candidates are found by the
    /// rebinder index (`Dest` mode is the widest of the three per-name relations, so it
    /// misses no candidate; each is then re-tested with its own channel).
    ///
    /// A CONFINED store writes `read` iff some havoc name `h` rebinding `read` does not
    /// overlap the store's base; the bases for which EVERY such `h` overlaps are found
    /// by lookup (they overlap the first `h`), and the latest store outside them is
    /// reached by jumping over runs of one base — not by testing every store.
    pub(crate) fn last_writer_before(&self, b: usize, i: usize, read: &str) -> Option<u32> {
        let bw = self.blocks.get(b)?;
        let i = i.min(bw.n_stmts as usize) as u32;
        if i == 0 {
            return None;
        }
        let mut best: Option<u32> = last_before(&self.writer_positions(bw, read), i);
        if !bw.h_unconfined.is_empty() || !bw.confined.is_empty() {
            let mut rebinders: Vec<NameId> = Vec::new();
            self.h_index.for_each_rebinder(read, RebindMode::Plain, |h| rebinders.push(h));
            if !rebinders.is_empty() {
                if let Some(pos) = last_before(&bw.h_unconfined, i) {
                    bump(&mut best, pos);
                }
                if !bw.confined.is_empty() {
                    let failing = self.failing_bases(bw, &rebinders);
                    if let Some(pos) = bw.confined.last_before_outside(i, &failing, best) {
                        bump(&mut best, pos);
                    }
                }
            }
        }
        if !bw.cno.is_empty()
            && self.all_index.any_rebinder(read, RebindMode::Plain)
            && let Some(pos) = last_before(&bw.cno, i)
        {
            bump(&mut best, pos);
        }
        best
    }

    /// `first_writer_before(b, i, read)` = `(0..i).find(|&j| stmt_writes_name(b, j, read))`.
    pub(crate) fn first_writer_before(&self, b: usize, i: usize, read: &str) -> Option<u32> {
        let bw = self.blocks.get(b)?;
        let i = i.min(bw.n_stmts as usize) as u32;
        if i == 0 {
            return None;
        }
        let mut best: Option<u32> = first_before(&self.writer_positions(bw, read), i);
        if best == Some(0) {
            return best;
        }
        if !bw.h_unconfined.is_empty() || !bw.confined.is_empty() {
            let mut rebinders: Vec<NameId> = Vec::new();
            self.h_index.for_each_rebinder(read, RebindMode::Plain, |h| rebinders.push(h));
            if !rebinders.is_empty() {
                if let Some(pos) = first_before(&bw.h_unconfined, i) {
                    lower(&mut best, pos);
                }
                if best != Some(0) && !bw.confined.is_empty() {
                    let failing = self.failing_bases(bw, &rebinders);
                    if let Some(pos) = bw.confined.first_before_outside(i, &failing, best) {
                        lower(&mut best, pos);
                    }
                }
            }
        }
        if best != Some(0)
            && !bw.cno.is_empty()
            && self.all_index.any_rebinder(read, RebindMode::Plain)
            && let Some(pos) = first_before(&bw.cno, i)
        {
            lower(&mut best, pos);
        }
        best
    }

    /// Every statement position of `bw` whose explicitly named write
    /// `stmt_writes_name` admits for `read`, sorted — computed once per `(block, read)`:
    /// a read of a base whose descendants the block writes one by one (`s` against
    /// `s.f_0 = ..; s.f_1 = ..; ..`) has as many rebinders as there are fields, and
    /// visiting them at every statement of the block was quadratic in the block.
    fn writer_positions(&self, bw: &BlockWrites, read: &str) -> Rc<[u32]> {
        if let Some(p) = bw.writer_positions.borrow().get(read) {
            return Rc::clone(p);
        }
        let mut pos: Vec<u32> = Vec::new();
        bw.writer_index.for_each_rebinder(read, RebindMode::Dest, |w| {
            let text = self.names.name(w);
            if let Some(entries) = bw.writer_entries.get(&w) {
                pos.extend(
                    entries
                        .iter()
                        .filter(|&&(_, chan)| chan_admits(chan, text, read))
                        .map(|&(p, _)| p),
                );
            }
        });
        if pos.len() > 1 {
            pos.sort_unstable();
            pos.dedup();
        }
        let pos: Rc<[u32]> = Rc::from(pos);
        bw.writer_positions.borrow_mut().insert(Rc::from(read), Rc::clone(&pos));
        pos
    }

    /// The block's confined-store bases that EVERY havoc name in `rebinders` overlaps
    /// (a store through such a base writes none of them).
    fn failing_bases(&self, bw: &BlockWrites, rebinders: &[NameId]) -> Vec<u32> {
        let Some(&first) = rebinders.first() else { return Vec::new() };
        let mut out = bw.confined.overlapping(self.names.name(first));
        out.retain(|&base| {
            let text = bw.confined.bases.name(base);
            rebinders.iter().all(|&h| place_names_overlap(self.names.name(h), text))
        });
        out
    }

    /// `(∃ w ∈ writes_until(b, i): dest_write_rebinds(w, read),
    ///   ∃ w ∈ writes_until(b, i): write_rebinds(w, read))` — exactly.
    ///
    /// `writes_until(b, i)` is the union of (1) the monotone destination part (explicit
    /// destinations and index fallbacks of `stmts[..i]`, the every-local list of a
    /// memory-writing `CopyNonOverlapping` in `stmts[..i]`, and the derived twins of
    /// all of these), (2) the prefix deref-store havoc (`deref_store_havoc_names_over`:
    /// the whole list once an unconfined opaque store is in the prefix, else per
    /// confined store the list minus the store's own tree), and (3) the definition
    /// names of the prefix extraction with their derived twins. (1) and (2) are
    /// answered exactly from the index. (3) is answered from the isolated-extraction
    /// superset: when no member of it with `j < i` relates to `read` under
    /// `dest_write_rebinds` (the wider relation), (3) contributes nothing to either
    /// half; otherwise the exact prefix set is used (`BlockWrites::exact_prefix`).
    pub(crate) fn gate(
        &self,
        func: &VerifiableFunction,
        b: usize,
        i: usize,
        read: &str,
    ) -> (bool, bool) {
        let Some(bw) = self.blocks.get(b) else { return (false, false) };
        let i = i.min(bw.n_stmts as usize) as u32;
        if i == 0 {
            return (false, false);
        }
        let mut dest = false;
        let mut plain = false;
        let note = |w: &str, dest: &mut bool, plain: &mut bool| -> ControlFlow<()> {
            *dest = true;
            if !*plain && write_rebinds(w, read) {
                *plain = true;
            }
            if *plain { ControlFlow::Break(()) } else { ControlFlow::Continue(()) }
        };
        let _ = bw.a_index.try_for_each_rebinder(read, RebindMode::Dest, |w| {
            if bw.a_first.get(&w).is_some_and(|&f| f < i) {
                note(self.names.name(w), &mut dest, &mut plain)
            } else {
                ControlFlow::Continue(())
            }
        });
        if !(dest && plain) && bw.cno.first().is_some_and(|&f| f < i) {
            for idx in [&self.all_index, &self.all_derived_index] {
                if idx
                    .try_for_each_rebinder(read, RebindMode::Dest, |w| {
                        note(self.names.name(w), &mut dest, &mut plain)
                    })
                    .is_break()
                {
                    break;
                }
            }
        }
        if !(dest && plain) && (!bw.h_unconfined.is_empty() || !bw.confined.is_empty()) {
            let first_unconfined = bw.h_unconfined.first().copied().unwrap_or(u32::MAX);
            let _ = self.h_index.try_for_each_rebinder(read, RebindMode::Dest, |h| {
                let text = self.names.name(h);
                let written = first_unconfined < i
                    || bw.confined.any_before_outside(i, &bw.confined.overlapping(text));
                if written { note(text, &mut dest, &mut plain) } else { ControlFlow::Continue(()) }
            });
        }
        if dest && plain {
            return (true, true);
        }
        let syn = bw.syn_names(func, b);
        // A superset extracted after a budget trip may be short, so it cannot clear the
        // read: take the exact prefix, as the retired gate always did.
        let syn_hit = syn.truncated
            || syn
                .index
                .try_for_each_rebinder(read, RebindMode::Dest, |s| {
                    if syn.first[s as usize] < i {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                })
                .is_break();
        if !syn_hit {
            return (dest, plain);
        }
        // Exact: a synthetic definition name of the prefix may relate to `read`.
        crate::fn_memo::count_gate_fallbacks();
        let prefix = bw.exact_prefix(func, b, i);
        (prefix.any_rebinder(read, RebindMode::Dest), prefix.any_rebinder(read, RebindMode::Plain))
    }

    /// The retired `gen_out` token of gen'd name `k` at block `b`: `None` for the
    /// terminator marker `s{b}_t`, `Some(j)` for `s{b}_{j}`.
    ///
    /// Exact: the terminator marker when some terminator write name `write_rebinds`
    /// `k` (the explicit names by index; the unrefined havoc list by its index; a
    /// refined list as the havoc list minus its removed names), else the latest
    /// statement writing `k` (`last_writer_before(b, stmts.len(), k)`, the same
    /// `stmt_writes_name` search), else the marker.
    pub(crate) fn out_token(&self, b: usize, k: NameId) -> Option<u32> {
        let bw = &self.blocks[b];
        let text = self.names.name(k);
        if bw.term_index.any_rebinder(text, RebindMode::Plain) {
            return None;
        }
        let term_writes = match &bw.term {
            TermKind::None => false,
            TermKind::Function => self.h_index.any_rebinder(text, RebindMode::Plain),
            TermKind::Refined(removed) => self
                .h_index
                .try_for_each_rebinder(text, RebindMode::Plain, |w| {
                    if removed.binary_search(&w).is_ok() {
                        ControlFlow::Continue(())
                    } else {
                        ControlFlow::Break(())
                    }
                })
                .is_break(),
        };
        if term_writes {
            return None;
        }
        self.last_writer_before(b, bw.n_stmts as usize, text)
    }

    /// Whether block `b`'s gen-set of `family` holds `k` through its `h` part.
    #[cfg(test)]
    pub(crate) fn h_part_holds(&self, b: usize, family: GenFamily, k: NameId) -> bool {
        if !self.in_havoc(k) {
            return false;
        }
        match self.blocks[b].h_mode(family) {
            HMode::None => false,
            HMode::Full => true,
            HMode::Part(c) => !self.class_excludes(family, c, k),
        }
    }

    /// Every name of `block_written_names(b)` with its `gen_out` token (`None` = the
    /// terminator marker), sorted by name id (parity tests).
    #[cfg(test)]
    pub(crate) fn gen_with_tokens(&self, b: usize) -> Vec<(String, Option<u32>)> {
        let bw = &self.blocks[b];
        let mut ids: Vec<NameId> = bw.gen_explicit.clone();
        ids.extend(
            self.h.iter().copied().filter(|&k| self.h_part_holds(b, GenFamily::Versions, k)),
        );
        if bw.gen_all {
            ids.extend(self.all_names());
        }
        ids.sort_unstable();
        ids.dedup();
        ids.into_iter().map(|k| (self.names.name(k).to_string(), self.out_token(b, k))).collect()
    }

    /// Number of stored write entries (instrumentation).
    fn entries(&self) -> u64 {
        self.blocks
            .iter()
            .map(|bw| {
                (bw.writer_entries.values().map(Vec::len).sum::<usize>()
                    + bw.h_unconfined.len()
                    + bw.confined.pos.len()
                    + bw.cno.len()
                    + bw.a_first.len()
                    + bw.gen_explicit.len()
                    + bw.stmt_explicit.len()
                    + bw.term_explicit.len()) as u64
            })
            .sum::<u64>()
            + (self.h.len() + self.all.len() + self.all_derived.len()) as u64
    }

    pub(crate) fn count_entries(&self) {
        crate::fn_memo::count_block_write_entries(self.entries());
    }
}

fn dedup(ids: impl Iterator<Item = NameId>) -> Vec<NameId> {
    let mut v: Vec<NameId> = ids.collect();
    if v.len() > 1 {
        v.sort_unstable();
        v.dedup();
    }
    v
}

fn bump(best: &mut Option<u32>, pos: u32) {
    if best.is_none_or(|b| pos > b) {
        *best = Some(pos);
    }
}

fn lower(best: &mut Option<u32>, pos: u32) {
    if best.is_none_or(|b| pos < b) {
        *best = Some(pos);
    }
}

fn last_before(sorted: &[u32], i: u32) -> Option<u32> {
    let k = sorted.partition_point(|&p| p < i);
    (k > 0).then(|| sorted[k - 1])
}

fn first_before(sorted: &[u32], i: u32) -> Option<u32> {
    sorted.first().copied().filter(|&p| p < i)
}

/// What one block's build reads and writes of the function-level index.
struct BuildCtx<'a> {
    names: &'a mut NameTable,
    h_index: &'a RebindIndex,
    h_nonempty: bool,
    index_locals: &'a IndexLocals,
    classes_versions: &'a mut ClassTable,
    classes_kills: &'a mut ClassTable,
}

impl BlockWrites {
    fn build(
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        ctx: &mut BuildCtx<'_>,
    ) -> BlockWrites {
        let index_locals = ctx.index_locals;
        let n_stmts = block.stmts.len() as u32;
        let mut writer_entries: FxHashMap<NameId, Vec<(u32, Chan)>> = FxHashMap::default();
        let mut h_unconfined: Vec<u32> = Vec::new();
        let mut confined = Confined::default();
        let mut cno: Vec<u32> = Vec::new();
        let mut a_first: FxHashMap<NameId, u32> = FxHashMap::default();

        let note_a = |names: &mut NameTable,
                      a_first: &mut FxHashMap<NameId, u32>,
                      n: &str,
                      pos: u32|
         -> NameId {
            let id = names.intern(n);
            a_first.entry(id).or_insert(pos);
            if !n.ends_with(SLICE_LEN_SUFFIX) {
                let d = names.intern(&format!("{n}{SLICE_LEN_SUFFIX}"));
                a_first.entry(d).or_insert(pos);
            }
            id
        };

        for (j, stmt) in block.stmts.iter().enumerate() {
            let j = j as u32;
            match stmt {
                Statement::Assign { place, .. } => {
                    let dest = crate::place_to_var_name(func, place);
                    let id = note_a(ctx.names, &mut a_first, &dest, j);
                    writer_entries.entry(id).or_default().push((j, Chan::Dest));
                    // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — the union cover, on the
                    // destination's channel, as `stmt_writes_name` tests it.
                    if let Some(cover) = super::union_write_cover_name(func, place) {
                        let cid = note_a(ctx.names, &mut a_first, &cover, j);
                        writer_entries.entry(cid).or_default().push((j, Chan::Dest));
                    }
                    if place.projections.is_empty() && index_locals.contains(place.local) {
                        let fb = local_fallback_name(place.local);
                        let fid = note_a(ctx.names, &mut a_first, &fb, j);
                        writer_entries.entry(fid).or_default().push((j, Chan::Fallback));
                    }
                    // Trust: 2026-10-11 (LAUNDERED-ALIAS-STORE) — the one havoc predicate
                    // the retired oracle asks too (`stmt_writes_name`): an opaque deref
                    // store, or a write into escaped storage a laundered pointer can read.
                    if super::write_havocs_function_list(func, place) {
                        if super::opaque_store_confined_to_written_place(func, place) {
                            let base = crate::place_to_var_name(
                                func,
                                &trust_types::Place::local(place.local),
                            );
                            confined.push(j, &base);
                        } else {
                            h_unconfined.push(j);
                        }
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    let chan = if matches!(stmt, Statement::Deinit { .. }) {
                        Chan::Dest
                    } else {
                        Chan::Plain
                    };
                    let dest = crate::place_to_var_name(func, place);
                    let id = note_a(ctx.names, &mut a_first, &dest, j);
                    writer_entries.entry(id).or_default().push((j, chan));
                    // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — the union cover, on the
                    // same channel.
                    if let Some(cover) = super::union_write_cover_name(func, place) {
                        let cid = note_a(ctx.names, &mut a_first, &cover, j);
                        writer_entries.entry(cid).or_default().push((j, chan));
                    }
                    // `extend_with_assigned_place_dests` mints the fallback for every
                    // whole-local destination of these three statement kinds.
                    if place.projections.is_empty() && index_locals.contains(place.local) {
                        note_a(ctx.names, &mut a_first, &local_fallback_name(place.local), j);
                    }
                }
                Statement::CopyNonOverlapping { .. } => {
                    if super::copy_nonoverlapping_writes_memory(stmt) {
                        cno.push(j);
                    }
                }
                _ => {}
            }
        }
        confined.finish();

        // ---- The explicit part of the gen-sets: `block_written_names` /
        // `block_entry_fact_kill_names` minus their `h` and every-local parts.
        // `a_first` already holds every statement destination (`place_to_var_name`,
        // `union_write_cover_name`, and `local_fallback_name`) plus its derived
        // `__slice_len` twin from the forward pass above.
        let intern_with_slice_len = |names: &mut NameTable, out: &mut Vec<NameId>, n: &str| {
            out.push(names.intern(n));
            if !n.ends_with(SLICE_LEN_SUFFIX) {
                out.push(names.intern(&format!("{n}{SLICE_LEN_SUFFIX}")));
            }
        };
        let mut stmt_explicit_ids: Vec<NameId> = a_first.keys().copied().collect();
        let mut defs = crate::guards::extract_block_definitions(func, block);
        defs.extend(super::extract_set_discriminant_definitions(func, block));
        for def in &defs {
            if let Some(n) = formula_def_name(def) {
                intern_with_slice_len(ctx.names, &mut stmt_explicit_ids, n);
            }
        }
        // Trust (triage ticket 216): as in `extend_with_assigned_place_dests`, a
        // `SetDiscriminant` also writes the synthetic `discr_<place>` and tag-field
        // names, including when its definitions were refused. Gen-set only:
        // `stmt_writes_name` tests a `SetDiscriminant` against its place alone, so
        // these names take the terminator OUT token there and here alike.
        for stmt in &block.stmts {
            if let Statement::SetDiscriminant { place, .. } = stmt {
                for n in super::set_discriminant_synthetic_write_names(func, place)
                    .into_iter()
                    .flatten()
                {
                    intern_with_slice_len(ctx.names, &mut stmt_explicit_ids, &n);
                }
            }
        }
        let stmt_explicit: Vec<NameId> = dedup(stmt_explicit_ids.into_iter());

        // ---- The terminator: its explicit names, and how it havocs `h`.
        let term_defs = super::terminator_def_names_structured(func, block);
        let mut term_ids: Vec<NameId> = Vec::new();
        let term = match &term_defs.havoc {
            TermHavoc::None => TermKind::None,
            TermHavoc::Function => TermKind::Function,
            TermHavoc::Refined(delta) => {
                let h_index = ctx.h_index;
                let in_h = |n: &str| h_index.contains(n).is_some();
                for n in delta.added(&in_h) {
                    term_ids.push(ctx.names.intern(&n));
                }
                let removed: Vec<NameId> =
                    dedup(delta.removed(&in_h).iter().map(|n| ctx.names.intern(n)));
                TermKind::Refined(Rc::from(removed))
            }
            TermHavoc::Escape(e) => {
                let removed: Vec<NameId> = dedup(e.dropped.iter().map(|n| ctx.names.intern(n)));
                TermKind::Refined(Rc::from(removed))
            }
        };
        for e in &term_defs.extra {
            let (TermExtra::Push(n) | TermExtra::PushIfAbsent(n)) = e;
            term_ids.push(ctx.names.intern(n));
        }
        let term_explicit = dedup(term_ids.iter().copied());
        let gen_explicit = dedup(stmt_explicit.iter().chain(&term_explicit).copied());

        // ---- How each gen-set family holds `h`.
        let term_removed = match &term {
            TermKind::Refined(r) => Some(Rc::clone(r)),
            _ => None,
        };
        // `block_deref_store_havoc_names`: the whole list once any store is
        // unconfined; else, per confined store, the list minus its tree (the store's
        // own place is an explicit destination already).
        let h_versions =
            if (ctx.h_nonempty && !h_unconfined.is_empty()) || matches!(term, TermKind::Function) {
                HMode::Full
            } else {
                let bases = (ctx.h_nonempty && !confined.is_empty()).then(|| {
                    let mut b: Vec<Rc<str>> = (0..confined.bases.len() as NameId)
                        .map(|id| Rc::from(confined.bases.name(id)))
                        .collect();
                    b.sort_unstable();
                    Rc::<[Rc<str>]>::from(b)
                });
                let removed = term_removed.clone().filter(|_| ctx.h_nonempty);
                if bases.is_none() && removed.is_none() {
                    HMode::None
                } else {
                    HMode::Part(ctx.classes_versions.intern(Exclusion { bases, removed }))
                }
            };
        // `block_entry_fact_kill_names` takes the RAW list (`deref_store_havoc_names`)
        // for any opaque store, confined or not.
        let h_kills = if matches!(term, TermKind::Function)
            || !h_unconfined.is_empty()
            || !confined.is_empty()
        {
            HMode::Full
        } else if let Some(removed) = term_removed.filter(|_| ctx.h_nonempty) {
            HMode::Part(ctx.classes_kills.intern(Exclusion { bases: None, removed: Some(removed) }))
        } else {
            HMode::None
        };

        let writer_index = RebindIndex::build(ctx.names, writer_entries.keys().copied());
        let a_index = RebindIndex::build(ctx.names, a_first.keys().copied());
        let term_index = RebindIndex::build(ctx.names, term_ids.iter().copied());
        BlockWrites {
            n_stmts,
            writer_entries,
            writer_index,
            h_unconfined,
            confined,
            gen_all: !cno.is_empty(),
            cno,
            a_first,
            a_index,
            gen_explicit,
            stmt_explicit,
            term_explicit,
            term,
            h_versions,
            h_kills,
            term_index,
            stmt_index: OnceCell::new(),
            syn: RefCell::new(None),
            exact_prefix: RefCell::new(None),
            writer_positions: RefCell::new(FxHashMap::default()),
        }
    }

    fn syn_names(&self, func: &VerifiableFunction, b: usize) -> Rc<SynNames> {
        if let Some(s) = self.syn.borrow().as_ref() {
            return Rc::clone(s);
        }
        let block = &func.body.blocks[b];
        let mut table = NameTable::default();
        let mut first: Vec<u32> = Vec::new();
        let note = |table: &mut NameTable, first: &mut Vec<u32>, n: &str, j: u32| {
            let id = table.intern(n) as usize;
            if id == first.len() {
                first.push(j);
            }
        };
        for j in 0..block.stmts.len() {
            let mut defs = crate::guards::extract_statement_definitions_isolated(func, block, j);
            if let Statement::SetDiscriminant { place, variant_index } = &block.stmts[j]
                && let Ok(sd) = super::set_discriminant_definitions(func, place, *variant_index)
            {
                defs.extend(sd);
            }
            for d in &defs {
                if let Some(n) = formula_def_name(d) {
                    note(&mut table, &mut first, n, j as u32);
                    if !n.ends_with(SLICE_LEN_SUFFIX) {
                        note(&mut table, &mut first, &format!("{n}{SLICE_LEN_SUFFIX}"), j as u32);
                    }
                }
            }
        }
        let index = RebindIndex::build(&table, 0..table.len() as NameId);
        let truncated = trust_types::verify_budget::exhausted_readonly();
        let syn = Rc::new(SynNames { first, index, truncated });
        *self.syn.borrow_mut() = Some(Rc::clone(&syn));
        syn
    }

    /// `writes_until(b, i)` exactly, indexed, and kept for the block's most recent
    /// point: the gate's fallback is a pure function of `(b, i)`, and the rename asks
    /// it once per free variable of every entry fact AT THE SAME POINT, so one slot
    /// per block turns those into one extraction. (A slot, not a map: a map over every
    /// point ever asked would hold Θ(statements²) names on a long block — the retired
    /// `writes_until` memo, which needed a size cap for exactly that.)
    fn exact_prefix(&self, func: &VerifiableFunction, b: usize, i: u32) -> Rc<RebindIndex> {
        if let Some((at, p)) = self.exact_prefix.borrow().as_ref()
            && *at == i
        {
            return Rc::clone(p);
        }
        crate::fn_memo::count_writes_until();
        let block = &func.body.blocks[b];
        let ws = super::writes_until_uncached(func, block, i as usize);
        let mut table = NameTable::default();
        let ids: Vec<NameId> = ws.iter().map(|w| table.intern(w)).collect();
        let prefix = Rc::new(RebindIndex::build(&table, ids));
        *self.exact_prefix.borrow_mut() = Some((i, Rc::clone(&prefix)));
        prefix
    }

    pub(crate) fn gen_explicit(&self) -> &[NameId] {
        &self.gen_explicit
    }

    pub(crate) fn stmt_explicit(&self) -> &[NameId] {
        &self.stmt_explicit
    }

    pub(crate) fn term_explicit(&self) -> &[NameId] {
        &self.term_explicit
    }

    /// How this block's gen-set of `family` holds the whole-function havoc list.
    pub(crate) fn h_mode(&self, family: GenFamily) -> HMode {
        match family {
            GenFamily::Versions => self.h_versions,
            GenFamily::Kills => self.h_kills,
        }
    }

    /// The block contains an OPAQUE deref store (`deref_store_havoc_names` is the
    /// whole-function list here, not empty).
    pub(crate) fn any_opaque_store(&self) -> bool {
        !self.h_unconfined.is_empty() || !self.confined.is_empty()
    }

    pub(crate) fn gen_all(&self) -> bool {
        self.gen_all
    }

    /// Whether some name of the block's STATEMENT kill gen-set explicit part
    /// (`stmt_explicit`) `dest_write_rebinds` `read` — the may-reassigned probe's
    /// own-block test, by lookup.
    pub(crate) fn stmt_explicit_dest_rebinds(&self, names: &NameTable, read: &str) -> bool {
        self.stmt_index
            .get_or_init(|| RebindIndex::build(names, self.stmt_explicit.iter().copied()))
            .any_rebinder(read, RebindMode::Dest)
    }
}
