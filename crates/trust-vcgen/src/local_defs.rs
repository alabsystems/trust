//! THE ONE SEAM for "how many values can this local hold?" and "what is its value?".
//!
//! # The channel set
//!
//! A local receives a value through SEVERAL channels, and the class of bugs this
//! module exists to close is a scan that enumerates a PROPER SUBSET of them. The
//! complete set is `trust_types::LocalWrite`, produced by `Statement::local_write` and
//! `Terminator::local_write`. Those two classifiers live in `trust-types` rather than
//! here because `Statement` and `Terminator` are `#[non_exhaustive]`: only their own
//! crate can match them WITHOUT A WILDCARD, and only a wildcard-free match makes a new
//! MIR variant a COMPILE ERROR until it is classified. On top of that set there is
//! exactly one further channel, the one that is not a statement or a terminator at all:
//!
//!  * every PARAMETER (`1..=arg_count`) is defined at ENTRY, implicitly. No statement
//!    anywhere in the body carries that definition, so no block scan can see it.
//!  * everything else is one of the `LocalWrite` variants.
//!
//! The classifiers are checked against the model's OWN write-completeness taxonomy,
//! `trust_types::WriteEffect`: `LocalWrite::agrees_with` is asserted on every statement
//! and terminator [`for_each_local_write`] visits (debug builds — which is every test
//! run, over every corpus body) and is exercised variant-by-variant in
//! `trust_types::model_write_channel_tests`. Re-classifying a variant's `WriteEffect`
//! without re-classifying its channel therefore fails a test, and ADDING a variant
//! fails the build.
//!
//! `LocalWrite` is deliberately not `#[non_exhaustive]`, so every EXPORTED QUESTION
//! below — each written as a wildcard-free match over it — stops compiling when a
//! channel is added.
//!
//! # Why a subset is a false proof
//!
//! A predicate that scans a subset of the channels reads a local written through the
//! others as SINGLE-VALUED. Facts keyed on that reading are emitted against the
//! local's BARE name, `generate::safety` conjoins them into `vc.formula` BEFORE
//! `conjoin_preconditions_versioned_recorded` renames the whole formula, and the
//! rename binds the fact to whichever version is terminal in the block under proof —
//! including a version that never ran the write the scan did see. The fact is FALSE of
//! that value, the path condition goes UNSAT, and every obligation on the emptied path
//! is proved VACUOUSLY and kernel-certified. A RESOLVER is worse still: its answer is
//! INLINED into a formula, so version renaming cannot rebind a wrong one afterwards.
//!
//! Callers ask one of the exported questions below. The generic body walk and the
//! count/unique-value interpretation live in `trust_types::local_defs`, shared with
//! the IR bridge. This module retains indexed traversal, memoization and its escape
//! classification. Each interpretation exhaustively matches [`LocalWrite`] here
//! or in the shared reducer — [`body_value_count`], [`body_never_explicitly_reseated`],
//! [`body_unique_value_def`], [`body_value_defs`], [`body_unique_initializing_def`],
//! [`body_unique_value_call`], [`body_unique_initializing_call`], [`body_value_calls`],
//! [`body_is_single_static_assignment`], [`body_path_is_single_static_assignment`],
//! [`body_dest_fact_is_version_pinnable`], [`body_stmt_dest_fact_is_version_pinnable_at`],
//! [`body_unique_defining_block`],
//! [`body_storage_never_aliased`], [`body_pointer_is_pinned`],
//! [`body_unique_value_modulo_whole_drops`], [`body_unique_initializing_modulo_whole_drops`]
//! — and the
//! remaining two ([`body_holds_one_value`], [`body_has_one_explicit_def`]) are
//! compositions of those. So a new channel forces
//! every question to state what it does with it, at compile time, with no site left to
//! inherit an unstated default. The two READ walks in this module,
//! [`body_reads_are_whole_local_uses`] (the call-through-temp admission of
//! [`body_value_calls`]) and the alias half of [`body_storage_never_aliased`], must carry
//! wildcards over the `#[non_exhaustive]` MIR enums, and every wildcard arm there
//! REFUSES — an unrecognised construct is never read as absent.
//!
//! # One predicate cannot answer two questions
//!
//! [`body_is_single_static_assignment`] and [`body_dest_fact_is_version_pinnable`] are
//! deliberately SEPARATE and differ on exactly one shape — a `mut` parameter written by
//! one `Call` destination. They are the two halves of a gate that used to be one, and
//! the split is load-bearing IN BOTH DIRECTIONS:
//!
//!  * A fact keyed on a local's BARE NAME is a claim about every point in the function,
//!    so a parameter's entry definition refutes it. That is
//!    [`body_is_single_static_assignment`], and admitting the parameter there is a
//!    live kernel-certified false proof (`wc` below).
//!  * A fact PINNED to a post-call version token is a claim about one spelling that the
//!    entry value is never read under. That is
//!    [`body_dest_fact_is_version_pinnable`], and refusing the parameter there costs
//!    real proofs and buys nothing.
//!
//! The witness for the first half, refuted by the runtime oracle at 51,200 of 131,072
//! inputs and PROVED + kernel-certified before the parameter arm existed:
//!
//! ```ignore (illustrative)
//! pub fn wc(mut i: u8, j: u8, c: bool) -> u8 {
//!     if c { i = j.min(3); }
//!     i + 200                     // `i <= 3` was emitted as a GLOBAL fact on `i`
//! }
//! ```
//!
//! Asking the bare-name question at the version-pinned site (or the reverse) is the
//! defect, not the answer either one gives.
//!
//! # Absence of information is not a value
//!
//! Two of the six channels report that a write MAY have happened somewhere the seam
//! cannot see: [`LocalWrite::Unlocatable`] (no destination `Place` at all) and
//! [`LocalWrite::Escape`] (a mutable alias, through which a later store names a
//! DIFFERENT place). Neither is one value, and neither is zero values. A question that
//! grants a license ought therefore to DECLINE on them — answer "I do not know", not
//! "exactly one" — which is why [`body_value_count`] answers a
//! [`trust_types::ValueCount`] and not a `usize`: a `usize` licenses in one direction
//! or disqualifies in the other, and an unlocated write has to do both.
//!
//! [`LocalWrite::Unlocatable`] is handled that way everywhere. [`LocalWrite::Escape`] is
//! handled that way in every question that GRANTS A LICENSE OVER A VALUE:
//! [`body_is_single_static_assignment`], [`body_dest_fact_is_version_pinnable`],
//! [`body_unique_defining_block`], [`body_unique_value_call`] — and, since 2026-09-15,
//! the resolver [`body_unique_value_def`], whose admission of the channel WAS a live,
//! kernel-certified false proof (`x3::pesc`; read that function's `Escape` arm for the
//! witness, the measured cost and what a precision recovery would have to supply).
//!
//! [`body_unique_initializing_def`] is the one place the channel is readmitted ON
//! PURPOSE, and it is a DIFFERENT QUESTION — "what was this local BUILT FROM", true
//! only at the point after its one `Assign` — with the caller-side obligation written
//! on it. It grants no value license. Since 2026-09-16 it has exactly ONE caller,
//! `generate::iterator_yield::iterator_origin_def`, which supplies the obligation
//! (the affirmative `iter_mut_borrows_only_feed_next` allow-list plus the yield-set
//! argument) and is the sole entrance for the `for`-loop iterator tracers; nothing
//! else may call it without writing its own argument in the same form.
//!
//! A BLIND SPOT SHARED BY EVERY QUESTION HERE AND BY
//! `generate::witness_grounding::local_escapes_anywhere`, recorded 2026-09-16 as LIVE
//! (currently unreachable from stable Rust, not conditional): rustc 1.99's
//! `mir::Rvalue::Reborrow(Ty, Mutability, Place)` — a mutable reborrow of a user ADT
//! through the unstable `Reborrow`/`CoerceShared` traits — is lowered by
//! `trust-mir-extract`'s `convert.rs` to `Rvalue::Unsupported { operands: [Copy(place)] }`.
//! That rvalue is NOT `Rvalue::Ref { mutable: true }` and NOT `Rvalue::AddressOf`, so
//! `trust_types::Statement::escapes_local` does not put the reborrowed local on the
//! [`LocalWrite::Escape`] channel, and `LocalWrite::of_place` sees no write at all;
//! and vcgen does not fail a body closed for containing such a statement. A mutable
//! alias minted that way is therefore invisible to the resolver, to the origin
//! question's gate, and to the witness-grounding escape check alike. Until
//! `escapes_local` classifies the `Unsupported` reborrow as an escape (or the
//! extractor fails the body closed), every answer in this module is stated modulo
//! that operator. It is a fact about today's lowering, not a rule.
//!
//! ONE ADMISSION REMAINS ON A VALUE QUESTION, and it is the COUNTING channel:
//! [`body_value_count`] does not CHARGE an alias, because an alias is not itself a
//! value and the count is also consumed as a storage-slot question — so
//! [`body_holds_one_value`] and [`body_has_one_explicit_def`], which are compositions
//! of it, still inherit the admission. That residual is declared in the count's own
//! arm, together with the measured reason it is still open, and it is WEAKER than the
//! resolver's was: a count-keyed fact is emitted against the local's BARE NAME and can
//! still be rebound by version renaming, whereas a resolver answer is INLINED and
//! cannot. [`body_unique_defining_block`], the one layered question that grants a
//! dominance license, disqualifies the channel for itself.

use trust_types::local_defs::LocalDefinitionSummary;
use trust_types::{LocalWrite, Rvalue, Terminator, ValueCount, VerifiableBody, VerifiableFunction};

/// True iff `local` is a function PARAMETER (locals `1..=arg_count`) — the locals
/// that carry an implicit ENTRY definition. The return place (`_0`) is not one.
pub(crate) fn body_is_parameter(body: &VerifiableBody, local: usize) -> bool {
    trust_types::local_defs::is_parameter(body.arg_count, local)
}

/// Visit EVERY channel by which a value can reach `local` inside `body.blocks`, with
/// the index in `body.blocks` of the block it is in.
///
/// The ENTRY definition is deliberately NOT visited: it is not in any block, and every
/// exported question below adds it explicitly via [`body_is_parameter`].
fn for_each_local_write<'a>(
    body: &'a VerifiableBody,
    local: usize,
    f: impl FnMut(usize, LocalWrite<'a>),
) {
    for_each_local_write_classified(body, local, escapes_wide, f)
}

/// An ESCAPE classifier of the walkers below: does `stmt` hand out an alias through
/// which `local`'s storage may be written? Takes the body because a SHARED borrow is an
/// escape exactly when it covers `UnsafeCell` bytes, which only the body's typing says.
type EscapeClassifier = fn(&VerifiableBody, &trust_types::Statement, usize) -> bool;

/// The wide classifier: `crate::body_stmt_escapes_local` — `&mut`, `&raw` of any place
/// rooted at `local`, or a shared borrow of `local`'s own storage that covers an
/// `UnsafeCell` byte. Trust: 2026-10-15 (INTERIOR-MUT-CHANNEL-1): until then this module
/// passed the cell-blind `Statement::escapes_local`, so `poke(&c)` for an owned
/// `c: Cell<usize>` left `c` with one value.
fn escapes_wide(body: &VerifiableBody, stmt: &trust_types::Statement, local: usize) -> bool {
    crate::body_stmt_escapes_local(body, stmt, local)
}

/// The narrow classifier: `Statement::escapes_local_storage` (a borrow THROUGH a
/// pointer local's `Deref` reaches its pointee, not its slot) plus the same
/// shared-borrow-of-a-cell clause as [`escapes_wide`] (a pointer slot holds no cell, so
/// the clause never fires for the pointer locals the narrow callers ask about).
fn escapes_storage(body: &VerifiableBody, stmt: &trust_types::Statement, local: usize) -> bool {
    trust_types::local_defs::statement_escapes_local_storage(body, stmt, local)
}

/// [`for_each_local_write`] with the ESCAPE classifier as a parameter, so exactly one
/// walker serves both questions and a new MIR channel cannot be classified in one and
/// forgotten in the other.
///
/// Trust: 2026-09-17 (round A12, pass 2) — `escapes` is [`escapes_wide`] for every
/// caller but [`body_unique_value_def_modulo_pointee_borrows`] (and its SSA twin) and
/// [`body_pointer_is_pinned`], which pass the narrower [`escapes_storage`]
/// ([`trust_types::Statement::escapes_local_storage`] plus the cell clause) and each
/// carry the argument that licenses it. Nothing else in this module may pass the
/// narrow one.
///
/// When the body is the one the innermost `generate::FuncAnalysisScope` holds, the
/// walk visits only the items [`LocalWriteIndex`] lists for `local` — every other item
/// answers [`LocalWrite::Untouched`] with no escape, which every caller treats as a
/// no-op — instead of the whole body once per question (the extraction asks one per
/// statement it lowers, so the full walk was quadratic in the body).
fn for_each_local_write_classified<'a>(
    body: &'a VerifiableBody,
    local: usize,
    escapes: EscapeClassifier,
    f: impl FnMut(usize, LocalWrite<'a>),
) {
    if let Some(index) = crate::generate::local_write_index_for(body) {
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            let mut indexed: Vec<(usize, LocalWrite<'a>)> = Vec::new();
            index.visit(body, local, escapes, |i, w| indexed.push((i, w)));
            let mut scanned: Vec<(usize, LocalWrite<'a>)> = Vec::new();
            walk_all(body, local, escapes, |i, w| {
                if !matches!(w, LocalWrite::Untouched) {
                    scanned.push((i, w));
                }
            });
            let key = |(i, w): &(usize, LocalWrite<'a>)| {
                let rv = match w {
                    LocalWrite::WholeNamed(rv) => std::ptr::from_ref(*rv) as usize,
                    _ => 0,
                };
                (*i, std::mem::discriminant(w), rv)
            };
            let a: Vec<_> =
                indexed.iter().filter(|e| !matches!(e.1, LocalWrite::Untouched)).map(key).collect();
            let b: Vec<_> = scanned.iter().map(key).collect();
            assert_eq!(a, b, "local-write index disagrees with the full walk for local {local}");
            let mut f = f;
            for (i, w) in indexed {
                f(i, w);
            }
            return;
        }
        index.visit(body, local, escapes, f);
        return;
    }
    crate::fn_memo::count_body_scan_items(
        body.blocks.iter().map(|b| b.stmts.len() as u64 + 1).sum(),
    );
    walk_all(body, local, escapes, f);
}

/// The whole-body walk behind [`for_each_local_write_classified`].
fn walk_all<'a>(
    body: &'a VerifiableBody,
    local: usize,
    escapes: EscapeClassifier,
    mut f: impl FnMut(usize, LocalWrite<'a>),
) {
    trust_types::local_defs::visit_local_writes(
        body,
        local,
        |statement| escapes(body, statement, local),
        |block, _, write| f(block, write),
    );
}

/// [`for_each_local_write`] with each event's ITEM: `(block, Some(statement index))`, or
/// `(block, None)` for the block's TERMINATOR. The same classifiers and the same index
/// ([`LocalWriteIndex::visit_located`]), for the one question that must tell a
/// terminator's write from a statement's in the same block
/// ([`unique_whole_definition_modulo_whole_drops`]).
///
/// Trust: 2026-10-11 (CL-FOLD-LOCALDEF-1).
fn for_each_local_write_located<'a>(
    body: &'a VerifiableBody,
    local: usize,
    mut f: impl FnMut(usize, Option<usize>, LocalWrite<'a>),
) {
    let escapes: EscapeClassifier = escapes_wide;
    if let Some(index) = crate::generate::local_write_index_for(body) {
        index.visit_located(body, local, escapes, |(b, j), w| {
            f(b as usize, (j != TERM_ITEM).then_some(j as usize), w);
        });
        return;
    }
    crate::fn_memo::count_body_scan_items(
        body.blocks.iter().map(|b| b.stmts.len() as u64 + 1).sum(),
    );
    trust_types::local_defs::visit_local_writes(
        body,
        local,
        |statement| escapes(body, statement, local),
        f,
    );
}

/// Terminator position in a [`LocalWriteIndex`] item.
const TERM_ITEM: u32 = u32::MAX;

/// Per local, the items (statements and terminators, as `(block, statement index)`
/// with [`TERM_ITEM`] for the terminator) that can answer anything but
/// [`LocalWrite::Untouched`] for it or hand out an alias of it, plus the items that can
/// for EVERY local (a write with no destination place). Exact by the classifiers'
/// definitions in `trust-types`: `LocalWrite::of_place` is `Untouched` for every local
/// but the place's own, the escape classifiers hold only for a borrow's root local
/// (`&mut` / raw, or a shared borrow of `UnsafeCell` bytes), and the destination-less writes are
/// `Unlocatable` for all. A statement or terminator shape this crate cannot match
/// (both enums are `#[non_exhaustive]`) is listed for every local — the fail-safe
/// direction, since a visited item is classified by the walk itself.
struct DenseLocalMemo<T> {
    cap: usize,
    slots: Vec<Option<T>>,
    overflow: trust_types::fx::FxHashMap<usize, T>,
}

impl<T: Copy> DenseLocalMemo<T> {
    #[inline]
    fn new(cap: usize) -> Self {
        Self { cap, slots: Vec::new(), overflow: Default::default() }
    }

    #[inline]
    fn get(&self, local: usize) -> Option<T> {
        if local < self.cap {
            self.slots.get(local).copied().flatten()
        } else {
            self.overflow.get(&local).copied()
        }
    }

    #[inline]
    fn insert(&mut self, local: usize, val: T) {
        if local < self.cap {
            if self.slots.is_empty() && self.cap > 0 {
                self.slots.resize(self.cap, None);
            }
            if let Some(slot) = self.slots.get_mut(local) {
                *slot = Some(val);
            }
        } else {
            self.overflow.insert(local, val);
        }
    }

    #[inline]
    fn get_or_insert(&mut self, local: usize, val: T) {
        if self.get(local).is_none() {
            self.insert(local, val);
        }
    }
}

struct DenseBoolKeyedLocalMemo<T> {
    cap: usize,
    slots: Vec<[Option<T>; 2]>,
    overflow: trust_types::fx::FxHashMap<(usize, bool), T>,
}

impl<T: Copy> DenseBoolKeyedLocalMemo<T> {
    #[inline]
    fn new(cap: usize) -> Self {
        Self { cap, slots: Vec::new(), overflow: Default::default() }
    }

    #[inline]
    fn get(&self, local: usize, flag: bool) -> Option<T> {
        if local < self.cap {
            self.slots.get(local).and_then(|pair| pair[usize::from(flag)])
        } else {
            self.overflow.get(&(local, flag)).copied()
        }
    }

    #[inline]
    fn insert(&mut self, local: usize, flag: bool, val: T) {
        if local < self.cap {
            if self.slots.is_empty() && self.cap > 0 {
                self.slots.resize(self.cap, [None, None]);
            }
            if let Some(pair) = self.slots.get_mut(local) {
                pair[usize::from(flag)] = Some(val);
            }
        } else {
            self.overflow.insert((local, flag), val);
        }
    }
}

pub(crate) struct LocalWriteIndex {
    by_local: Vec<Vec<(u32, u32)>>,
    by_local_overflow: trust_types::fx::FxHashMap<usize, Vec<(u32, u32)>>,
    universal: Vec<(u32, u32)>,
    /// [`body_value_count`] per local: the extraction asks it for the same locals at
    /// statement after statement, and a local written at `k` items costs `O(k)` per
    /// question even through the index.
    value_counts: std::cell::RefCell<DenseLocalMemo<ValueCount>>,
    /// [`body_unique_value_def`] and [`body_unique_value_def_modulo_pointee_borrows`]
    /// per local (keyed with `true` for the latter's narrower escape classifier), as
    /// the LOCATION of the resolved `Assign` (`None` when there is no unique value) —
    /// for the same reason.
    unique_value_defs: std::cell::RefCell<DenseBoolKeyedLocalMemo<Option<(u32, u32)>>>,
    /// [`body_is_single_static_assignment`] (`false`) and
    /// [`body_is_single_static_assignment_modulo_pointee_borrows`] (`true`) per local.
    single_static_assignment: std::cell::RefCell<DenseBoolKeyedLocalMemo<bool>>,
    /// [`body_slot_is_stable`] per local.
    slot_source_stable: std::cell::RefCell<DenseLocalMemo<bool>>,
    /// [`body_slot_is_stable_modulo_whole_drops`] per local.
    slot_source_stable_modulo_whole_drops: std::cell::RefCell<DenseLocalMemo<bool>>,
    /// [`body_unique_defining_block`] per local.
    unique_defining_block: std::cell::RefCell<DenseLocalMemo<Option<usize>>>,
    /// [`body_unique_value_modulo_whole_drops`] (`false`) and
    /// [`body_unique_initializing_modulo_whole_drops`] (`true`) per local, as the
    /// location `(block, stmt_or_TERM_ITEM)` of the resolved definition (`None` when
    /// there is no unique whole definition).
    unique_whole_defs_modulo_whole_drops:
        std::cell::RefCell<DenseBoolKeyedLocalMemo<Option<(u32, u32)>>>,
}

impl LocalWriteIndex {
    pub(crate) fn build(body: &VerifiableBody) -> LocalWriteIndex {
        use trust_types::Statement;
        let n_locals = body.locals.len();
        let mut by_local: Vec<Vec<(u32, u32)>> = vec![Vec::new(); n_locals];
        let mut by_local_overflow: trust_types::fx::FxHashMap<usize, Vec<(u32, u32)>> =
            Default::default();
        let mut push_local = |local: usize, item: (u32, u32)| {
            if let Some(bucket) = by_local.get_mut(local) {
                bucket.push(item);
            } else {
                by_local_overflow.entry(local).or_default().push(item);
            }
        };
        let mut universal: Vec<(u32, u32)> = Vec::new();
        let mut items = 0u64;
        for (b, block) in body.blocks.iter().enumerate() {
            let b = b as u32;
            for (j, stmt) in block.stmts.iter().enumerate() {
                items += 1;
                let item = (b, j as u32);
                let mut keys: [Option<usize>; 2] = [None, None];
                match stmt {
                    Statement::Assign { place, rvalue, .. } => {
                        keys[0] = Some(place.local);
                        if let Rvalue::Ref { mutable: true, place: borrowed }
                        | Rvalue::AddressOf(_, borrowed) = rvalue
                        {
                            keys[1] = Some(borrowed.local);
                        } else if let Rvalue::Ref { mutable: false, .. } = rvalue
                            && let Some((root, _)) =
                                crate::generate::shared_borrow_cell_places(body, stmt)
                        {
                            // A SHARED borrow escapes its root exactly when it covers
                            // `UnsafeCell` bytes (`escapes_wide` / `escapes_storage`,
                            // INTERIOR-MUT-CHANNEL-1), so it is listed exactly then.
                            // Trust: 2026-10-15 (G2-INDEX-LINEAR-1): listing EVERY shared
                            // borrow put each `&*self` of `n` calls on `self`'s list, and
                            // every question about `self` visited all `n` (Θ(n²); the
                            // `shared_reborrow_calls` rung grew 3.76x). A shared borrow of
                            // `Freeze` bytes, or through a `Deref`, answers `Untouched`
                            // with no escape for the borrowed local, so leaving it off
                            // changes no answer.
                            keys[1] = Some(root);
                        }
                    }
                    Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                        keys[0] = Some(place.local);
                    }
                    Statement::Retag { .. }
                    | Statement::PlaceMention(_)
                    | Statement::StorageLive(_)
                    | Statement::StorageDead(_)
                    | Statement::Coverage
                    | Statement::ConstEvalCounter
                    | Statement::Nop => {}
                    // `Intrinsic`, `CopyNonOverlapping`, `Unsupported` (`Unlocatable`
                    // for every local) and any shape added later.
                    _ => universal.push(item),
                }
                if keys[0].is_some() && keys[0] == keys[1] {
                    keys[1] = None;
                }
                for l in keys.into_iter().flatten() {
                    push_local(l, item);
                }
            }
            items += 1;
            let item = (b, TERM_ITEM);
            match &block.terminator {
                Terminator::Call { dest, .. } => push_local(dest.local, item),
                Terminator::TailCall { .. } => push_local(0, item),
                Terminator::Drop { place, .. } => {
                    push_local(place.local, item);
                }
                Terminator::Goto(_)
                | Terminator::SwitchInt { .. }
                | Terminator::Return
                | Terminator::Assert { .. }
                | Terminator::Unreachable
                | Terminator::Resume => {}
                // `Opaque` (`Unlocatable` for every local) and any shape added later.
                _ => universal.push(item),
            }
        }
        crate::fn_memo::count_body_scan_items(items);
        LocalWriteIndex {
            by_local,
            by_local_overflow,
            universal,
            value_counts: std::cell::RefCell::new(DenseLocalMemo::new(n_locals)),
            unique_value_defs: std::cell::RefCell::new(DenseBoolKeyedLocalMemo::new(n_locals)),
            single_static_assignment: std::cell::RefCell::new(DenseBoolKeyedLocalMemo::new(
                n_locals,
            )),
            slot_source_stable: std::cell::RefCell::new(DenseLocalMemo::new(n_locals)),
            slot_source_stable_modulo_whole_drops: std::cell::RefCell::new(DenseLocalMemo::new(
                n_locals,
            )),
            unique_defining_block: std::cell::RefCell::new(DenseLocalMemo::new(n_locals)),
            unique_whole_defs_modulo_whole_drops: std::cell::RefCell::new(
                DenseBoolKeyedLocalMemo::new(n_locals),
            ),
        }
    }

    #[inline]
    fn items_for_local(&self, local: usize) -> &[(u32, u32)] {
        match self.by_local.get(local) {
            Some(items) => items.as_slice(),
            None => self.by_local_overflow.get(&local).map_or(&[], Vec::as_slice),
        }
    }

    /// The per-local cache [`body_slot_is_stable_modulo_whole_drops`] fills (`None` until
    /// it has answered for `local` through this index), so a fixture can show that the
    /// indexed visit, and not the unindexed fallback, produced an answer.
    #[cfg(test)]
    pub(crate) fn cached_slot_stable_modulo_whole_drops(&self, local: usize) -> Option<bool> {
        self.slot_source_stable_modulo_whole_drops.borrow().get(local)
    }

    /// Short-circuiting visit over each `(block, statement index)` item
    /// ([`TERM_ITEM`] for the terminator) listed for `local` or in `universal`,
    /// in body order, without bumping `body_scan_items`.
    fn find_raw_item<R>(&self, local: usize, mut f: impl FnMut((u32, u32)) -> Option<R>) -> Option<R> {
        let own = self.items_for_local(local);
        let (mut a, mut b) = (0usize, 0usize);
        loop {
            let item = match (own.get(a), self.universal.get(b)) {
                (None, None) => return None,
                (Some(&x), None) => {
                    a += 1;
                    x
                }
                (None, Some(&y)) => {
                    b += 1;
                    y
                }
                (Some(&x), Some(&y)) => {
                    if x <= y {
                        a += 1;
                        if x == y {
                            b += 1;
                        }
                        x
                    } else {
                        b += 1;
                        y
                    }
                }
            };
            if let Some(out) = f(item) {
                return Some(out);
            }
        }
    }

    /// Visits each `(block, statement index)` item ([`TERM_ITEM`] for the terminator)
    /// listed for `local` or in `universal`, in body order, without bumping
    /// `body_scan_items`.
    fn visit_raw_items(&self, local: usize, mut f: impl FnMut((u32, u32))) {
        let _ = self.find_raw_item(local, |item| {
            f(item);
            None::<()>
        });
    }

    /// [`for_each_local_write_classified`]'s visit, over the listed items only, in
    /// body order.
    fn visit<'a>(
        &self,
        body: &'a VerifiableBody,
        local: usize,
        escapes: EscapeClassifier,
        mut f: impl FnMut(usize, LocalWrite<'a>),
    ) {
        self.visit_located(body, local, escapes, |(b, _), w| f(b as usize, w));
    }

    /// [`Self::visit`], with each event's item `(block, statement index)` ([`TERM_ITEM`]
    /// for the terminator).
    fn visit_located<'a>(
        &self,
        body: &'a VerifiableBody,
        local: usize,
        escapes: EscapeClassifier,
        mut f: impl FnMut((u32, u32), LocalWrite<'a>),
    ) {
        let own = self.items_for_local(local);
        crate::fn_memo::count_body_scan_items((own.len() + self.universal.len()) as u64);
        let (mut a, mut b) = (0usize, 0usize);
        loop {
            let item = match (own.get(a), self.universal.get(b)) {
                (None, None) => break,
                (Some(&x), None) => {
                    a += 1;
                    x
                }
                (None, Some(&y)) => {
                    b += 1;
                    y
                }
                (Some(&x), Some(&y)) => {
                    if x <= y {
                        a += 1;
                        if x == y {
                            b += 1;
                        }
                        x
                    } else {
                        b += 1;
                        y
                    }
                }
            };
            let (bi, j) = (item.0 as usize, item.1);
            let block = &body.blocks[bi];
            if j == TERM_ITEM {
                let write = block.terminator.local_write(local);
                debug_assert!(
                    write.agrees_with(block.terminator.write_effect()),
                    "terminator channel classification disagrees with WriteEffect: {:?}",
                    block.terminator
                );
                f(item, write);
            } else {
                let stmt = &block.stmts[j as usize];
                let write = stmt.local_write(local);
                debug_assert!(
                    write.agrees_with(stmt.write_effect()),
                    "statement channel classification disagrees with WriteEffect: {stmt:?}"
                );
                f(item, write);
                if escapes(body, stmt, local) {
                    f(item, LocalWrite::Escape);
                }
            }
        }
    }

    /// [`Self::visit_located`] with the slot rule's classifier
    /// (`trust_types::local_defs::statement_escapes_local_slot`, the one the unindexed
    /// `source_slot_is_stable` walk asks) and without bumping `body_scan_items`, for the
    /// slot-stability queries whose unindexed `trust_types::local_defs` walks do not bump
    /// `body_scan_items`. Its two consumers ([`body_slot_is_stable`],
    /// [`body_slot_is_stable_modulo_whole_drops`]) are differentially checked against
    /// those walks, and `tests/write_channel_rule_is_not_restated.rs` admits the cell-blind
    /// slot classifier in this crate only here.
    fn visit_located_slot_writes<'a>(
        &self,
        body: &'a VerifiableBody,
        local: usize,
        mut f: impl FnMut(usize, Option<usize>, LocalWrite<'a>),
    ) {
        let own = self.items_for_local(local);
        let (mut a, mut b) = (0usize, 0usize);
        loop {
            let item = match (own.get(a), self.universal.get(b)) {
                (None, None) => break,
                (Some(&x), None) => {
                    a += 1;
                    x
                }
                (None, Some(&y)) => {
                    b += 1;
                    y
                }
                (Some(&x), Some(&y)) => {
                    if x <= y {
                        a += 1;
                        if x == y {
                            b += 1;
                        }
                        x
                    } else {
                        b += 1;
                        y
                    }
                }
            };
            let (bi, j) = (item.0 as usize, item.1);
            let block = &body.blocks[bi];
            if j == TERM_ITEM {
                let write = block.terminator.local_write(local);
                debug_assert!(
                    write.agrees_with(block.terminator.write_effect()),
                    "terminator channel classification disagrees with WriteEffect: {:?}",
                    block.terminator
                );
                f(bi, None, write);
            } else {
                let stmt_idx = j as usize;
                let stmt = &block.stmts[stmt_idx];
                let write = stmt.local_write(local);
                debug_assert!(
                    write.agrees_with(stmt.write_effect()),
                    "statement channel classification disagrees with WriteEffect: {stmt:?}"
                );
                f(bi, Some(stmt_idx), write);
                if trust_types::local_defs::statement_escapes_local_slot(stmt, local) {
                    f(bi, Some(stmt_idx), LocalWrite::Escape);
                }
            }
        }
    }
}

/// Short-circuiting lookup over every statement (`Some(stmt)`) and terminator (`None`)
/// in `blocks` that [`LocalWriteIndex`] lists for `local` (or in `universal`) when an
/// index is bound for `func.body`, or every block in `blocks` when no index is bound.
pub(crate) fn find_local_write_candidate<'a, R>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut f: impl FnMut(&'a trust_types::BasicBlock, Option<&'a trust_types::Statement>) -> Option<R>,
) -> Option<R> {
    if std::ptr::eq(blocks, func.body.blocks.as_slice())
        && let Some(idx) = crate::generate::local_write_index_for(&func.body)
    {
        return idx.find_raw_item(local, |(b, j)| {
            let block = &blocks[b as usize];
            if j == TERM_ITEM {
                f(block, None)
            } else {
                f(block, Some(&block.stmts[j as usize]))
            }
        });
    }
    for block in blocks {
        for stmt in &block.stmts {
            if let Some(out) = f(block, Some(stmt)) {
                return Some(out);
            }
        }
        if let Some(out) = f(block, None) {
            return Some(out);
        }
    }
    None
}

/// Short-circuiting predicate over [`find_local_write_candidate`] items (`Some(stmt)` for
/// a statement, `None` for the block's terminator).
pub(crate) fn any_local_write_candidate<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut pred: impl FnMut(&'a trust_types::BasicBlock, Option<&'a trust_types::Statement>) -> bool,
) -> bool {
    find_local_write_candidate(func, blocks, local, |block, item| pred(block, item).then_some(()))
        .is_some()
}

/// Visits every statement (`Some(stmt)`) and terminator (`None`) in `blocks` that
/// [`LocalWriteIndex`] lists for `local` (or in `universal`) when an index is bound for
/// `func.body`, or every block in `blocks` when no index is bound.
pub(crate) fn visit_local_write_candidates<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut on_item: impl FnMut(&'a trust_types::BasicBlock, Option<&'a trust_types::Statement>),
) {
    let _ = find_local_write_candidate(func, blocks, local, |block, item| {
        on_item(block, item);
        None::<()>
    });
}

/// Statement-only variant of [`visit_local_write_candidates`] over a [`VerifiableBody`].
pub(crate) fn visit_body_local_write_stmts<'a>(
    body: &'a VerifiableBody,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut on_stmt: impl FnMut(&'a trust_types::BasicBlock, &'a trust_types::Statement),
) {
    if std::ptr::eq(blocks, body.blocks.as_slice())
        && let Some(idx) = crate::generate::local_write_index_for(body)
    {
        idx.visit_raw_items(local, |(b, j)| {
            if j != TERM_ITEM {
                let block = &blocks[b as usize];
                on_stmt(block, &block.stmts[j as usize]);
            }
        });
        return;
    }
    for block in blocks {
        for stmt in &block.stmts {
            on_stmt(block, stmt);
        }
    }
}

/// Statement-only variant of [`visit_local_write_candidates`].
pub(crate) fn visit_local_write_stmts<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    on_stmt: impl FnMut(&'a trust_types::BasicBlock, &'a trust_types::Statement),
) {
    visit_body_local_write_stmts(&func.body, blocks, local, on_stmt);
}

/// Statement-only variant of [`visit_local_write_candidates`] that also passes the
/// statement's index within `block.stmts`.
pub(crate) fn visit_local_write_indexed_stmts<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut on_stmt: impl FnMut(&'a trust_types::BasicBlock, usize, &'a trust_types::Statement),
) {
    if std::ptr::eq(blocks, func.body.blocks.as_slice())
        && let Some(idx) = crate::generate::local_write_index_for(&func.body)
    {
        idx.visit_raw_items(local, |(b, j)| {
            if j != TERM_ITEM {
                let block = &blocks[b as usize];
                let s = j as usize;
                on_stmt(block, s, &block.stmts[s]);
            }
        });
        return;
    }
    for block in blocks {
        for (s, stmt) in block.stmts.iter().enumerate() {
            on_stmt(block, s, stmt);
        }
    }
}

/// Short-circuiting statement lookup over [`LocalWriteIndex`] items for `local` when
/// bound, or all statements in `blocks` when unbound.
pub(crate) fn find_local_write_stmt<'a, R>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut f: impl FnMut(&'a trust_types::BasicBlock, &'a trust_types::Statement) -> Option<R>,
) -> Option<R> {
    if std::ptr::eq(blocks, func.body.blocks.as_slice())
        && let Some(idx) = crate::generate::local_write_index_for(&func.body)
    {
        return idx.find_raw_item(local, |(b, j)| {
            if j == TERM_ITEM {
                return None;
            }
            let block = &blocks[b as usize];
            f(block, &block.stmts[j as usize])
        });
    }
    blocks.iter().find_map(|block| block.stmts.iter().find_map(|stmt| f(block, stmt)))
}

/// Short-circuiting statement predicate over [`LocalWriteIndex`] items for `local` when
/// bound, or all statements in `blocks` when unbound.
pub(crate) fn any_local_write_stmt<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut pred: impl FnMut(&'a trust_types::BasicBlock, &'a trust_types::Statement) -> bool,
) -> bool {
    find_local_write_stmt(func, blocks, local, |block, stmt| pred(block, stmt).then_some(()))
        .is_some()
}

/// Short-circuiting terminator lookup over [`LocalWriteIndex`] items for `local` when
/// bound, or all terminators in `blocks` when unbound.
pub(crate) fn find_local_write_term<'a, R>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut f: impl FnMut(&'a trust_types::BasicBlock, &'a Terminator) -> Option<R>,
) -> Option<R> {
    if std::ptr::eq(blocks, func.body.blocks.as_slice())
        && let Some(idx) = crate::generate::local_write_index_for(&func.body)
    {
        return idx.find_raw_item(local, |(b, j)| {
            if j != TERM_ITEM {
                return None;
            }
            let block = &blocks[b as usize];
            f(block, &block.terminator)
        });
    }
    blocks.iter().find_map(|block| f(block, &block.terminator))
}

/// Short-circuiting terminator predicate over [`LocalWriteIndex`] items for `local` when
/// bound, or all terminators in `blocks` when unbound.
pub(crate) fn any_local_write_term<'a>(
    func: &'a VerifiableFunction,
    blocks: &'a [trust_types::BasicBlock],
    local: usize,
    mut pred: impl FnMut(&'a trust_types::BasicBlock, &'a Terminator) -> bool,
) -> bool {
    find_local_write_term(func, blocks, local, |block, term| pred(block, term).then_some(()))
        .is_some()
}

/// How many VALUES `local` can hold across the whole body: one per LOCATED write on
/// any channel that replaces the whole value, PLUS the implicit ENTRY definition a
/// parameter carries — and [`ValueCount::AtLeast`] when a write could not be located
/// at all.
///
/// `Exactly(1)` is the single-valued case UNIFORMLY — a parameter with no write at
/// all, or any other local with exactly one. `Exactly(0)` is a non-parameter that is
/// never written.
///
/// THE ENTRY DEFINITION IS COUNTED UNCONDITIONALLY. A liveness relaxation — "nothing
/// can read the incoming argument before the store, so the bare name means one value"
/// — was tried and REMOVED; it is a `body.blocks` analysis and both of the channels
/// that broke it are outside `body.blocks`:
///
///  * the UNWIND edge out of a `Call` whose destination is the parameter. The call did
///    not write the destination on that edge, so the parameter still holds its entry
///    value in the cleanup region. Pinned by
///    `a_call_dest_written_parameter_is_two_valued_because_of_the_unwind_edge`.
///  * the function's PRECONDITIONS. `vc.formula` carries them, and
///    `#[core::contracts::requires(k >= 10)]` is stated about the parameter's ENTRY
///    value. A post-definition fact renamed onto that same symbol contradicts the
///    precondition, the path goes UNSAT, and every obligation on it is proved
///    VACUOUSLY and kernel-certified. Pinned by
///    `a_stored_parameter_is_two_valued_even_when_no_block_reads_it_first`.
///
/// Two independent unsoundness channels through one precision recovery; the price of
/// counting the entry definition unconditionally is measured in
/// `tests/entry_def_structural.rs` (§ THE PRICE) and is paid.
///
/// WHAT IT COUNTS IS THE LOCATED WHOLE-VALUE CHANNELS. `WholeNamed`/`WholeOpaque`
/// REPLACE the local's value, and they are the only two that add to the total.
///
///  * `Partial` (a field or index store, a discriminant write, a `Deinit`, a `Drop`)
///    changes what the local holds without replacing it. It is NOT counted, and every
///    question below that cannot tolerate it refuses it for itself:
///    [`body_is_single_static_assignment`] and [`body_unique_defining_block`] refuse
///    it, and so does [`body_unique_value_def`]. Callers that adjudicate the partial
///    channel themselves compose with this count rather than duplicating it:
///    `lib.rs::array_local_index_naming_stable` decides its own projected stores (a
///    constant `Index` store keeps the array-theory naming, anything else bails) and
///    then asks [`body_has_one_explicit_def`] for the whole value. Folding `Partial`
///    in here double-counts exactly that store.
///  * `Unlocatable` is a write with NO destination `Place`. It is not one value and it
///    is not none: it is the absence of the information this function reports, so it
///    makes the count [`ValueCount::AtLeast`] and every affirmative question below
///    answers `false`. Counting it as a value instead is FAIL-OPEN, not fail-closed:
///    for a local with no whole-local write at all it would take the total from 0 to
///    1, and `Exactly(1)` is exactly the reading that licenses a global fact keyed on
///    the bare name — a license granted precisely where the seam admits it cannot see
///    the writes. `unlocatable_writes_fail_closed_for_every_local` pins all three
///    questions, not just the count.
///  * `Escape` — a `&mut local` handed out here — can be written through later at a
///    place this scan never names, so an escaped local can hold values this function
///    does not count. It is an OPEN RESIDUAL of THIS question, declared in the arm
///    rather than omitted: [`body_is_single_static_assignment`],
///    [`body_unique_defining_block`] and — since 2026-09-15 — the resolver
///    [`body_unique_value_def`] all refuse it, but the count itself still admits it.
///    The resolver's admission WAS a live kernel-certified false proof and is now
///    closed; this residual is weaker in kind — a count-keyed fact is emitted against
///    the BARE NAME and stays subject to version renaming, where a resolver answer is
///    INLINED beyond its reach — but it is not argued sound, only not-yet-closed.
///    Folding it in here is not a free tightening: every `for` loop's iterator local is
///    `&mut`-borrowed by the `Iterator::next` desugar, so counting the alias makes
///    every iterator local multi-valued at once and the loop-bound producers keyed on
///    this count stop firing across the whole corpus — turning `proved/` programs whose
///    runtime oracle never panics into refutations with counterexamples. That is a
///    REAL and substantial precision loss, and it is why the residual is still open.
///    Closing it needs the iterator tracers moved off the value question and onto an
///    ORIGIN question; that is a separate change, and it must be MEASURED when it is
///    made rather than quoted from here.
pub(crate) fn body_value_count(body: &VerifiableBody, local: usize) -> ValueCount {
    let index = crate::generate::local_write_index_for(body);
    if let Some(hit) = index.as_ref().and_then(|i| i.value_counts.borrow().get(local)) {
        return hit;
    }
    let n = body_value_count_walk(body, local);
    if let Some(index) = index {
        index.value_counts.borrow_mut().insert(local, n);
    }
    n
}

fn body_value_count_walk(body: &VerifiableBody, local: usize) -> ValueCount {
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write(body, local, |_, write| summary.observe((), write));
    summary.value_count()
}

/// True iff `local` PROVABLY holds ONE value everywhere its bare name can be read —
/// the [`body_value_count`] [`ValueCount::Exactly`]`(1)` case. This is the license a
/// GLOBAL fact keyed on the bare name needs, so an inexact count cannot grant it.
pub(crate) fn body_holds_one_value(body: &VerifiableBody, local: usize) -> bool {
    body_value_count(body, local).is_exactly(1)
}

/// True iff NO whole-local definition of `local` exists anywhere in the body: for a
/// parameter, the entry definition is the only one; for any other local, the slot is
/// never whole-written (it is projection-written, aliased, or never written).
///
/// Strictly stronger than [`body_holds_one_value`] for a parameter and strictly weaker for
/// any other local, so the two are NOT interchangeable. This is the question asked by
/// a caller that needs a fixed STORAGE SLOT (a closure-env pointer whose pointee can
/// be named definitionally), not a fixed VALUE — which is why a `Partial` write (into
/// the slot) and an `Escape` (an alias of it) do not disqualify, and an `Unlocatable`
/// write, which may have reseated it, does.
pub(crate) fn body_never_explicitly_reseated(body: &VerifiableBody, local: usize) -> bool {
    let mut reseated = false;
    for_each_local_write(body, local, |_, write| {
        reseated |= match write {
            LocalWrite::Untouched => false,
            LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => true,
            // A store into the slot, or an alias of it, keeps the slot itself.
            LocalWrite::Partial | LocalWrite::Escape => false,
            // Could have reseated it; the seam cannot tell.
            LocalWrite::Unlocatable => true,
        };
    });
    !reseated
}

/// True iff EVERY write that reaches `local` in `body.blocks` is a whole-local
/// `Assign` — the one channel whose destination is a named `Place` and whose
/// statement the STATEMENT VERSION ORACLE therefore stamps
/// (`path_defs::stmt_writes_name` reads `Statement::Assign` and nothing else).
///
/// Trust: 2026-09-18 (the SIGNED g7 twin). This is NOT a value question and it is
/// not a stability question: it asks whether a DIFFERENT oracle — the version
/// tokens — can see every write, so that a caller which re-checks staleness with
/// that oracle may stop consulting `guards::value_local_is_unstable`'s blunt
/// "reassigned anywhere ⇒ no facts" gate. `overflow_vc`'s multiply-operand fact
/// miner is the caller and the only one: every fact it mines is kept only when
/// `version_token_at` reports the same token at the guard and at the multiply's
/// own use point, so a reassignment the oracle STAMPS is already handled exactly,
/// while a write the oracle CANNOT see would make that check vacuous.
///
/// So `true` is granted for exactly `WholeNamed` (and `Untouched`), and every
/// other channel answers `false`:
///
///  * `WholeOpaque` — a `Call` destination or a `TailCall` — is a TERMINATOR
///    write, and the version oracle mints tokens per STATEMENT; nothing stamps it.
///  * `Partial` — a field or index store, a discriminant write, a `Deinit`, a
///    `Drop`'s glue — changes what the local holds without a whole-local
///    destination, so no whole-local name moves for it.
///  * `Escape` — a `&mut local` / `&raw mut local` handed out here — is written
///    through later at a place named for the POINTER, which no scan keyed on this
///    local can see.
///  * `Unlocatable` — a pointer write, inline asm, or unmodelled MIR — has no
///    destination `Place` at all and FAILS CLOSED for every local.
///
/// The ENTRY definition of a parameter is deliberately irrelevant here: it is not a
/// write, and the caller's version check compares the multiply's token against the
/// guard's, both of which name the entry value when nothing has been stored yet.
/// That is precisely the case this question exists to admit —
/// `pub fn sgn_mut(a: i64, mut b: i64)`, whose `b` is `WholeNamed` once.
pub(crate) fn body_every_write_is_whole_named(body: &VerifiableBody, local: usize) -> bool {
    let mut only_named = true;
    for_each_local_write(body, local, |_, write| {
        only_named &= match write {
            LocalWrite::Untouched | LocalWrite::WholeNamed(_) => true,
            LocalWrite::WholeOpaque
            | LocalWrite::Partial
            | LocalWrite::Escape
            | LocalWrite::Unlocatable => false,
        };
    });
    only_named
}

/// True iff EVERY write that reaches `local` in `body.blocks` is a WHOLE-local write
/// with a located destination — a named `Assign` or a `Call`/`TailCall` destination —
/// i.e. a write the SSA value oracle (`generate::version_ssa`) records as a def site.
///
/// Trust: 2026-10-02 (class 10, `generate::range_bound_use`). The value-identity
/// question (`StmtVersionCtx::value_id_at`) is asked over def sites the per-block write
/// index records: statement destinations (`ValueId::Def { stmt }`) AND terminator
/// destinations (`ValueId::Def { stmt: u32::MAX }`, the `s{b}_t` token —
/// `block_writes::FnWrites::out_token` answers `None` exactly when the terminator writes
/// the name). So, for THAT question, a `Call` destination is as visible as an `Assign`,
/// and [`body_every_write_is_whole_named`]'s refusal of it (stated for the
/// statement-granular token comparison its one caller makes) is not needed. A
/// loop-carried `len` first written by `bands.len().min(16)` is exactly that shape.
///
/// Every other channel answers `false`, for the reasons
/// [`body_every_write_is_whole_named`] gives: `Partial` moves no whole-local name,
/// `Escape` is written through later under the POINTER's name, and `Unlocatable` has no
/// destination at all.
pub(crate) fn body_every_write_is_whole_located(body: &VerifiableBody, local: usize) -> bool {
    let mut located = true;
    for_each_local_write(body, local, |_, write| {
        located &= match write {
            LocalWrite::Untouched | LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => true,
            LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => false,
        };
    });
    located
}

/// True iff `local` holds ONE value AND that value is produced by an EXPLICIT
/// definition in `body.blocks`.
///
/// The question asked by a caller that goes on to INSPECT the defining statement —
/// "is this the `Vec::new()` that created the container", "is this the `len()` call
/// that produced the bound". A never-reassigned PARAMETER is single-valued but has no
/// such statement, so it answers `false` here and `true` to [`body_holds_one_value`].
pub(crate) fn body_has_one_explicit_def(body: &VerifiableBody, local: usize) -> bool {
    body_holds_one_value(body, local) && !body_never_explicitly_reseated(body, local)
}

/// The rvalue of `local`'s ONE value, when that value is produced by a whole-local
/// `Assign` and NOTHING ELSE touches the local.
///
/// `None` whenever the local can hold more than one value. That includes EVERY
/// PARAMETER with any write (whose `Assign` is its SECOND value — [`body_value_count`])
/// and every local reached by a channel this module cannot name, WITH NO EXCEPTION: a
/// `Call`/`TailCall` destination, a `SetDiscriminant`/`Deinit`/`Drop`, a projected
/// store, an unlocatable pointer write, and — since 2026-09-15 — a MUTABLE OR RAW ALIAS
/// all answer `None`.
/// This is the resolver channel, distinct from the counting channel: a caller that
/// INLINES the returned rvalue (a constant, a length, a referent place) bakes the value
/// into a formula, so version-renaming cannot rescue it afterwards.
///
/// A write THROUGH this local (`*local = v` — a `Deref`-first projection) changes the
/// POINTEE, not what `local` holds, so it does not count; see
/// `trust_types::LocalWrite::of_place`.
///
/// Live kernel-certified false proofs went through three of those channels, each
/// admitted here at some point and each closed by measuring the witness:
///
///  * the ENTRY definition. `stable_min_arg_formula` resolves a modulo divisor / a
///    `min` argument through here and INLINES the result as a constant into a global
///    fact keyed on the parameter's bare name. `param_mod_divisor_guarded` /
///    `param_min_arg` are the rows.
///  * the `Call` DESTINATION. `pmod` — `let mut m = 4; if s { m = pick(c); } b[n % m]`
///    with `#[inline(never)] pick` — lowers at `-O` to `m = const 4` in bb0 and a
///    `Call` whose dest IS `m` in bb1, ONE `Assign` and one `Call` dest. An
///    `Assign`-only scan resolved `m` to `4`, `build_modulo_bound_facts` emitted
///    `n % m < 4`, and the out-of-bounds `b[n % 9]` was proved and kernel-certified.
///    `call_dest_and_assign_is_not_a_unique_value` and the end-to-end
///    `call_dest_reassigned_modulo_divisor_still_refutes` are the rows.
///  * the MUTABLE ALIAS ([`LocalWrite::Escape`]) — CLOSED 2026-09-15. It was the last
///    channel this resolver admitted; `x3::pesc` below is the reproduced witness, and
///    the arm states what closing it cost and what a precision recovery would have to
///    supply.
pub(crate) fn body_unique_value_def(body: &VerifiableBody, local: usize) -> Option<&Rvalue> {
    if body_is_parameter(body, local) {
        return None;
    }
    if let Some(resolved) = unique_value_def_indexed(body, local, false) {
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            assert_eq!(
                resolved.map(std::ptr::from_ref),
                body_unique_value_def_walk(body, local).map(std::ptr::from_ref),
                "memoised unique value def disagrees with the walk for local {local}"
            );
        }
        return resolved;
    }
    body_unique_value_def_walk(body, local)
}

/// [`body_unique_value_def`] (`storage_only == false`) or
/// [`body_unique_value_def_modulo_pointee_borrows`] (`true`) through the per-body
/// index, memoised per local as the resolved statement's LOCATION — the extraction
/// resolves the same locals at statement after statement. The same state machine as
/// the two walks, over the same events (`None`: no index for this body).
fn unique_value_def_indexed(
    body: &VerifiableBody,
    local: usize,
    storage_only: bool,
) -> Option<Option<&Rvalue>> {
    let index = crate::generate::local_write_index_for(body)?;
    let cached = index.unique_value_defs.borrow().get(local, storage_only);
    let loc = cached.unwrap_or_else(|| {
        let escapes: EscapeClassifier = if storage_only { escapes_storage } else { escapes_wide };
        let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
        index.visit_located(body, local, escapes, |item, write| summary.observe(item, write));
        let loc = summary.unique_value_def().map(|(location, _)| location);
        index.unique_value_defs.borrow_mut().insert(local, storage_only, loc);
        loc
    });
    Some(loc.and_then(|(b, j)| match body.blocks[b as usize].stmts.get(j as usize) {
        Some(trust_types::Statement::Assign { rvalue, .. }) => Some(rvalue),
        _ => None,
    }))
}

fn body_unique_value_def_walk(body: &VerifiableBody, local: usize) -> Option<&Rvalue> {
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write(body, local, |_, write| summary.observe((), write));
    summary.unique_value_def().map(|(_, value)| value)
}

/// EVERY value of `local`, as the `(block index, rvalue)` of the write that produces
/// it — the N-DEFINITION generalization of [`body_unique_value_def`], for a caller
/// that recognizes a SHAPE spread over more than one definition.
///
/// [`body_unique_value_def`] answers only when the local holds ONE value, so a caller
/// asking about a two-definition idiom — a loop COUNTER (`i = 0` … `i = i + s`), an
/// ACCUMULATOR (`t = 0` … `t = t + x`) — had no seam question to ask and re-derived a
/// block scan for itself. `generate::loop_bounds::counter_init_stride_block` was
/// exactly that scan: it enumerated the `Assign` and `Call`-dest channels and the
/// mutable alias by hand, and was blind to `Partial` (a projected store,
/// `SetDiscriminant`, `Deinit`, `Drop` glue) and to `TailCall` — and the trip count it
/// derives from those two definitions UNDER-counts if anything else can advance or
/// RESET the counter, which is the false-bound direction.
///
/// The channel arms are [`body_unique_value_def`]'s, with `WholeNamed` accumulated
/// instead of refused on the second sighting, and for the same reasons — read that
/// function's arm for the three live kernel-certified false proofs behind them:
///
///  * a PARAMETER answers `None` outright. Its ENTRY definition is not in
///    `body.blocks`, so no list built here can contain it, and a caller that reads
///    `Some(defs)` as "these are all the values" would be reading a list with one
///    missing. (This is the same refusal [`body_unique_value_def`] makes, one
///    definition higher.)
///  * [`LocalWrite::WholeOpaque`] (a `Call` destination, a `TailCall`) is a value with
///    no `Rvalue` to return. [`body_unique_value_call`] is the question for that
///    channel; a caller that wants BOTH must ask both, and this one refuses rather
///    than silently omitting the call's value from the list.
///  * [`LocalWrite::Partial`], [`LocalWrite::Escape`] and [`LocalWrite::Unlocatable`]
///    leave the local holding a value no returned `Rvalue` names.
///
/// So `Some(defs)` means: `defs` is the COMPLETE set of values `local` can hold, each
/// named by its own rvalue, and `defs.len()` is exactly
/// [`body_value_count`]'s `Exactly(defs.len())`. `Some(vec![])` is a non-parameter that
/// is never written at all.
pub(crate) fn body_value_defs(
    body: &VerifiableBody,
    local: usize,
) -> Option<Vec<(usize, &Rvalue)>> {
    // The ENTRY definition is a value no element of this list can be.
    if body_is_parameter(body, local) {
        return None;
    }
    let mut disqualified = false;
    let mut defs: Vec<(usize, &Rvalue)> = Vec::new();
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(rvalue) => defs.push((index, rvalue)),
        LocalWrite::Escape
        | LocalWrite::WholeOpaque
        | LocalWrite::Partial
        | LocalWrite::Unlocatable => {
            disqualified = true;
        }
    });
    if disqualified { None } else { Some(defs) }
}

/// Trust: 2026-09-17 (round A12, pass 2) — [`body_unique_value_def`] with ONE
/// narrowing: a borrow reached THROUGH `local` (`&mut (*p)[i]`, `&mut (*p).f`,
/// `&raw mut (*p)` — a `Deref`-first projection) is not counted on the
/// [`LocalWrite::Escape`] channel. Everything else is byte-identical, the 2026-09-15
/// closure above included: a borrow of `local`'s OWN storage still disqualifies.
///
/// # Why that is not the closed channel reopening
///
/// The closure's obligation is stated on the arm above: "no write through the alias
/// can change the value this resolver hands back". A `Deref`-first borrow hands out a
/// pointer to `local`'s POINTEE. Writing through it changes what the pointee holds; it
/// cannot change what `local` holds, because `local`'s bytes are not in the borrowed
/// region. That is not a heuristic about how the alias is used — the three tries the
/// arm above rules out are all of that shape — it is the same structural fact
/// [`trust_types::LocalWrite::of_place`] already relies on when it classifies a write
/// to a `Deref`-first place as [`LocalWrite::Untouched`]. The two classifiers
/// disagreed, and `trust_types::Statement::escapes_local_storage` is where the line is
/// now drawn once.
///
/// # THE CALLER'S OBLIGATION, which is why this is not `body_unique_value_def`
///
/// The wider question ALSO happens to imply "nothing mutates `local`'s pointee behind
/// my back", and a caller that needs THAT must keep asking the wider one. The only
/// caller here is `crate::resolve_referent_guarded`, the referent fold, and it does
/// not need it: the fold spells `*local` by the referent's own name, so a write
/// through any alias of the pointee is a write to a place that name covers, versioned
/// at the use point by the ordinary fabric (an attributable store) or havocked (an
/// opaque one). What the fold needs is exactly this question — "does `local` hold ONE
/// pointer value" — plus `referent_fold::is_stable`, which carries the storage-identity
/// half (no local that roots or indexes the referent holds a value other than its
/// borrow-time one at any use; round A13 states it on the VALUE, where round A12
/// stated the strictly coarser "is not written"). Before round A12 nothing carried
/// that half and the Escape refusal was standing in for it; that is why this
/// narrowing is defensible now and was not then.
///
/// # WHAT IT RECOVERS, measured
///
/// `let mut arr = *src; let a = &mut arr; if j >= 4 { return 0; } let r = &mut a[j];
/// *r = 3; t[arr[j] as usize]` — plain safe Rust, runtime oracle never panics, the
/// pristine sealed driver PROVES the `t[..]` row at both `-O` levels. On the wider
/// question `&mut (*a)[j]` escaped `a`, `*a` stayed opaque, the store defined
/// `a*[_3]` while the read spelled `arr[_3]`, and the row was REFUTED with a
/// counterexample at `-O0`. `escaped_local_seam_realmir::a12_pointee_borrow_*` are
/// the rows, on real compiler MIR at both levels.
pub(crate) fn body_unique_value_def_modulo_pointee_borrows(
    body: &VerifiableBody,
    local: usize,
) -> Option<&Rvalue> {
    if body_is_parameter(body, local) {
        return None;
    }
    if let Some(resolved) = unique_value_def_indexed(body, local, true) {
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            assert_eq!(
                resolved.map(std::ptr::from_ref),
                body_unique_value_def_modulo_pointee_borrows_walk(body, local)
                    .map(std::ptr::from_ref),
                "memoised unique value def (storage) disagrees with the walk for local {local}"
            );
        }
        return resolved;
    }
    body_unique_value_def_modulo_pointee_borrows_walk(body, local)
}

fn body_unique_value_def_modulo_pointee_borrows_walk(
    body: &VerifiableBody,
    local: usize,
) -> Option<&Rvalue> {
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write_classified(body, local, escapes_storage, |_, write| {
        summary.observe((), write)
    });
    summary.unique_value_def().map(|(_, value)| value)
}

/// Trust: 2026-09-15 — THE ORIGIN QUESTION. **THIS IS NOT A VALUE. DO NOT USE IT AS
/// ONE.** It is [`body_unique_value_def`] with the alias channel readmitted, and it
/// exists so that the tracers which need "what was this local BUILT FROM" have a
/// question to ask that says what it means, instead of taking a value answer that the
/// body can contradict.
///
/// # What it claims, exactly
///
/// `local` has exactly one whole-local `Assign` in `body.blocks`, no entry definition,
/// no `Call`/`TailCall` destination, no projected/discriminant/`Deinit`/`Drop` write
/// and no unlocatable write — so the returned [`Rvalue`] is the value `local` holds
/// **at the point immediately after that one statement**, and nowhere else is it
/// established. A MUTABLE OR RAW ALIAS of `local` may exist, and a store through it
/// (`*p = v`, or an opaque callee handed `&mut local`) can make the returned rvalue
/// STALE at every later program point.
///
/// # What a caller must supply before using it
///
/// An argument, about ITS OWN shape, that the part of this rvalue it reads survives
/// every write that can arrive through the alias. That argument needs the CALLEE
/// MODEL, which lives at the caller and not here.
///
/// THE ONE CALLER, since 2026-09-16, is `generate::iterator_yield::iterator_origin_def`
/// — the sole entrance for the `for`-loop iterator tracers — and its argument is
/// written on it: `iter_mut_borrows_only_feed_next`, an affirmative allow-list that
/// every `&mut`/`&raw` conduit of the local is defined once, never read, never written
/// through, never dropped, and passed only as argument 0 of a std `Iterator::next`
/// call, paired with the tracers' own callee-identity gates. Under it the local's only
/// mutation is `next` on itself, which consumes and never reseats, so the yield set of
/// the initializer contains every later yield. What that does NOT license, and what
/// the tracers withhold across the hop: the iterator's POSITION (`Range::next`
/// advances `start`; the traced `start` is `None` there) and an EXACT trip count (a
/// stray `next` before the loop consumes one; only an upper bound is read).
///
/// A caller that cannot state such an argument must use [`body_unique_value_def`],
/// which refuses the channel. There is no default here and no silent middle: asking
/// this question is a claim that the caller has done that work — and a second caller
/// must write its own argument in the same form, not borrow this one.
///
/// # Why it is separate rather than a flag on the resolver
///
/// `x3::pesc` (see [`body_unique_value_def`]'s `Escape` arm) was a kernel-certified
/// false proof produced by exactly one question answering both. A parameter that
/// selects between "value" and "origin" puts the choice at the call site where it is
/// invisible in review; two named questions put it in the name.
pub(crate) fn body_unique_initializing_def(body: &VerifiableBody, local: usize) -> Option<&Rvalue> {
    // The ENTRY definition is not an in-block initializer and can never be returned.
    if body_is_parameter(body, local) {
        return None;
    }
    let mut found: Option<&Rvalue> = None;
    let mut ambiguous = false;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(rvalue) => {
            if found.is_some() {
                ambiguous = true;
            } else {
                found = Some(rvalue);
            }
        }
        // READMITTED, and it is the whole difference between this question and the
        // resolver. It is sound ONLY under the caller-side argument this function's
        // doc demands; nothing here checks that the caller made one.
        LocalWrite::Escape => {}
        // Every other channel is refused for the same reasons as in the resolver: a
        // second whole write is a second initializer, a partial write leaves a value
        // the rvalue does not name, and an unlocatable write is the absence of the
        // information rather than a value.
        LocalWrite::WholeOpaque | LocalWrite::Partial | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous { None } else { found }
}

/// The `Call` terminator that produces `local`'s ONE value, when that value comes from
/// a whole-local CALL DESTINATION and NOTHING ELSE touches the local.
///
/// The [`LocalWrite::WholeOpaque`] half of the resolver channel. [`body_unique_value_def`]
/// hands back an [`Rvalue`] and therefore refuses `WholeOpaque` — a call destination has
/// no `Rvalue` to name — so a caller that wants to INSPECT the producing call (which
/// callee, which arguments) had no seam question to ask and re-derived a block scan for
/// itself. `termination::resolve_saturating_add_increment` was exactly that scan, and it
/// was blind to the ENTRY definition: for a `mut` PARAMETER whose only body store is the
/// call, the entry value still reaches every use on a path that skips the call, and the
/// scan reported the call's value as the parameter's only one.
///
/// `None` whenever the local can hold more than one value, on ANY channel:
///
///  * a PARAMETER, always — its entry definition is not in `body.blocks` and this
///    resolver can never hand it back, so a parameter with a defining call holds TWO
///    values and a parameter without one has no call to return;
///  * a second `Call`/`TailCall` destination, or any [`LocalWrite::WholeNamed`] `Assign`
///    beside the call — two values, and the `Assign`'s is not the call's;
///  * [`LocalWrite::Partial`] (a projected store, `SetDiscriminant`, `Deinit`, `Drop`
///    glue) — the local's value after it is not the call's result;
///  * [`LocalWrite::Unlocatable`] — a write the seam cannot locate may have replaced it;
///  * [`LocalWrite::Escape`] — a `&mut local` handed out here can be stored through at a
///    place no scan keyed on `local` names. This question has refused the alias channel
///    since it was written (the scan it replaces already refused `&mut`/`&raw` borrows
///    of its temp by hand), and since 2026-09-15 [`body_unique_value_def`] refuses it
///    too, so the two resolver halves now agree on every channel.
///
/// A `TailCall` writes only the return place `_0` and has no destination of its own, so
/// it can never be the answer; it is counted as a value and declined like any other
/// second definition.
pub(crate) fn body_unique_value_call(body: &VerifiableBody, local: usize) -> Option<&Terminator> {
    // The ENTRY definition is a value no call can be, so a parameter has none; a named
    // `Assign` is a SECOND value beside the call, and its value is not the call's —
    // either way this question has no single answer. The walk is
    // `body_unique_value_call_index`'s; `WholeOpaque` is reachable only from
    // `Terminator::local_write`, and its `Call` filter is what rejects the `TailCall`
    // spelling.
    let index = body_unique_value_call_index(body, local)?;
    Some(&body.blocks.get(index)?.terminator)
}

/// Trust: 2026-09-16 (round A6) — THE CALL-THROUGH-TEMP SPELLING, for the join question
/// only. rustc does not always write a `let`-bound call result straight into its
/// binding: the loop-carried `let mut o = it.next(); while let Some(i) = o { ..; o =
/// it.next(); }` lowers at `-Copt-level=0` to `_4 = next(..)` (bb0) and then `_12 =
/// next(..)` (bb4), `_4 = move _12` (bb5) — the second call lands in a fresh temp and a
/// whole-local `Use` carries it into `o`. [`body_value_calls`] saw a `WholeNamed` write
/// beside the call and declined; the join was withheld, the havoc lane
/// (`havoc_decline::unmodelled_next_payload_fields`, which asks the same question) had
/// no candidate either, and the bounds row of that CORRECT program REFUTED with `i = 5`
/// on the real compiler (`-O0`, strict: build failed; oracle ok 15). At `-O1` the copy is
/// folded and the row proves.
///
/// This admits exactly that spelling. `rvalue` is the `WholeNamed` write of `local`
/// being classified; it is admitted iff it is `Use(Copy(_tmp) | Move(_tmp))` of a
/// whole, DIFFERENT local `_tmp` such that
///
///  * `_tmp`'s writes on every channel are exactly ONE `Call` destination
///    ([`body_unique_value_call`]: not a parameter, no second call, no `WholeNamed`
///    `Assign`, no `Partial`, no `Escape`, no `Unlocatable` write) — so the value `_tmp`
///    holds at every read IS that call's result; and
///  * every READ of `_tmp` anywhere in the body is a whole-local `Use` into an
///    unprojected destination ([`body_reads_are_whole_local_uses`]): no borrow, no
///    projected read, no call argument, no terminator operand, no unclassified
///    statement. The first bullet already makes the call's result the only value the
///    `Use` can carry into `local`; this keeps `_tmp` a pure carrier, so the call-result
///    temp rustc mints is the only shape admitted and a temp that is also handed to a
///    callee, aliased or read through a projection is refused rather than reasoned
///    about.
///
/// The answer is the index in `body.blocks` of `_tmp`'s producing call, which the join
/// records beside `local`'s direct call destinations: whichever branch ran, `local`
/// holds the result of one of the recorded calls and nothing else, so a consumer's
/// disjunction over them is true of `local` at every read — the same argument as for a
/// direct destination. A `Use` of anything else (a constant, a projected place, a local
/// with a second write, a parameter, an aliased temp) is a value no call produced, and
/// the caller marks the local ambiguous exactly as before.
///
/// Pinned on the compiler's own `-O0` MIR in `tests/escaped_local_seam_realmir.rs`
/// (`a7_ctl_two_next_loopcarried` proves through the join of two identical groups;
/// `a7_two_next_loopcarried_bug`, whose second call's receiver is `50..100`, stays
/// refuted on a witness the program realises; `a7_loopcarried_some_bug`, where the
/// carried value is `Some(i + 50)` — a `WholeNamed` write that is NOT a call-result
/// temp — is refused and never proved).
fn body_call_through_temp_index(
    body: &VerifiableBody,
    local: usize,
    rvalue: &Rvalue,
) -> Option<usize> {
    let Rvalue::Use(trust_types::Operand::Copy(p) | trust_types::Operand::Move(p)) = rvalue else {
        return None;
    };
    if !p.projections.is_empty() || p.local == local {
        return None;
    }
    let temp = p.local;
    let index = body_unique_value_call_index(body, temp)?;
    body_reads_are_whole_local_uses(body, temp).then_some(index)
}

/// The index in `body.blocks` of the ONE `Call` whose destination is `local`, under
/// exactly [`body_unique_value_call`]'s conditions (this is that question, answering
/// with the block index instead of the terminator; the two share one write walk).
fn body_unique_value_call_index(body: &VerifiableBody, local: usize) -> Option<usize> {
    if body_is_parameter(body, local)
        || crate::generate::cached_terminator_presence_for_body(body)
            .is_some_and(|tp| !tp.has_bare_dest_call)
    {
        return None;
    }
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write(body, local, |block, write| summary.observe(block, write));
    summary.unique_value_call_index(body)
}

/// True iff every READ of `local` in `body.blocks` is the source operand of a
/// whole-local `Use` assigned to an unprojected destination — `_x = copy local` /
/// `_x = move local` — and nothing else mentions `local` except as the whole
/// destination of a `Call` (its producing write, which is not a read).
///
/// FAIL-CLOSED BY CONSTRUCTION: `Statement`, `Terminator`, `Rvalue` and `Operand` are
/// `#[non_exhaustive]`, so this walk must carry wildcards, and every wildcard arm counts
/// as a READ. A statement, terminator or rvalue this function does not recognise
/// therefore REFUSES the local rather than admitting it — the opposite of the
/// proper-subset scan the module banner warns about, where an unrecognised channel
/// reads as absent.
fn body_reads_are_whole_local_uses(body: &VerifiableBody, local: usize) -> bool {
    use trust_types::{Operand, Place, Projection, Statement};
    fn place_mentions(place: &Place, local: usize) -> bool {
        place.local == local
            || place.projections.iter().any(|p| matches!(p, Projection::Index(i) if *i == local))
    }
    fn operand_mentions(op: &Operand, local: usize) -> bool {
        match op {
            Operand::Copy(p) | Operand::Move(p) => place_mentions(p, local),
            Operand::Constant(_) => false,
            // A symbolic or unsupported operand may name anything: a read.
            _ => true,
        }
    }
    fn rvalue_mentions(rv: &Rvalue, local: usize) -> bool {
        match rv {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast(op, _)
            | Rvalue::Repeat(op, _) => operand_mentions(op, local),
            Rvalue::BinaryOp(_, a, b)
            | Rvalue::CheckedBinaryOp(_, a, b)
            | Rvalue::UncheckedBinaryOp(_, a, b) => {
                operand_mentions(a, local) || operand_mentions(b, local)
            }
            Rvalue::Ref { place, .. }
            | Rvalue::AddressOf(_, place)
            | Rvalue::Discriminant(place)
            | Rvalue::Len(place)
            | Rvalue::CopyForDeref(place) => place_mentions(place, local),
            Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_mentions(op, local)),
            Rvalue::PtrOffset { ptr, count } => {
                operand_mentions(ptr, local) || operand_mentions(count, local)
            }
            Rvalue::Unsupported { operands, .. } => {
                operands.iter().any(|op| operand_mentions(op, local))
            }
            // An rvalue this walk does not know may read anything.
            _ => true,
        }
    }
    for block in &body.blocks {
        for stmt in &block.stmts {
            let ok = match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    // The admitted read: `_x = copy/move local`, `_x` a whole local.
                    let admitted_use = place.projections.is_empty()
                        && place.local != local
                        && matches!(
                            rvalue,
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.local == local && p.projections.is_empty()
                        );
                    admitted_use
                        || (!rvalue_mentions(rvalue, local)
                            && !place
                                .projections
                                .iter()
                                .any(|p| matches!(p, Projection::Index(i) if *i == local)))
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => true,
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                | Statement::PlaceMention(place) => !place_mentions(place, local),
                Statement::Intrinsic { args, .. } => {
                    !args.iter().any(|a| operand_mentions(a, local))
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    !(operand_mentions(src, local)
                        || operand_mentions(dst, local)
                        || operand_mentions(count, local))
                }
                Statement::Unsupported { operands, .. } => {
                    !operands.iter().any(|a| operand_mentions(a, local))
                }
                // A statement this walk does not know may read anything.
                _ => false,
            };
            if !ok {
                return false;
            }
        }
        let ok = match &block.terminator {
            // The producing write is the whole `dest`; an argument or a projected dest
            // rooted at the local is a read.
            Terminator::Call { args, dest, .. } => {
                !args.iter().any(|a| operand_mentions(a, local))
                    && !dest
                        .projections
                        .iter()
                        .any(|p| matches!(p, Projection::Index(i) if *i == local))
            }
            Terminator::TailCall { args, .. } => !args.iter().any(|a| operand_mentions(a, local)),
            Terminator::SwitchInt { discr, .. } => !operand_mentions(discr, local),
            Terminator::Assert { cond, .. } => !operand_mentions(cond, local),
            Terminator::Drop { place, .. } => !place_mentions(place, local),
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => true,
            // `Opaque` and anything this walk does not know may read anything.
            _ => false,
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Trust: 2026-09-24 (TRUST-10) — THE STORAGE QUESTION. True iff no code other than
/// `local`'s own whole named assignments can reach `local`'s STORAGE anywhere in
/// `body`, so a `Call`/`Drop`/`Opaque` elsewhere in the body cannot change what it
/// holds:
///
///  * every WRITE channel is [`LocalWrite::Untouched`] or [`LocalWrite::WholeNamed`] —
///    no `Call` destination, no `Partial` write (a field or index store, a discriminant
///    write, a `Deinit`, or a `Drop` whose glue takes `&mut local`), no `Escape`, and no
///    `Unlocatable` write anywhere in the body;
///  * no ALIAS of it is minted: no `Rvalue::Ref` — shared as well as mutable — and no
///    `Rvalue::AddressOf` rooted at `local`, whole or projected. A shared borrow is
///    refused because interior mutability reaches a field through it, which is why this
///    question cannot be answered from the write channels, where `&local` is not an
///    `Escape`;
///  * it is named by no `Rvalue::Unsupported` operand: the extractor lowers
///    `Rvalue::Reborrow` to `Unsupported { operands: [Copy(place)] }`, an alias not
///    spelled as a `Ref` (the module banner's shared blind spot, which this question
///    therefore does not share).
///
/// Every pointer to a local's storage is minted by one of those rvalues, so with none
/// of them a callee can reach `local` only through a by-value operand: a `Copy` hands
/// over a copy, and a `Move` leaves `local` moved-from, which MIR does not read again
/// before a re-initialisation — a second write this question already refuses.
///
/// It is NOT a value question: it says nothing about how many values `local` holds or
/// which. [`body_unique_value_def`] answers that, and a caller needs both.
/// `generate::value_facts::build_discriminant_cse_facts` is the caller: it ties two
/// `Discriminant` reads of one field of an owned aggregate across a `Call` only when
/// this holds.
///
/// FAIL-CLOSED BY CONSTRUCTION, like [`body_reads_are_whole_local_uses`]: the alias walk
/// carries wildcards over the `#[non_exhaustive]` MIR enums, and an rvalue or a
/// statement it does not recognise REFUSES.
pub(crate) fn body_storage_never_aliased(body: &VerifiableBody, local: usize) -> bool {
    let mut unreached = true;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched | LocalWrite::WholeNamed(_) => {}
        LocalWrite::WholeOpaque
        | LocalWrite::Partial
        | LocalWrite::Escape
        | LocalWrite::Unlocatable => unreached = false,
    });
    if !unreached {
        return false;
    }
    body_storage_has_no_aliases(body, local)
}

/// The alias half of `body_storage_never_aliased`, with its exact same
/// fail-closed all-CFG walk. This does NOT screen writes. A constructor result
/// combines it with `body_dest_fact_is_version_pinnable`: exactly one call
/// definition is allowed, while partial/escaped/unlocatable/other writes are
/// still refused. Existing storage consumers retain their original write gate.
pub(crate) fn body_storage_has_no_aliases(body: &VerifiableBody, local: usize) -> bool {
    use trust_types::{Operand, Statement};
    let names_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) => p.local == local,
        Operand::Constant(_) => false,
        // A symbolic or unsupported operand may name anything.
        _ => true,
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            let aliases = match stmt {
                Statement::Assign { rvalue, .. } => match rvalue {
                    Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => place.local == local,
                    Rvalue::Unsupported { operands, .. } => operands.iter().any(names_local),
                    // By-value reads and constructions: none mints a pointer.
                    Rvalue::Use(_)
                    | Rvalue::UnaryOp(..)
                    | Rvalue::Cast(..)
                    | Rvalue::Repeat(..)
                    | Rvalue::BinaryOp(..)
                    | Rvalue::CheckedBinaryOp(..)
                    | Rvalue::UncheckedBinaryOp(..)
                    | Rvalue::Discriminant(_)
                    | Rvalue::Len(_)
                    | Rvalue::CopyForDeref(_)
                    | Rvalue::Aggregate(..)
                    | Rvalue::PtrOffset { .. } => false,
                    // An rvalue this walk does not know may mint an alias.
                    _ => true,
                },
                // Pointer-destination and unmodelled writes are `Unlocatable` above and
                // have already refused; the rest mint nothing.
                Statement::Intrinsic { .. }
                | Statement::CopyNonOverlapping { .. }
                | Statement::Unsupported { .. }
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => false,
                // A statement this walk does not know may mint an alias.
                _ => true,
            };
            if aliases {
                return false;
            }
        }
    }
    true
}

/// Trust: 2026-09-24 (TRUST-10) — THE PINNED-POINTER QUESTION. True iff `local` holds
/// ONE value for the whole body — a parameter never written, or a non-parameter with
/// exactly one whole named `Assign` — and nothing but that definition can change what
/// `local` itself holds: no `Call` destination, no `Partial` write, no `Unlocatable`
/// write, and no alias of `local`'s OWN storage (`&mut local`, `&raw local`).
///
/// A `Deref`-first borrow THROUGH `local` (`&mut (*local).f`) does not count: it hands
/// out a pointer to the POINTEE, and writing through it cannot change the pointer
/// `local` holds — the argument [`body_unique_value_def_modulo_pointee_borrows`] states,
/// on the same narrow classifier. That is what makes this usable on a `&mut self`
/// method, which almost always borrows a field of `*self` mutably somewhere.
///
/// THE CALLER'S OBLIGATION. This says the POINTER is fixed; it says nothing about the
/// pointee, which any of those `Deref`-first borrows may write. Both callers need
/// exactly the pointer half: `generate::callee_write_set::refine_shared_reborrow_havoc`,
/// that `(*local).f` at a call names the same bytes the call's protected
/// shared-reference argument covers; and the post-barrier shared-parameter arm of
/// `generate::value_facts::build_discriminant_cse_facts` (2026-09-25, TRUST-09), that
/// `*local` names the bytes this body's own protected `&T` parameter covers at every
/// read. What anyone can do to those bytes is the protector's argument, not this
/// question's.
pub(crate) fn body_pointer_is_pinned(body: &VerifiableBody, local: usize) -> bool {
    let mut values = usize::from(body_is_parameter(body, local));
    let mut pinned = true;
    for_each_local_write_classified(body, local, escapes_storage, |_, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(_) => values += 1,
        LocalWrite::WholeOpaque
        | LocalWrite::Partial
        | LocalWrite::Escape
        | LocalWrite::Unlocatable => pinned = false,
    });
    pinned && values == 1
}

/// Trust: 2026-09-16 (round A5) — THE JOIN QUESTION. EVERY `Call` terminator that writes
/// `local`, when call destinations are the local's ONLY write channel: not a parameter,
/// no [`LocalWrite::WholeNamed`] `Assign`, no `Partial`, no `Escape`, no `Unlocatable`,
/// and no `TailCall` (which has no destination of its own). `None` otherwise, and `None`
/// for a local no call writes.
///
/// [`body_unique_value_call`] is this question with the answer required to be ONE call.
/// The two are kept separate because they license different facts: a single call's
/// result IS the local's value everywhere, while `k` calls license only the JOIN — a
/// fact that is a disjunction over the `k` results, true of the local at every read
/// because whichever branch ran, the local holds one of them and nothing else could
/// have written it. `generate::iterator_yield::next_call_receivers` is the caller: the
/// `Option` local of `let o = if c { small.next() } else { big.next() }` is written by two
/// `next` calls and nothing else, so its `Some` payload is a yield of `small` OR of
/// `big`, and the yield-set facts of the two receivers may be disjoined onto it. What
/// this question refuses is exactly what would break that argument: a named `Assign`
/// beside the calls (a value that is no call's result), a projected store or a
/// `SetDiscriminant` (`o.as_mut()`/`Some(x)` laundering a payload the calls never
/// yielded), an alias (the same through `*p = ..`), an unlocatable write, and a
/// parameter's entry value.
///
/// Trust: 2026-09-16 (round A6) — ONE `WholeNamed` spelling is admitted, and it is a
/// call destination one hop away: `_o = move _tmp` where `_tmp` is rustc's call-result
/// temp — its only write is one `Call` destination and its only reads are whole-local
/// `Use`s ([`body_call_through_temp_index`], which carries the witness: the loop-carried
/// `let mut o = it.next(); while let Some(i) = o { ..; o = it.next() }` at `-O0`, a
/// correct program the previous round's refusal turned into a refutation). The temp's
/// call is recorded as one of `local`'s producing calls; every other `WholeNamed` write
/// stays a refusal.
pub(crate) fn body_value_calls(body: &VerifiableBody, local: usize) -> Option<Vec<&Terminator>> {
    if body_is_parameter(body, local)
        || crate::generate::cached_terminator_presence_for_body(body)
            .is_some_and(|tp| !tp.has_bare_dest_call)
    {
        return None;
    }
    let mut ambiguous = false;
    let mut at: Vec<usize> = Vec::new();
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeOpaque => at.push(index),
        // The call-through-temp spelling: admitted only when `rvalue` carries the
        // result of exactly one `Call` and nothing else; any other named value refuses.
        LocalWrite::WholeNamed(rvalue) => match body_call_through_temp_index(body, local, rvalue) {
            Some(call_index) => at.push(call_index),
            None => ambiguous = true,
        },
        LocalWrite::Escape | LocalWrite::Partial | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous || at.is_empty() {
        return None;
    }
    at.iter()
        .map(|&index| {
            let terminator = &body.blocks.get(index)?.terminator;
            matches!(terminator, Terminator::Call { .. }).then_some(terminator)
        })
        .collect()
}

/// Trust: 2026-09-16 — THE ORIGIN QUESTION FOR A CALL DESTINATION. **THIS IS NOT A
/// VALUE. DO NOT USE IT AS ONE.** It is [`body_unique_value_call`] with the alias
/// channel readmitted — the `WholeOpaque` twin of [`body_unique_initializing_def`],
/// under the SAME caller-side contract, and it exists for the same reason: the `for`-
/// loop iterator tracers need "which CALL was this local BUILT BY", and the `&mut`
/// conduit the `Iterator::next` desugar hands out sits on the local whenever the
/// identity `into_iter` copy has been folded away (every `-Copt-level=1` body; the
/// bounded-reduction lane's synthetic fixtures spell that shape directly).
///
/// # What it claims, exactly
///
/// `local` is not a parameter and its writes in `body.blocks`, on every channel, are
/// exactly one `Call` destination: no `WholeNamed` `Assign` beside it (a `r = ..`
/// reseat), no second `Call`/`TailCall`, no `Partial` write (a projected store, a
/// `SetDiscriminant`/`Deinit`, a `Drop`), no `Unlocatable` write. A MUTABLE OR RAW ALIAS
/// of `local` MAY exist, and a store through it can make the returned call's result
/// STALE at every later program point — so the answer is "the call that initialised
/// the local", never "the local's value".
///
/// # What a caller must supply before using it
///
/// The argument [`body_unique_initializing_def`] demands, about ITS OWN shape: that the
/// part of the answer it reads survives every write that can arrive through the alias.
/// THE FIRST CALLER is `generate::iterator_yield::call_dest_hop`, whose argument is
/// `iter_mut_borrows_only_feed_next` — every conduit is defined once, never read,
/// never written through, never dropped, passed only as argument 0 of a std
/// `Iterator::next` — so the local's only mutation is `next` on itself, and the yield
/// set of the call's result contains every later yield.
///
/// THE SECOND CALLER is `generate::str_offset::bytes_position_root`, whose argument is
/// `iter_mut_borrows_only_feed` admitting ONE terminator: every conduit of `it` feeds
/// only argument 0 of the one authenticated `Iterator::position` call it vouches for.
/// `it`'s type is fixed to `core::str::Bytes` by the authenticated `str::bytes`
/// initialiser, `position` consumes and never reseats, and nothing else touches `it`
/// before it, so the items `position` scans are a suffix of `s.as_bytes()`. Its
/// STR_BYTE_POSITION use (`str_offset::bytes_position_origin`) adds
/// `iterator_yield::iter_consumed_once_by`: no other mention of the local, and one
/// dynamic execution of the call per initialisation, so the suffix is the whole
/// string. A third caller writes its own argument in the same form.
///
/// The measured witnesses this question must keep refusing, all kernel-certified
/// false bounds proofs on real MIR before 2026-09-16 (`tests/escaped_local_seam_realmir
/// .rs`): `r = (0..5).rev(); r = (0..100).rev()` (a `WholeNamed` beside the call —
/// refused HERE); `let p = &mut r; *p = (0..100).rev()` (an `Escape`, admitted HERE,
/// refused by the caller's conduit gate because `(*p) = ..` is a write rooted at the
/// conduit). The gate, not this question, is what makes the alias safe; this question
/// refuses everything else.
pub(crate) fn body_unique_initializing_call(
    body: &VerifiableBody,
    local: usize,
) -> Option<&Terminator> {
    if body_is_parameter(body, local)
        || crate::generate::cached_terminator_presence_for_body(body)
            .is_some_and(|tp| !tp.has_bare_dest_call)
    {
        return None;
    }
    let mut ambiguous = false;
    let mut at: Option<usize> = None;
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeOpaque => {
            if at.is_some() {
                ambiguous = true;
            } else {
                at = Some(index);
            }
        }
        // READMITTED — the whole difference from `body_unique_value_call`, sound ONLY
        // under the caller-side argument this function's doc demands.
        LocalWrite::Escape => {}
        LocalWrite::WholeNamed(_) | LocalWrite::Partial | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous {
        return None;
    }
    let terminator = &body.blocks.get(at?)?.terminator;
    matches!(terminator, Terminator::Call { .. }).then_some(terminator)
}

/// Trust: 2026-10-11 (CL-FOLD-LOCALDEF-1) — a local's ONE whole definition, on whichever
/// channel it is: the `Assign`'s [`Rvalue`] ([`body_unique_value_def`]'s answer) or the
/// `Call` [`Terminator`] whose destination it is ([`body_unique_value_call`]'s).
#[derive(Clone, Copy, Debug)]
pub(crate) enum WholeDefinition<'a> {
    Assign(&'a Rvalue),
    Call(&'a Terminator),
}

/// Trust: 2026-10-11 (CL-FOLD-LOCALDEF-1) — THE VALUE QUESTION for a caller that INLINES
/// a local's one definition and accepts either channel: [`body_unique_value_def`]'s
/// answer or [`body_unique_value_call`]'s, whichever holds, with ONE narrowing. A `Drop`
/// terminator of the WHOLE local is not a write here.
///
/// Every other channel is refused exactly as the two resolvers refuse it: a PARAMETER
/// (its entry definition), a second whole write (an `Assign`, a `Call` destination, a
/// `TailCall`), a projected store, a `SetDiscriminant`/`Deinit`, a `Drop` of a PROJECTION
/// (`drop(x.f)`, after which `x`'s other fields are still read), a `&mut`/`&raw` alias,
/// and an unlocatable write.
///
/// # Why a whole-local `Drop` is not a value at any read
///
/// `Drop(x)` runs `x`'s drop glue in place (a custom `Drop::drop` gets `&mut x` for the
/// duration of the terminator) and leaves `x` UNINITIALISED. MIR reads a dropped place
/// only after a re-initialisation, and a re-initialisation is a second whole write, which
/// this question refuses. So no read of the bare name observes anything the glue did:
/// the drop ENDS the value this question names, it does not replace it. `trust-types`
/// still classifies the drop `Partial`, and every other question here still counts it:
/// a fact keyed on the bare name under version renaming is a different question.
///
/// # Why it exists
///
/// `generate::alloc_vcs::local_def` asked `has_one_explicit_def`, the COUNTING question,
/// which admits a projected store and an alias. Every caller inlines the answer, so
/// `let mut r = 0u8..4; r.end = 200; r.sum::<u8>()` was kernel-certified (stage 1 of
/// `2bf0ad72e3`) while the program panics. The plain resolvers close that, but they also
/// refuse every local with drop glue that is live across a call, because the call's
/// unwind edge drops it: `first.to_uppercase()` in the `capitalize` idiom (`ToUppercase`
/// holds an `array::IntoIter`) is `Drop`ped on the `flat_map` call's cleanup edge, and its
/// bounded `collect` source was lost (`tests/ui/trust/iter_hof_collect_counts.rs
/// #capitalize_root`). `local_defs_tests::whole_drop_*` pin both halves.
pub(crate) fn body_unique_value_modulo_whole_drops(
    body: &VerifiableBody,
    local: usize,
) -> Option<WholeDefinition<'_>> {
    unique_whole_definition_modulo_whole_drops(body, local, false)
}

/// Trust: 2026-10-11 (CL-FOLD-LOCALDEF-1) — THE ORIGIN QUESTION twin of
/// [`body_unique_value_modulo_whole_drops`]. **THIS IS NOT A VALUE.** It readmits exactly
/// one channel, the `&mut`/`&raw` alias ([`LocalWrite::Escape`]), as
/// [`body_unique_initializing_def`] and [`body_unique_initializing_call`] do, under their
/// contract: the caller must argue that the part of the answer it reads survives every
/// write that can arrive through the alias.
///
/// THE ONE CALLER is `generate::alloc_vcs::origin_def_through_core_next` (and its key
/// twin), reached only from `fold_source_bound` (for a std `Range`/`RangeInclusive`
/// origin) and `collect_source_live_count`. Its argument is written there: every
/// conduit is argument 0 of core's `Iterator::next` by rendered path AND compiler-minted
/// key (`iter_mut_borrows_only_feed`), so the local's only mutation is `next` on itself,
/// and both consumers read the origin only as an UPPER bound on what is still to be
/// yielded, which a consumed iterator still satisfies. A second caller writes its own
/// argument in the same form.
pub(crate) fn body_unique_initializing_modulo_whole_drops(
    body: &VerifiableBody,
    local: usize,
) -> Option<WholeDefinition<'_>> {
    unique_whole_definition_modulo_whole_drops(body, local, true)
}

/// The one walk behind [`body_unique_value_modulo_whole_drops`] (`admit_alias == false`)
/// and [`body_unique_initializing_modulo_whole_drops`] (`true`). Private, so the choice
/// between a value and an origin stays in the name the caller asks.
fn unique_whole_definition_modulo_whole_drops(
    body: &VerifiableBody,
    local: usize,
    admit_alias: bool,
) -> Option<WholeDefinition<'_>> {
    // The ENTRY definition is a value no in-block definition can be.
    if body_is_parameter(body, local) {
        return None;
    }
    let blocks = body.blocks.as_slice();
    let index = crate::generate::local_write_index_for(body);
    if let Some(cached) = index
        .as_ref()
        .and_then(|idx| idx.unique_whole_defs_modulo_whole_drops.borrow().get(local, admit_alias))
    {
        return cached.and_then(|(b, j)| {
            let block = blocks.get(b as usize)?;
            if j == TERM_ITEM {
                matches!(block.terminator, Terminator::Call { .. })
                    .then_some(WholeDefinition::Call(&block.terminator))
            } else {
                match block.stmts.get(j as usize) {
                    Some(trust_types::Statement::Assign { rvalue, .. }) => {
                        Some(WholeDefinition::Assign(rvalue))
                    }
                    _ => None,
                }
            }
        });
    }
    let mut ambiguous = false;
    let mut found: Option<((u32, u32), WholeDefinition<'_>)> = None;
    for_each_local_write_located(body, local, |b, stmt, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(rvalue) => {
            if found.is_some() {
                ambiguous = true;
            } else if let Some(j) = stmt {
                found = Some(((b as u32, j as u32), WholeDefinition::Assign(rvalue)));
            } else {
                ambiguous = true;
            }
        }
        // A `Call` destination is the one opaque write that can be the answer; a second
        // definition, a `TailCall`, or anything a statement writes opaquely is refused.
        LocalWrite::WholeOpaque => match blocks.get(b).map(|blk| &blk.terminator) {
            Some(terminator)
                if stmt.is_none()
                    && found.is_none()
                    && matches!(terminator, Terminator::Call { .. }) =>
            {
                found = Some(((b as u32, TERM_ITEM), WholeDefinition::Call(terminator)));
            }
            _ => ambiguous = true,
        },
        // The ONE narrowing: the terminator `Drop` of the WHOLE local. A projected drop,
        // a projected store, a discriminant write and a `Deinit` are still refused.
        LocalWrite::Partial => {
            let whole_drop = stmt.is_none()
                && matches!(
                    blocks.get(b).map(|blk| &blk.terminator),
                    Some(Terminator::Drop { place, .. })
                        if place.local == local && place.projections.is_empty()
                );
            if !whole_drop {
                ambiguous = true;
            }
        }
        LocalWrite::Escape => {
            if !admit_alias {
                ambiguous = true;
            }
        }
        LocalWrite::Unlocatable => ambiguous = true,
    });
    let resolved = if ambiguous { None } else { found };
    if let Some(index) = index {
        index
            .unique_whole_defs_modulo_whole_drops
            .borrow_mut()
            .insert(local, admit_alias, resolved.map(|(loc, _)| loc));
    }
    resolved.map(|(_, def)| def)
}

/// Indexed [`trust_types::local_defs::source_slot_is_stable`] over `body`: when the
/// body is bound in `LocalWriteIndex`, visits only the indexed items of `local` +
/// `universal` and caches the `bool` per local; otherwise delegates to the shared walk.
pub(crate) fn body_slot_is_stable(body: &VerifiableBody, local: usize) -> bool {
    if let Some(index) = crate::generate::local_write_index_for(body) {
        if let Some(hit) = index.slot_source_stable.borrow().get(local) {
            return hit;
        }
        let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
        let mut projected_store = false;
        index.visit_located_slot_writes(body, local, |block, statement, write| {
            summary.observe((), write);
            projected_store |= match statement {
                Some(idx) => matches!(
                    &body.blocks[block].stmts[idx],
                    trust_types::Statement::Assign { place, .. }
                        if place.local == local && !place.projections.is_empty()
                ),
                None => matches!(
                    &body.blocks[block].terminator,
                    Terminator::Call { dest, .. }
                        if dest.local == local && !dest.projections.is_empty()
                ),
            };
        });
        let ans = !projected_store && summary.has_at_most_one_stable_value();
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            assert_eq!(
                ans,
                trust_types::local_defs::source_slot_is_stable(body, local),
                "LocalWriteIndex::slot_source_stable disagrees with source_slot_is_stable for local {local}"
            );
        }
        index.slot_source_stable.borrow_mut().insert(local, ans);
        return ans;
    }
    trust_types::local_defs::source_slot_is_stable(body, local)
}

/// Trust: 2026-11-06 (VCGEN-LIB-REDS-1) — the shared slot-stability question
/// (`trust_types::local_defs::source_slot_is_stable`, which
/// [`crate::slot_source_is_stable`] asks) with the ONE narrowing of
/// [`body_unique_value_modulo_whole_drops`]: a terminator `Drop` of the WHOLE local is
/// not a write. Every other channel is judged exactly as the shared reducer judges it,
/// over the same full walk and the same cell-blind escape classifier: a second whole
/// value (an `Assign`, a `Call` destination, a `TailCall`, or a parameter's entry value
/// plus a store), a projected store or call destination (a store through a pointer
/// rooted at the local included), a `Drop` of a PROJECTION, a
/// `SetDiscriminant`/`Deinit`, a `&mut`/`&raw` alias, and an unlocatable write.
///
/// Why the narrowing holds is [`body_unique_value_modulo_whole_drops`]'s argument:
/// `Drop(x)` ends `x`'s value and leaves `x` uninitialised; MIR reads a dropped place
/// only after a re-initialisation, which is a second whole write this question still
/// refuses. So every read the body can make of the local sees its one value. Since
/// 354c8202e1 the shared reducer also classifies the whole drop as a destabilising
/// partial write ("a consumed value cannot license a later fact"), which is the right
/// answer for a fact asked about the bare name at an arbitrary point. It is the wrong
/// answer for a caller that only matches PLACES that the body reads while the value is
/// live; such a caller must say so where it asks.
///
/// Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1) — the drop-narrowed SLOT question is
/// stated once, in `trust_types::local_defs::source_slot_is_stable_modulo_whole_drops`,
/// beside the rule it narrows. This is its indexed, per-local cached spelling
/// (PERF-COMPILER-VCGEN-77): with no `LocalWriteIndex` bound it IS that rule, and under
/// the differential harness the indexed answer is asserted equal to it. Until this
/// change the fallback restated the walk with a bare cell-blind `Statement::escapes_local`,
/// the one call `tests/write_channel_rule_is_not_restated.rs` refuses in this crate. Like
/// [`body_slot_is_stable`] it leaves a SHARED borrow of `UnsafeCell` bytes off, so each
/// caller states the cell argument where it asks:
///
///  * `crate::place_source_is_stable_modulo_whole_drops` (the witness candidate walk)
///    conjoins the cell clause, which makes it the cell-aware
///    `trust_types::local_defs::source_value_is_stable_modulo_whole_drops`;
///  * `generate::primitive_decimal_len::decimal_string_origin` holds the compiler's
///    `Freeze` license for the call's returned std `String`
///    (`trust_mir_extract::primitive_decimal_strings`, `output.is_freeze`), and every hop
///    of its origin chain is a whole `Use`/`&`/`CopyForDeref` of that value, so a `String`
///    or a shared reference to one: `Freeze` bytes a shared borrow cannot write. The
///    license bridges only the opaque/`Seq` lowering's conservative cell answer
///    (PRIMITIVE-DECIMAL-STRING-LENGTH in docs/DECISION_QUEUE.md).
pub(crate) fn body_slot_is_stable_modulo_whole_drops(body: &VerifiableBody, local: usize) -> bool {
    if let Some(index) = crate::generate::local_write_index_for(body) {
        if let Some(hit) = index.slot_source_stable_modulo_whole_drops.borrow().get(local) {
            return hit;
        }
        let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
        let mut projected_store = false;
        index.visit_located_slot_writes(body, local, |block, statement, write| {
            let Some(block) = body.blocks.get(block) else {
                summary.observe((), LocalWrite::Unlocatable);
                return;
            };
            match statement {
                None => {
                    if matches!(&block.terminator, Terminator::Drop { place, .. }
                        if place.local == local && place.projections.is_empty())
                    {
                        return;
                    }
                    projected_store |= matches!(&block.terminator, Terminator::Call { dest, .. }
                        if dest.local == local && !dest.projections.is_empty());
                }
                Some(idx) => {
                    projected_store |= matches!(block.stmts.get(idx),
                        Some(trust_types::Statement::Assign { place, .. })
                        if place.local == local && !place.projections.is_empty());
                }
            }
            summary.observe((), write);
        });
        let ans = !projected_store && summary.has_at_most_one_stable_value();
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            assert_eq!(
                ans,
                trust_types::local_defs::source_slot_is_stable_modulo_whole_drops(body, local),
                "LocalWriteIndex::slot_source_stable_modulo_whole_drops disagrees with \
                 source_slot_is_stable_modulo_whole_drops for local {local}"
            );
        }
        index.slot_source_stable_modulo_whole_drops.borrow_mut().insert(local, ans);
        return ans;
    }
    trust_types::local_defs::source_slot_is_stable_modulo_whole_drops(body, local)
}

/// True iff `local` holds ONE value for the whole body ([`body_holds_one_value`]) and
/// that value is produced by a WHOLE-local write — no field/index store, no
/// discriminant write, no mutable alias, no unlocatable pointer write. Licenses
/// treating `Var(local)` as a GLOBAL invariant: the symbol has one meaning at every
/// program point.
///
/// SOUNDNESS (P0 false proof): before the parameter arm existed,
/// `fn f(g:&[u8;6], mut i:usize, c:bool)` whose body does `i = y*3+x` inside a
/// guarded loop scored one explicit def, PASSED, and licensed the flattened-index
/// fact `i <= 5` on the BARE parameter name — which version-renaming then bound to
/// the *entry* version read on the other branch, killing `g[i]` for every entry
/// `i >= 6`. Pinned by `param_reassigned_once_flat_index_still_refutes`.
///
/// The alias channel that used to be checked here by hand is now
/// [`LocalWrite::Escape`] (`trust_types::Statement::escapes_local`). Its own false
/// proof: `let mut i = a.min(3); let p = &mut i; *p = b; arr[i]` PROVED in-bounds in
/// both the default and the kernel-certified `-full` lane, because the store's place is
/// `*p` — `place.local == p`, not `i` — so no scan keyed on `i` saw the reassignment
/// and a stale `i <= 3` vacuously discharged the violated bounds VC.
pub(crate) fn body_is_single_static_assignment(body: &VerifiableBody, local: usize) -> bool {
    let index = crate::generate::local_write_index_for(body);
    if let Some(hit) =
        index.as_ref().and_then(|i| i.single_static_assignment.borrow().get(local, false))
    {
        return hit;
    }
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write(body, local, |_, write| summary.observe((), write));
    let ans = summary.has_one_stable_value();
    if let Some(index) = index {
        index.single_static_assignment.borrow_mut().insert(local, false, ans);
    }
    ans
}

/// Trust: 2026-09-17 (round A12, pass 2) — [`body_is_single_static_assignment`] with
/// the narrow escape classifier of
/// [`body_unique_value_def_modulo_pointee_borrows`], and the argument is the same one:
/// a borrow reached THROUGH `local` addresses the pointee, so it cannot rebind
/// `local`.
///
/// It exists because the referent fold asks BOTH questions about the SAME local —
/// the resolver for "what does it hold", `referent_fold::def_position` for "where is
/// that one binding" — and two classifiers that disagree make the second discard the
/// first's answer. `crate::referent_fold::def_position` is the only caller, and
/// `crate::resolve_referent_guarded` has already asked the resolver by the time it
/// runs.
///
/// NOT for a caller that keys a GLOBAL fact on the bare name: that caller needs
/// "nothing mutates what this local reaches", which is the wider question, and
/// `body_is_single_static_assignment`'s own doc has the two false proofs that cost.
pub(crate) fn body_is_single_static_assignment_modulo_pointee_borrows(
    body: &VerifiableBody,
    local: usize,
) -> bool {
    let index = crate::generate::local_write_index_for(body);
    if let Some(hit) =
        index.as_ref().and_then(|i| i.single_static_assignment.borrow().get(local, true))
    {
        return hit;
    }
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    for_each_local_write_classified(body, local, escapes_storage, |_, write| {
        summary.observe((), write);
    });
    let ans = summary.has_one_stable_value();
    if let Some(index) = index {
        index.single_static_assignment.borrow_mut().insert(local, true, ans);
    }
    ans
}

/// How a written or borrowed place `p` relates to a PATH `q`, both rooted at the same
/// local, by projection prefix. The answer of [`body_path_is_single_static_assignment`]
/// is built from this relation and nothing else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathTouch {
    /// `p` is a prefix of `q` (`p == q` included): a write to `p` REBINDS the whole of
    /// `q`, and a mutable alias of `p` can.
    Prefix,
    /// `q` is a PROPER prefix of `p`: `p` lies strictly inside `q` — an element, a
    /// field, the pointee behind a `Deref` — and touches nothing `q` itself stores.
    Inside,
    /// `p` and `q` diverge before either ends — sibling fields, sibling variants, two
    /// `Index` projections by different locals. Whether their storage overlaps is a
    /// question about the ADT (a `union` field DOES overlap its siblings) that this
    /// module does not answer, so a caller must treat it as `Prefix`.
    Sibling,
}

impl PathTouch {
    /// Trust: 2026-09-16 (round A9) — `Index(l) == Index(l)` is the SAME SLOT only
    /// when `l` holds one value for the whole body. This relation is purely
    /// structural and cannot ask that question; [`body_path_is_single_static_assignment`]
    /// asks it FIRST (`body_place_index_locals_are_single_static_assignment`) and
    /// refuses any path carrying a multi-valued index local, so by the time two
    /// `Index(l)` segments are compared here `l` is single-valued and the equality
    /// is a slot equality.
    fn of(p: &[trust_types::Projection], q: &[trust_types::Projection]) -> Self {
        let common = p.iter().zip(q.iter()).take_while(|(a, b)| a == b).count();
        if common == p.len() {
            PathTouch::Prefix
        } else if common == q.len() {
            PathTouch::Inside
        } else {
            PathTouch::Sibling
        }
    }
}

/// Trust: 2026-09-17 (round A12) — a write of the place `written` (projections
/// only; the caller has matched the root local) REBINDS the storage AT `path`
/// unless it lies STRICTLY INSIDE it: a prefix write replaces the path, a sibling
/// write may overlap it (a `union`), and only an element / field / pointee write
/// below the path leaves what the path itself stores untouched. This is the
/// [`PathTouch`] relation read in the one direction the referent-fold stability
/// walk (`lib.rs::referent_fold`) needs; it inherits `PathTouch::of`'s `Index`
/// caveat, which that walk discharges by treating a differing-index sibling as a
/// rebinding (the conservative side).
pub(crate) fn written_projections_rebind_path(
    written: &[trust_types::Projection],
    path: &[trust_types::Projection],
) -> bool {
    PathTouch::of(written, path) != PathTouch::Inside
}

/// Trust: 2026-09-16 (round A8) — THE PATH QUESTION. True iff the storage AT `path` —
/// the bytes of the place itself, together with every enclosing prefix's — is bound
/// exactly once for the whole body and never mutably aliased. Concretely, over every
/// channel of every statement and terminator rooted at `path.local`, plus the ENTRY
/// definition when that local is a parameter:
///
///  * a DEFINITION (`Assign`, `Call` destination) of a place that is a PREFIX of `path`
///    (`path` itself included) is one binding of the path; exactly one is admitted;
///  * a DEFINITION, a DESTRUCTION (`SetDiscriminant`, `Deinit`, `Drop`) or a MUTABLE
///    ALIAS (`&mut p`, `&raw p`) of a place STRICTLY INSIDE `path` — any proper
///    extension of it, through a `Deref` or not — is IGNORED: it touches an element, a
///    field or a pointee that `path` reaches, never what `path` stores;
///  * a destruction or a mutable alias of a prefix of `path`, a SIBLING place
///    (`PathTouch::Sibling`), an [`LocalWrite::Unlocatable`] write, and any channel this
///    walk cannot attribute to a place (fail closed) DISQUALIFY.
///
/// # What it licenses, and what it must never be asked
///
/// It licenses a NAME whose value lives IN the path and not in its contents: a fat
/// pointer's length metadata is the case it was written for. `{s}__slice_len` for
/// `s: &mut [u8]` is a claim about `s`'s metadata; `(*s)[i] = v` and rustc's
/// `&raw const (*s)` / `&mut (*s)` reborrows (the `<[T]>::len` and bounds-check
/// spellings on a `&mut [T]`, at `-Copt-level=0`) write and alias the ELEMENTS, and no
/// write through a slice reference can change its length. `body_is_single_static_
/// assignment` refuses the reborrow as an `Escape` of `s` and the previous round's
/// caller refused the element store as a projected write, which turned the most
/// common mutable-slice idiom — `for i in 0..s.len() { s[i] = 0 }` — into a refuted
/// program on the real compiler at `-Copt-level=1` (fifteen correct functions,
/// nineteen `SliceBoundsCheck` rows; `tests/escaped_local_seam_realmir.rs`, the
/// `a8_ctl_mut_*` rows).
///
/// It is the WRONG question for the VALUE of `path`: a store into `(*s)[i]` does change
/// what the slice holds. A caller that reads the contents keeps asking
/// [`body_is_single_static_assignment`] / [`body_unique_value_def`]. And for a slice
/// length the caller must pass the place that OWNS the metadata — the fat pointer,
/// never the unsized `[T]` behind it (a borrow of `(*s)` is `Prefix` of the path
/// `(*s)` and would be refused for nothing) — which is
/// `generate::slice_len_licence::metadata_owner`'s job.
///
/// `Sibling` is disqualifying rather than ignored because storage overlap between
/// siblings is an ADT property (`union`) this module does not model; the precision
/// it costs is exactly what the previous caller already paid (any projected write of
/// the root refused), so nothing is lost against that baseline.
pub(crate) fn body_path_is_single_static_assignment(
    body: &VerifiableBody,
    path: &trust_types::Place,
) -> bool {
    use trust_types::{Place, Statement};
    /// The place a statement or terminator writes, with the KIND of write: a
    /// definition establishes a value, a destruction ends one.
    enum Written<'a> {
        Define(&'a Place),
        Destroy(&'a Place),
        None,
    }
    // Trust: 2026-09-16 (round A9) — THE INDEX LOCALS ARE PART OF THE PATH. The place
    // `(*s)[j]` is one slot only while `j` is one value: `PathTouch::of` reads
    // `Index(j) == Index(j)` as the same slot, and the walk below counts ONE binding of
    // `s` while `j` is rebound freely, so `let mut j = 0; .. s[j] ..; j = k; .. s[j] ..`
    // licensed `{s*[_j]}__slice_len` — the length of TWO different slices under one
    // name — for the copy tie and the range end (`index_local_min_bug`,
    // `index_elem_end_bug`, kernel-certified proofs of panicking programs; the
    // `r5b_*`/`r5c_*` rows of `tests/escaped_local_seam_realmir.rs`). A multi-valued
    // index local anywhere in the path refuses the path.
    if !body_place_index_locals_are_single_static_assignment(body, path) {
        return false;
    }
    let local = path.local;
    let q = path.projections.as_slice();
    let mut whole = usize::from(body_is_parameter(body, local));
    let mut disqualified = false;
    // One classification for a statement or a terminator: the CHANNEL (exhaustive over
    // `LocalWrite`, the compile-time anchor) decides what must fail closed, the written
    // PLACE decides how the path is touched.
    let mut classify = |channel: LocalWrite<'_>, written: Written<'_>| {
        match (channel, written) {
            (LocalWrite::Unlocatable, _) => disqualified = true,
            // The alias channel is not produced by `local_write`; it is walked below from
            // the rvalue. Fail closed should that ever change.
            (LocalWrite::Escape, _) => disqualified = true,
            (LocalWrite::Untouched, Written::None) => {}
            // A write to some OTHER local.
            (LocalWrite::Untouched, Written::Define(p) | Written::Destroy(p))
                if p.local != local => {}
            // A `Deref`-first write is `Untouched` for the LOCAL (`LocalWrite::of_place`);
            // for a path that runs through that deref it may be a binding of the path.
            (
                LocalWrite::Untouched
                | LocalWrite::WholeNamed(_)
                | LocalWrite::WholeOpaque
                | LocalWrite::Partial,
                Written::Define(p),
            ) => match PathTouch::of(&p.projections, q) {
                PathTouch::Prefix => whole += 1,
                PathTouch::Inside => {}
                PathTouch::Sibling => disqualified = true,
            },
            (
                LocalWrite::Untouched
                | LocalWrite::WholeNamed(_)
                | LocalWrite::WholeOpaque
                | LocalWrite::Partial,
                Written::Destroy(p),
            ) => {
                if PathTouch::of(&p.projections, q) != PathTouch::Inside {
                    disqualified = true;
                }
            }
            // A channel that writes the local through a construct this walk did not
            // attribute to a place (a `TailCall`'s implicit return place, a variant added
            // later): fail closed.
            (
                LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque | LocalWrite::Partial,
                Written::None,
            ) => {
                disqualified = true;
            }
        }
    };
    let visit_stmt = |stmt: &Statement, classify: &mut dyn FnMut(LocalWrite<'_>, Written<'_>)| {
        let written = match stmt {
            Statement::Assign { place, .. } => Written::Define(place),
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                Written::Destroy(place)
            }
            // Every other statement is classified `Untouched` or `Unlocatable` by
            // `Statement::local_write`, and the channel match above fails closed on
            // any that names a write.
            _ => Written::None,
        };
        classify(stmt.local_write(local), written);
        if crate::body_stmt_escapes_local(body, stmt, local) {
            // A mutable alias of a prefix of the path (the path included) can rebind
            // it through a store this walk never names; one strictly inside the path
            // aliases contents the path does not store. `escapes_local` is true of
            // exactly these two rvalues; fail closed should the classifier widen.
            let alias = match stmt {
                Statement::Assign {
                    rvalue: Rvalue::Ref { place: borrowed, .. } | Rvalue::AddressOf(_, borrowed),
                    ..
                } => Written::Destroy(borrowed),
                _ => Written::None,
            };
            match alias {
                Written::Destroy(p) if PathTouch::of(&p.projections, q) == PathTouch::Inside => {}
                _ => classify(LocalWrite::Escape, Written::None),
            }
        }
    };
    let visit_terminator =
        |terminator: &Terminator, classify: &mut dyn FnMut(LocalWrite<'_>, Written<'_>)| {
            let written = match terminator {
                Terminator::Call { dest, .. } => Written::Define(dest),
                Terminator::Drop { place, .. } => Written::Destroy(place),
                _ => Written::None,
            };
            classify(terminator.local_write(local), written);
        };
    if let Some(index) = crate::generate::local_write_index_for(body) {
        index.visit_raw_items(local, |(bi, j)| {
            let block = &body.blocks[bi as usize];
            if j == TERM_ITEM {
                visit_terminator(&block.terminator, &mut classify);
            } else {
                visit_stmt(&block.stmts[j as usize], &mut classify);
            }
        });
        return !disqualified && whole == 1;
    }
    for block in &body.blocks {
        for stmt in &block.stmts {
            visit_stmt(stmt, &mut classify);
        }
        visit_terminator(&block.terminator, &mut classify);
    }
    !disqualified && whole == 1
}

/// Trust: 2026-09-16 (round A9) — THE INDEX-LOCAL QUESTION. True iff every
/// `Projection::Index(l)` in `place`'s projections names a local that is
/// [`body_is_single_static_assignment`] — one value on every channel, no `&mut`
/// alias, a never-written parameter included. A `ConstantIndex` names no local and
/// always passes; a place with no `Index` projection passes vacuously.
///
/// # Why a separate question
///
/// The block encoder spells a projected read `(*s)[j]` as `s*[_<j>]`: the index local
/// is embedded BY NUMBER and the version rename (which rebinds `j` itself on every
/// write, `j#s0_0` / `j#s3_2`) used to leave the segment alone, so two reads of `s[j]`
/// across a write `j = k` were ONE name. Every producer that keys a GLOBAL fact, a
/// tie or a licence on such a name — the yield lane's projected range end
/// (`for i in 0..a[j]`), the length licence on `(*s)[j]` (`s*[_j]__slice_len`), the
/// copy/borrow/unsize length ties, the path question above — therefore states a
/// claim about EVERY slot `j` ever selects. That is true only when `j` selects one:
/// `let mut j = 0; if a[j] > 5 { return 0 } j = k; for i in 0..a[j] { b[i] }`
/// (`index_elem_end_bug`, `b: &[u8; 5]`) PROVED the `b[i]` row kernel-certified while
/// `f(&[3, 100], &b, 1)` panics; `let mut j = 0; let n = s[j].len().min(100); j = k;
/// s[j][..n]` (`index_local_min_bug`) proved its `RangeTo` row the same way. Both are
/// pinned on the compiler's own MIR at `-O0` and `-O1` in
/// `tests/escaped_local_seam_realmir.rs` (`r5b_*`, `r5c_*`).
///
/// The rename itself is fixed at the root in `generate::path_defs` (a write to `l`
/// now covers every name carrying the segment `[_l]`, so the two reads mint two
/// tokens), and this predicate is what every NAME-keyed producer asks in addition:
/// a global fact must never be keyed on a name the rename cannot reach.
pub(crate) fn body_place_index_locals_are_single_static_assignment(
    body: &VerifiableBody,
    place: &trust_types::Place,
) -> bool {
    place.projections.iter().all(|p| match p {
        trust_types::Projection::Index(l) => body_is_single_static_assignment(body, *l),
        _ => true,
    })
}

/// True iff a fact about the value a `Call` terminator writes into `local` may be
/// PINNED to that call's post-call version token `{name}#s{block}_t`.
///
/// # This is a DIFFERENT QUESTION from [`body_is_single_static_assignment`], and the
/// # difference is the whole point of this function
///
/// `body_is_single_static_assignment` answers "may this local's BARE NAME carry a
/// function-wide invariant?". For a PARAMETER the answer is always NO — the entry
/// definition is a second value the bare name also denotes, on every path that skips
/// the body write — and that is exactly the false proof its parameter arm closes.
///
/// This function answers "is the post-call TOKEN a name of one value?", which is a
/// question about a SPELLING that does not exist at entry at all. The two answers
/// differ on precisely one shape, the `mut` parameter written by one call:
///
/// ```ignore (illustrative)
/// _3 = copy _1;                       // the argument temp rustc actually emits
/// _1 = step(move _3) -> bb1;          // dest IS the parameter
/// ```
///
/// The injected clause is threaded through `generate::block_defs`'
/// `version_terminator_dest_fact`, which rewrites EVERY occurrence of the dest's base
/// name to `{name}#s{block}_t`. Nothing reads the parameter's ENTRY value under that
/// spelling, so the fact cannot land on the path that skips the call — the skip path
/// reads the BARE name.
///
/// THE NAME-DISJOINTNESS IS STRUCTURAL, NOT MEASURED. Exactly two passes rewrite a
/// versioned token to the bare name — `discharge::normalize_ssa_version_tokens` and
/// `discharge::bare_ssa_guard_variant` — and both collapse `{name}#{tok}` to `{name}`
/// only when `discharge::local_versions_collapse_to_bare` licenses it. On its PARAMETER
/// arm that predicate requires `!local_has_call_dest_write(func, local)` — and a call whose dest
/// is this local IS a call-dest write. So for every shape admitted here through the
/// parameter arm the collapse is refused BY THIS PREDICATE'S OWN PRECONDITION, and the
/// post-call token stays a distinct SMT symbol from the bare entry read. Deleting the
/// parameter clause of `local_versions_collapse_to_bare` would make this unsound; that
/// pairing is ASSERTED, not left to a comment —
/// `param_entry_gate_tests::a_version_pinned_parameter_dest_can_never_collapse_to_the_bare_name`
/// fails there rather than as a false proof downstream.
///
/// # What it still refuses, and why each refusal is required
///
///  * MORE THAN ONE whole write. A second whole write means a second post-call (or
///    post-assign) version, and `version_terminator_dest_fact`'s rewrite is a BLANKET
///    base-name match: it would retime that other definition's reads onto THIS call's
///    token too. One whole write in `body.blocks` is what makes the blanket rewrite
///    equal to the targeted one.
///  * `Partial` — a field/index store, a discriminant write, a `Deinit`, a `Drop`.
///    The local changes at a point that mints no version token here, so the value the
///    token names is not the value at the use.
///  * `Escape` — a `&mut local` handed out anywhere. A store through the alias names a
///    different place, so it mints no token either and the pin is to a stale value.
///  * `Unlocatable` — a write the seam cannot locate at all. Absence of information is
///    not a value; it fails closed here as everywhere else in this module.
///
/// The one channel it ADMITS that `body_is_single_static_assignment` refuses is the
/// parameter's ENTRY definition, for the reason argued above. Every other channel is
/// refused identically, so this predicate is STRICTLY WEAKER than its sibling on
/// exactly one shape and identical on all the rest — which is the property that makes
/// splitting them a precision recovery rather than a hole.
///
/// The [`LocalWrite::WholeOpaque`] requirement is not redundant with the count: it is
/// what makes "the one whole write is a call destination" a fact rather than an
/// assumption about the caller. A caller asks this about the dest of a `Call` it is
/// looking at, so the one whole write it finds IS that call's — but stating it here
/// means a caller that asks about an `Assign`-written local gets `false`, instead of a
/// pin to a token that terminator never mints.
pub(crate) fn body_dest_fact_is_version_pinnable(body: &VerifiableBody, local: usize) -> bool {
    if crate::generate::cached_terminator_presence_for_body(body)
        .is_some_and(|tp| !tp.has_bare_dest_call && !tp.has_tail_call)
    {
        return false;
    }
    let mut opaque = 0usize;
    let mut named = 0usize;
    let mut disqualified = false;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched => {}
        // The channel a `Call`/`TailCall` destination arrives on — the one that mints
        // the post-call token this pin names.
        LocalWrite::WholeOpaque => opaque += 1,
        // A named `Assign` is a second version of the local under a token this pin
        // does not name.
        LocalWrite::WholeNamed(_) => named += 1,
        LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => disqualified = true,
    });
    // The ENTRY definition is deliberately NOT charged here — see this function's doc.
    !disqualified && opaque == 1 && named == 0
}

/// The index in `body.blocks` of the ONE block that writes `local`, when the body
/// holds exactly one value of it and that value is not the parameter's entry value.
///
/// The question asked by a caller that resolves a definition ACROSS blocks on the
/// dominance argument "a local with a single static definition dominates all its uses,
/// because MIR never reads an uninitialized local". That argument needs the definition
/// to be unique on EVERY channel, and it is false of a parameter (initialized at ENTRY,
/// so a body definition of it need not run first) — both of which this answers.
///
/// `guards::latest_same_block_bool_definition` is the caller, and both halves are live
/// kernel-certified false proofs it carried:
///  * `p7` — `fn p7(a:&[u8;4], mut c: bool, i: usize, q: bool) { if q { c = i < 4; }
///    if c { a[i] } else { 0 } }` resolved the PARAMETER `c` to `i < 4` and proved
///    `a[i]` while `q=false, c=true, i>=4` indexes out of bounds.
///  * `p8` — `let c; if q { c = g(q); } else { c = i < 4; }` with `#[inline(never)] g`
///    lowers at `-O` to ONE `Assign` (`c = i < 4`) and one `Call` whose dest IS `c`.
///    An `Assign`-only uniqueness scan called `c` uniquely defined, inlined `i < 4` as
///    the SwitchInt edge fact, and proved `a[i]` while `q=true, i>=4` indexes out of
///    bounds.
///
/// THE PARTIAL AND ALIAS CHANNELS DISQUALIFY, they do not merely fail to count.
/// [`body_value_count`] scores neither, so `is_exactly(1)` above lets a body through
/// that has one whole write AND a field store, a `Drop`, or a `&mut` alias elsewhere —
/// and then there is no single block whose index answers "where the reaching
/// definition is", because the local changes at a point no index here names. Answering
/// with the whole write's block would assert a dominance that does not hold; answering
/// with the partial write's block is not a definition at all. Declining is the only
/// sound reading, and it is monotone (the caller loses a hypothesis).
/// `a_partially_written_local_has_no_unique_defining_block` is the row.
pub(crate) fn body_unique_defining_block(body: &VerifiableBody, local: usize) -> Option<usize> {
    if body_is_parameter(body, local) {
        return None;
    }
    if let Some(index) = crate::generate::local_write_index_for(body) {
        if let Some(hit) = index.unique_defining_block.borrow().get(local) {
            return hit;
        }
        if index.value_counts.borrow().get(local).is_some_and(|vc| !vc.is_exactly(1)) {
            index.unique_defining_block.borrow_mut().insert(local, None);
            return None;
        }
        let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
        let mut at: Option<usize> = None;
        let mut disqualified = false;
        for_each_local_write(body, local, |block, write| {
            summary.observe((), write);
            match write {
                LocalWrite::Untouched => {}
                LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => at = Some(block),
                LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => {
                    disqualified = true;
                }
            }
        });
        let vc = summary.value_count();
        index.value_counts.borrow_mut().get_or_insert(local, vc);
        let ans = if !vc.is_exactly(1) || disqualified { None } else { at };
        index.unique_defining_block.borrow_mut().insert(local, ans);
        return ans;
    }
    if !body_value_count(body, local).is_exactly(1) {
        return None;
    }
    let mut at: Option<usize> = None;
    let mut disqualified = false;
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => at = Some(index),
        LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => disqualified = true,
    });
    if disqualified { None } else { at }
}

/// True iff a fact about the value statement `stmt_index` of `body.blocks[block_index]`
/// WROTE into the whole of `local` may be pinned to that statement's own
/// statement-version token (`{local}#s{b}_{k}`), even though `local` is not
/// single-assignment.
///
/// The pin rests on the statement-version oracle: every read it stamps with
/// `s{b}_{k}` reads the value statement `k` wrote. That holds only for writes the
/// oracle VERSIONS. A whole `Assign` and a call destination mint their own token. The
/// other channels do not, so a read after one of them can still carry `s{b}_{k}` while
/// it reads a different value:
///
///  * `Partial` and `Escape` — refused anywhere in the body, exactly as
///    [`body_dest_fact_is_version_pinnable`] refuses them (a field store, a `Drop`, a
///    store through a `&mut` alias change the local at a point that may mint no token).
///  * `Unlocatable` — inline asm (`Opaque{InlineAsm}` with `out(reg)` operands),
///    `Unsupported`/intrinsic statements, an unmodelled terminator. The oracle mints no
///    token for these (`block_writes` versions `Assign`/`SetDiscriminant`/`Deinit`/
///    `CopyNonOverlapping` only; an `Opaque` terminator's havoc covered mutably borrowed
///    and mutable-pointer locals only until 2026-10-08, when it began versioning every
///    local — H3 OPAQUE-ASM-OUTPUT, `path_defs::terminator_def_names_structured` — so
///    the terminator half of this refusal is now belt-and-braces; an `Unsupported` or
///    intrinsic statement still mints no token). Measured 2026-10-01 on the
///    `discr_domain_opaque_loop` fixture: an `Opaque{InlineAsm}` or an `Unsupported`
///    statement between `_5 = Discriminant(_3)` and `switchInt(_5)` left the switch
///    reading `_5#s2_0`, and a pin with no position check PROVED the reachable
///    `otherwise` arm.
///
/// `Unlocatable` is refused BY POSITION, not body-wide, because a body-wide refusal is
/// the defect this question exists to repair (one diverging `Opaque` anywhere made
/// every local non-single-assignment). It refuses when an `Unlocatable` item can run
/// AFTER the write and its effect can be observed by code in this body:
///
///  * a STATEMENT is observed by whatever follows it — refused when it is reachable
///    from the point just after the write;
///  * a TERMINATOR is observed only in its successors — refused when it is reachable
///    and has any successor, the unwind cleanup block included. One with NO successor
///    (a diverging indirect call, `Opaque{targets: []}`) ends the body's execution, so
///    nothing in this body reads a value it wrote;
///  * a terminator this crate cannot classify (`Terminator` is `#[non_exhaustive]`)
///    answers "has successors and unknown edges" and refuses.
///
/// Reachability is the plain CFG over every successor, cleanup edges included, with
/// the writing block revisited in full when a loop leads back to it. It is a
/// conservative over-approximation (it ignores whether `local` is ever read after the
/// unlocatable write), so it can only decline more often, never pin more.
pub(crate) fn body_stmt_dest_fact_is_version_pinnable_at(
    body: &VerifiableBody,
    local: usize,
    block_index: usize,
    stmt_index: usize,
) -> bool {
    // `(block index, Some(stmt) | None for the terminator)` of every unlocatable item.
    let mut unlocatable: Vec<(usize, Option<usize>)> = Vec::new();
    let mut disqualified = false;
    for_each_local_write_located(body, local, |b, item, write| match write {
        LocalWrite::Untouched | LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => {}
        LocalWrite::Partial | LocalWrite::Escape => disqualified = true,
        LocalWrite::Unlocatable => unlocatable.push((b, item)),
    });
    if disqualified {
        return false;
    }
    if unlocatable.is_empty() {
        return true;
    }
    let Some(write_block) = body.blocks.get(block_index) else {
        return false;
    };
    if unlocatable.iter().any(|&(b, item)| b == block_index && item.is_some_and(|j| j > stmt_index))
    {
        return false;
    }
    // Every in-CFG successor, cleanup included; returns `false` for a terminator whose
    // edges this crate cannot enumerate.
    let visit_in_cfg_successors =
        |term: &Terminator, f: &mut dyn FnMut(trust_types::BlockId)| -> bool {
            match term {
                Terminator::Goto(target)
                | Terminator::Assert { target, .. }
                | Terminator::Drop { target, .. } => f(*target),
                Terminator::SwitchInt { targets, otherwise, .. } => {
                    for &(_, t) in targets {
                        f(t);
                    }
                    f(*otherwise);
                }
                Terminator::Call { target, .. } => {
                    if let Some(t) = *target {
                        f(t);
                    }
                }
                Terminator::Opaque { targets, .. } => {
                    for &t in targets {
                        f(t);
                    }
                }
                Terminator::Return
                | Terminator::TailCall { .. }
                | Terminator::Unreachable
                | Terminator::Resume => {}
                _ => return false,
            }
            if let Some(cleanup) = term.unwind_cleanup_target() {
                f(cleanup);
            }
            true
        };
    let position: Option<trust_types::fx::FxHashMap<trust_types::BlockId, usize>> = body
        .blocks
        .iter()
        .enumerate()
        .any(|(i, b)| b.id.0 != i)
        .then(|| body.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect());
    let resolve_block = |id: trust_types::BlockId| -> Option<usize> {
        match &position {
            Some(map) => map.get(&id).copied(),
            None => (id.0 < body.blocks.len()).then_some(id.0),
        }
    };
    let mut stack: Vec<usize> = Vec::new();
    let mut bad_target = false;
    if !visit_in_cfg_successors(&write_block.terminator, &mut |s| match resolve_block(s) {
        Some(i) => stack.push(i),
        None => bad_target = true,
    }) || bad_target
    {
        return false;
    }
    if stack.is_empty() {
        return true;
    }
    // Blocks reachable from the writing block's terminator (the writing block itself
    // only if a cycle leads back to it).
    let mut reached = vec![false; body.blocks.len()];
    while let Some(i) = stack.pop() {
        if std::mem::replace(&mut reached[i], true) {
            continue;
        }
        if !visit_in_cfg_successors(&body.blocks[i].terminator, &mut |s| match resolve_block(s) {
            Some(n) => stack.push(n),
            None => bad_target = true,
        }) || bad_target
        {
            return false;
        }
    }
    unlocatable.into_iter().all(|(b, item)| {
        let runs_after_write =
            reached[b] || (b == block_index && item.is_none_or(|j| j > stmt_index));
        if !runs_after_write {
            return true;
        }
        match item {
            Some(_) => false,
            None => {
                let mut any_succ = false;
                visit_in_cfg_successors(&body.blocks[b].terminator, &mut |_| any_succ = true)
                    && !any_succ
            }
        }
    })
}

// ── the `VerifiableFunction` face ──────────────────────────────────────────
//
// Every question above is answered from `func.body` alone. These wrappers exist so
// the crate's call sites — which hold a `VerifiableFunction` — read naturally; the
// `body_*` forms are for the few callers (`typestate`) that hold only a body. There
// is ONE implementation of each question.

/// True when nothing in `func` can change the value `read` names: a place read through
/// a chain of REFERENCES (`(*s).n`, `(*self.inner).n`, `(**s).n`) whose every pointer is
/// accounted for.
///
/// The bare name of such a place is a claim about every value it holds, so a fact
/// stated on it (a range bound `i < s.n`) needs the place never to change. That is a
/// question about MEMORY, not about the local the read happens to name: rustc reloads
/// a pointer from memory at each use (`_17 = copy (*_1); _5 = copy (*_17).0`, then
/// `_18 = copy (*_1); shrink(copy _18)`), and a shared reborrow `r = &*s` is read
/// while `s` is written. A check keyed on the one local of the read missed every one
/// of those, and `for i in 0..s.n { shrink(*s); t ^= s.n - i - 1 }` and three siblings
/// were proved, kernel-certified, and panic (the trip-count lane review's escape audit,
/// 2026-09-29).
///
/// So the check is on the pointer FAMILY. Walk the read back to its ROOT: through
/// single-value copies and reborrows of a pointer (`copy (*q).f`, `&(*q)`, `&mut (*q)`,
/// `copy q`) to a parameter or a single-value local of reference type, every link a
/// reference (a raw pointer may alias anything a callee can reach, so it refuses).
/// Then collect every local derived from the root the same ways, and refuse when any
/// of them could change the place:
///  * a store whose name overlaps the read's (`path_defs::write_rebinds`), or a store
///    through a family pointer whose name does not share the read's root, where the
///    names cannot tell whether they overlap;
///  * a family pointer handed out, to a call, a closure or struct literal, or stored in
///    memory, unless it can reach only a place disjoint from the read (`&mut s.buf`
///    beside `s.n`: a reference reaches only what it borrows), or it is a SHARED
///    reference and nothing on the read's path is an `UnsafeCell` (through `&T` nothing
///    else can be written);
///  * any statement or terminator not audited here that mentions a family local.
/// A store to a SIBLING field (`s.items[i] = x` beside `s.n`) keeps the fact.
///
/// It relies on what Rust guarantees a reference: a callee handed no pointer derived
/// from the root cannot reach the place. The whole-function reading is conservative
/// in time: a hand-out after the last use (`shrink(s)` after the loop) still refuses.
pub fn deref_read_is_never_written(func: &VerifiableFunction, read: &trust_types::Place) -> bool {
    deref_read_unwritten_at(func, read, None)
}

/// [`deref_read_is_never_written`], counting only the writes at the program points
/// `within` names (a statement index, or `None` for the block's terminator).
///
/// The caller names the points that lie on some path from where the read's VALUE was
/// taken to where a fact about that value is used, and a STORE anywhere else cannot
/// make the fact false: `s.n = 5; for i in 0..s.n { t ^= s.n - i - 1 } s.n = 0;`.
/// A HAND-OUT is still counted wherever it is. A reference handed out cannot itself
/// write after its borrow ends, but the callee it was handed to can turn it into a raw
/// pointer and return or stash it, and a raw pointer outlives the borrow the checker
/// tracks; a later call handed nothing can then write through it. So a hand-out before
/// the loop (`shrink(s); for i in 0..s.n`) or after it still withholds the bound. A
/// family that holds a raw pointer itself (a cast or an offset of a family pointer) is
/// refused outright.
pub fn deref_read_is_unwritten_within(
    func: &VerifiableFunction,
    read: &trust_types::Place,
    within: &dyn Fn(trust_types::BlockId, Option<usize>) -> bool,
) -> bool {
    deref_read_unwritten_at(func, read, Some(within))
}

fn deref_read_unwritten_at(
    func: &VerifiableFunction,
    read: &trust_types::Place,
    within: Option<&dyn Fn(trust_types::BlockId, Option<usize>) -> bool>,
) -> bool {
    use trust_types::{Operand, Place, Projection, Statement, Ty};

    // `[Deref, Field..]`: one reference hop, then fields; a second deref would pass
    // through a pointer that is not a local (its type unchecked). The READ may also
    // select an element (`(*a)[j]`), by a constant or by an index local with one value.
    let one_hop = |place: &Place| {
        matches!(place.projections.first(), Some(Projection::Deref))
            && place.projections[1..].iter().all(|q| matches!(q, Projection::Field(..)))
    };
    let is_ref = |local: usize| matches!(crate::local_ty_ref(func, local), Some(Ty::Ref { .. }));
    if !matches!(read.projections.first(), Some(Projection::Deref))
        || !read.projections[1..].iter().all(|q| {
            matches!(
                q,
                Projection::Field(..) | Projection::Index(..) | Projection::ConstantIndex { .. }
            )
        })
        || !place_index_locals_are_single_static_assignment(func, read)
    {
        return false;
    }

    // 1. The root, through never-re-pointed pointer copies and reborrows. Every place
    // the walk reads a pointer out of is kept: a union on any of them refuses below.
    let mut root = read.local;
    let mut links: Vec<&Place> = vec![read];
    let mut root_settled = false;
    for _ in 0..32 {
        if !is_ref(root) {
            return false;
        }
        let Some(def) = pointer_local_definition(&func.body, root) else { return false };
        match def {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
            | Some(Rvalue::CopyForDeref(q))
            | Some(Rvalue::Ref { place: q, .. })
                if one_hop(q) || q.projections.is_empty() =>
            {
                links.push(q);
                root = q.local;
            }
            // A parameter, or any other definition of reference type (a call's `&mut`
            // result), is a root of its own.
            _ => {
                root_settled = true;
                break;
            }
        }
    }
    if !root_settled && (!is_ref(root) || pointer_local_definition(&func.body, root).is_none()) {
        return false;
    }
    // The family is about the memory the read's NAME denotes, so the walk must end at
    // the local that name is rooted at. The namer folds a copy out of a locally built
    // aggregate back to what was put in it (`let pair = (&*s, 0); let r = pair.0;`
    // reads `(*r).n` as `s*.n`), while this walk stops at `r`: the family was `{r}`,
    // `shrink(s)` was never looked at, and `for i in 0..r.n { shrink(s); s.n - i - 1 }`
    // was proved and panics (the pointer-family check's precondition audit,
    // 2026-09-29). Names rooted elsewhere cannot be compared, so they refuse.
    fn root_of(s: &str) -> &str {
        let end = s.bytes().position(crate::is_projection_segment_lead).unwrap_or(s.len());
        &s[..end]
    }
    let read_name = crate::place_to_var_name(func, read);
    let read_root = root_of(&read_name);
    if root_of(&crate::place_to_var_name(func, &Place::local(root))) != read_root {
        return false;
    }
    // A UNION on the read's path, or on the path of any pointer the walk loaded on the
    // way to it: its fields overlap, and the names spell them as disjoint siblings (`u.0`
    // beside `u.1`), so neither a store nor a hand-out could be told apart from the
    // read. `union U { a: &S, b: &S }` read as `u.a.n` while `u.b = other` was proved
    // and panics (the pointer-family audits, `p2a_union` and review8 `p2_union`).
    // "May be a union" is the walk of the union write cover
    // (`generate::union_write_cover_len`), as for the slot half's cover and
    // `place_is_body_stable`'s union step: a stamped union, reached directly or through a
    // by-name marker the body's table defines as one (the extractor spells a RECURSIVE
    // union so inside every type that holds it, and so every ADT inside a recursive type's
    // definition, a plain union field of a recursive struct included), a variant-less ADT
    // whose kind was not recorded, a by-name marker the table does not define, and a step
    // the walk cannot type. A read of a whole union value refuses too. A link that is a whole pointer to a
    // union (`_k: &U` in `_a = &_k`) is not refused: `*_a` is the pointer `_k`, not the
    // union's bytes. Until 2026-10-16 this walk asked `adt_kind == Some(Union)` of each
    // step and lost the type at a marker, so for a recursive `union RU` held in a struct a
    // store to `h.u.next` did not reach a read of `h.u.n`, and main PROVED that read's
    // panicking overflow on real MIR (UNION-MARKER-DEREF-READ-1,
    // `tests/union_marker_deref_read_realmir.rs`).
    let defs = &func.body.datatype_defs;
    let passes_a_union = |place: &Place| {
        crate::generate::union_write_cover_len(func, place).is_some()
            || crate::place_ty_cow(func, place).is_none_or(|ty| {
                matches!(ty.as_ref(), Ty::Adt { .. } | Ty::Datatype { .. })
                    && crate::generate::field_base_may_overlap_siblings(defs, ty.as_ref())
            })
    };
    if links.iter().any(|place| passes_a_union(place)) {
        return false;
    }

    // 2. The family: every local whose value is a pointer derived from the root, with
    // the REGION it can reach — the canonical name of the place it points into, `None`
    // when that is not known. A reborrow of a place reaches that place (`&mut (*s).buf`
    // reaches `s*.buf`, not its sibling `s*.n`: a reference's provenance is the place it
    // borrows); a copy reaches what its source reaches; a pointer LOADED from memory
    // reaches what that loaded value points to (`copy (*s).p` reaches `s*.p*`); and a
    // cast or an offset reaches something unknown. A local derived twice with different
    // regions reaches their union: unknown. A write of it that is not a derivation from
    // the family (a call's result) holds a pointer the family never gave it, which
    // reaches nothing the read names.
    let ty_has_pointer =
        |local: usize| crate::local_ty_ref(func, local).is_none_or(ty_holds_pointer);
    let name_of = |place: &Place| crate::place_to_var_name(func, place);
    let deref_of = |place: &Place| {
        let mut target = place.clone();
        target.projections.push(Projection::Deref);
        name_of(&target)
    };
    let mut family: trust_types::fx::FxHashMap<usize, Option<String>> =
        std::iter::once((root, Some(deref_of(&Place::local(root))))).collect();
    let derived = |family: &trust_types::fx::FxHashMap<usize, Option<String>>,
                   rvalue: &Rvalue|
     -> Option<Option<String>> {
        match rvalue {
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) | Rvalue::CopyForDeref(q)
                if family.contains_key(&q.local) =>
            {
                Some(if q.projections.is_empty() {
                    family[&q.local].clone()
                } else {
                    Some(deref_of(q))
                })
            }
            Rvalue::Ref { place: q, .. } | Rvalue::AddressOf(_, q)
                if family.contains_key(&q.local) =>
            {
                Some(Some(name_of(q)))
            }
            Rvalue::Cast(Operand::Copy(q) | Operand::Move(q), _)
            | Rvalue::PtrOffset { ptr: Operand::Copy(q) | Operand::Move(q), .. }
                if family.contains_key(&q.local) =>
            {
                Some(None)
            }
            _ => None,
        }
    };
    let rvalue_mentions_family =
        |family: &trust_types::fx::FxHashMap<usize, Option<String>>, rvalue: &Rvalue| match rvalue {
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
            | Rvalue::CopyForDeref(q)
            | Rvalue::Ref { place: q, .. }
            | Rvalue::AddressOf(_, q)
            | Rvalue::Cast(Operand::Copy(q) | Operand::Move(q), _)
            | Rvalue::PtrOffset { ptr: Operand::Copy(q) | Operand::Move(q), .. } => {
                family.contains_key(&q.local)
            }
            _ => false,
        };
    loop {
        let mut changed = false;
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place, rvalue, .. } = stmt else { continue };
                if !place.projections.is_empty()
                    || matches!(family.get(&place.local), Some(None))
                    || !rvalue_mentions_family(&family, rvalue)
                    || !ty_has_pointer(place.local)
                {
                    continue;
                }
                let Some(region) = derived(&family, rvalue) else { continue };
                match family.get(&place.local) {
                    None => {
                        family.insert(place.local, region);
                        changed = true;
                    }
                    Some(existing) if *existing != region && existing.is_some() => {
                        family.insert(place.local, None);
                        changed = true;
                    }
                    Some(_) => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Region-restricted: every pointer in the family must be a reference (see
    // `deref_read_is_unwritten_within`).
    if within.is_some()
        && family.iter().any(|(&local, region)| {
            region.is_none() || !matches!(crate::local_ty_ref(func, local), Some(Ty::Ref { .. }))
        })
    {
        return false;
    }
    let counts =
        |block: trust_types::BlockId, at: Option<usize>| within.is_none_or(|w| w(block, at));

    // 3. What may change the place.
    let store_may_write = |dest: &Place| {
        let name = crate::place_to_var_name(func, dest);
        crate::generate::write_rebinds(&name, &read_name)
            || (family.contains_key(&dest.local)
                && !dest.projections.is_empty()
                && root_of(&name) != read_root)
    };
    // Nothing on the read's path is an `UnsafeCell`, so a shared reference to any part
    // of it cannot write it. A type this cannot follow answers no. Trust: 2026-10-15
    // (INTERIOR-MUT-CHANNEL-1): a hop refuses a cell wrapper by the one name list
    // (`Cell` itself, not only `UnsafeCell`), and the LEAF asks the one structural
    // predicate: a read of `S { n, c: Cell }` whole reads cell bytes although no type on
    // its path is a cell.
    let path_is_freeze = {
        let cell = |t: &Ty| crate::guards::ty_is_interior_mut_wrapper(t);
        let leaf_may_hold_cell =
            |t: &Ty| crate::generate::ty_may_hold_unsafe_cell(&func.body.datatype_defs, t);
        let mut ty = match crate::local_ty_ref(func, read.local) {
            Some(Ty::Ref { inner, .. }) => Some(inner.as_ref()),
            _ => None,
        };
        let mut freeze = true;
        for q in &read.projections[1..] {
            let Some(t) = ty else { break };
            freeze &= !cell(t);
            ty = match (q, t) {
                (Projection::Field(index), Ty::Adt { fields, .. }) => {
                    fields.get(*index).map(|(_, f)| f)
                }
                (Projection::Field(index), Ty::Tuple(elems)) => elems.get(*index),
                (
                    Projection::Index(..) | Projection::ConstantIndex { .. },
                    Ty::Slice { elem } | Ty::Array { elem, .. },
                ) => Some(elem.as_ref()),
                _ => None,
            };
        }
        freeze && ty.is_some_and(|t| !leaf_may_hold_cell(t))
    };
    // A family POINTER leaving through `op`: the pointer itself, or a pointer reloaded
    // through one. A shared reference cannot write the place when its path is freeze.
    let hands_out_place = |q: &Place| {
        let Some(region) = family.get(&q.local) else { return false };
        // A pointer that can reach only a place disjoint from the read cannot write it.
        // Disjoint is decided only between names of one root; names the canonicalizer
        // spelled from different roots cannot be compared.
        if q.projections.is_empty()
            && let Some(region) = region
            && root_of(region) == read_root
            && !crate::generate::place_names_overlap(region, &read_name)
        {
            return false;
        }
        let value_ty = if q.projections.is_empty() {
            crate::local_ty_ref(func, q.local).map(std::borrow::Cow::Borrowed)
        } else {
            crate::place_ty_cow(func, q)
        };
        match value_ty.as_deref() {
            Some(Ty::Ref { mutable: false, .. }) => !path_is_freeze,
            Some(t) => ty_holds_pointer(t),
            None => true,
        }
    };
    let hands_out = |op: &Operand| match op {
        Operand::Copy(q) | Operand::Move(q) => hands_out_place(q),
        _ => false,
    };
    let mentions_family = |op: &Operand| matches!(op, Operand::Copy(q) | Operand::Move(q) if family.contains_key(&q.local));
    // Only a STORE is judged by the region. A hand-out counts wherever it is: a callee
    // handed a `&mut` can return or stash a raw pointer derived from it, which the
    // borrow checker does not track, and a later call handed nothing can write through
    // it. `let p = raw_of(s); for i in 0..s.n { poke(p); s.n - i - 1 }` was proved
    // and panics when this rule read hand-outs by region (review8 `p4_raw2`).
    for block in &func.body.blocks {
        for (index, stmt) in block.stmts.iter().enumerate() {
            let in_region = counts(block.id, Some(index));
            let may_write = match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    (in_region && store_may_write(place))
                        || match rvalue {
                            // A derivation into a bare local is followed through the
                            // family; into memory it is a hand-out.
                            Rvalue::Use(op) | Rvalue::Cast(op, _) => {
                                !place.projections.is_empty() && hands_out(op)
                            }
                            Rvalue::Ref { place: q, .. } | Rvalue::AddressOf(_, q) => {
                                !place.projections.is_empty() && family.contains_key(&q.local) && {
                                    let q_name = name_of(q);
                                    root_of(&q_name) != read_root
                                        || crate::generate::place_names_overlap(&q_name, &read_name)
                                }
                            }
                            Rvalue::CopyForDeref(q) => {
                                !place.projections.is_empty() && hands_out_place(q)
                            }
                            Rvalue::PtrOffset { ptr, .. } => {
                                !place.projections.is_empty() && mentions_family(ptr)
                            }
                            Rvalue::Aggregate(_, ops)
                            | Rvalue::Unsupported { operands: ops, .. } => {
                                ops.iter().any(hands_out)
                            }
                            Rvalue::Repeat(op, _) => hands_out(op),
                            // Comparisons, metadata and value reads write nothing.
                            Rvalue::BinaryOp(..)
                            | Rvalue::CheckedBinaryOp(..)
                            | Rvalue::UncheckedBinaryOp(..)
                            | Rvalue::UnaryOp(..)
                            | Rvalue::Discriminant(_)
                            | Rvalue::Len(_) => false,
                            other => family.keys().any(|&l| rvalue_mentions(other, l)),
                        }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    in_region && store_may_write(place)
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => false,
                Statement::Intrinsic { args, .. }
                | Statement::Unsupported { operands: args, .. } => args.iter().any(mentions_family),
                Statement::CopyNonOverlapping { dst, .. } => mentions_family(dst),
                _ => true,
            };
            if may_write {
                return false;
            }
        }
        let in_region = counts(block.id, None);
        let may_write = match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                (in_region && store_may_write(dest)) || args.iter().any(hands_out)
            }
            Terminator::TailCall { args, .. } => args.iter().any(hands_out),
            Terminator::Drop { place, .. } => in_region && store_may_write(place),
            Terminator::Opaque { .. } => true,
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Unreachable
            | Terminator::Resume => false,
            _ => true,
        };
        if may_write {
            return false;
        }
    }
    true
}

/// How a POINTER local gets its one value, when nothing re-points it: `Some(None)` for a
/// parameter never written, `Some(Some(rvalue))` for a local whose only whole write is
/// that `Assign`, and `None` when it may be re-pointed (a second whole write, a `Call`
/// result, a partial or unlocatable write).
///
/// Narrower than [`body_holds_one_value`] on purpose: an ALIAS of the pointer local is
/// not counted, because [`deref_read_is_never_written`] follows it as a family pointer,
/// and an alias that can reach the pointer itself (`&mut p`) reaches everything behind
/// it and counts as a write of the read there. The seam's value question refuses any
/// mutable alias, and a reborrow of the POINTEE (`&mut (*s).buf`) is one to it, which
/// left `for i in 0..b.n { b.buf.push(1); … }` without its bound.
fn pointer_local_definition(body: &VerifiableBody, local: usize) -> Option<Option<&Rvalue>> {
    let parameter = body_is_parameter(body, local);
    let mut whole_count = 0usize;
    let mut single_rvalue: Option<&Rvalue> = None;
    let mut repointed = false;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched | LocalWrite::Escape => {}
        LocalWrite::WholeNamed(rvalue) => {
            if whole_count == 0 {
                single_rvalue = Some(rvalue);
            } else {
                single_rvalue = None;
            }
            whole_count += 1;
        }
        LocalWrite::WholeOpaque => {
            single_rvalue = None;
            whole_count += 1;
        }
        LocalWrite::Partial | LocalWrite::Unlocatable => repointed = true,
    });
    match (repointed, parameter, whole_count, single_rvalue) {
        (false, true, 0, _) => Some(None),
        (false, false, 1, Some(rvalue)) => Some(Some(rvalue)),
        _ => None,
    }
}

/// Whether a value of `ty` carries a data pointer (a reference or raw pointer, at any
/// depth of a struct, tuple or array). An unknown shape answers yes.
fn ty_holds_pointer(ty: &trust_types::Ty) -> bool {
    use trust_types::Ty;
    match ty {
        Ty::Ref { .. } | Ty::RawPtr { .. } => true,
        Ty::Bool
        | Ty::Char
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Float { .. }
        | Ty::Unit => false,
        Ty::Array { elem, .. } => ty_holds_pointer(elem),
        Ty::Tuple(elems) => elems.iter().any(ty_holds_pointer),
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, f)| ty_holds_pointer(f))
                || variants.iter().any(|v| v.fields.iter().any(|(_, f)| ty_holds_pointer(f)))
        }
        _ => true,
    }
}

/// Whether `rvalue` names `local` anywhere, for the rvalues [`deref_read_is_never_written`]
/// does not classify one by one (fail closed: an unlisted variant names it).
fn rvalue_mentions(rvalue: &Rvalue, local: usize) -> bool {
    use trust_types::Operand;
    let op = |o: &Operand| matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == local);
    match rvalue {
        Rvalue::Use(o) | Rvalue::UnaryOp(_, o) | Rvalue::Cast(o, _) | Rvalue::Repeat(o, _) => op(o),
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => op(a) || op(b),
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place.local == local,
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => ops.iter().any(op),
        Rvalue::PtrOffset { ptr, count } => op(ptr) || op(count),
        _ => true,
    }
}

/// See [`body_is_parameter`].
pub fn is_parameter(func: &VerifiableFunction, local: usize) -> bool {
    body_is_parameter(&func.body, local)
}

/// See [`body_value_count`].
pub fn value_count(func: &VerifiableFunction, local: usize) -> ValueCount {
    body_value_count(&func.body, local)
}

/// See [`body_holds_one_value`].
pub fn holds_one_value(func: &VerifiableFunction, local: usize) -> bool {
    body_holds_one_value(&func.body, local)
}

/// See [`body_never_explicitly_reseated`].
pub fn never_explicitly_reseated(func: &VerifiableFunction, local: usize) -> bool {
    body_never_explicitly_reseated(&func.body, local)
}

/// See [`body_has_one_explicit_def`].
pub fn has_one_explicit_def(func: &VerifiableFunction, local: usize) -> bool {
    body_has_one_explicit_def(&func.body, local)
}

/// See [`body_every_write_is_whole_named`].
pub fn every_write_is_whole_named(func: &VerifiableFunction, local: usize) -> bool {
    body_every_write_is_whole_named(&func.body, local)
}

/// See [`body_every_write_is_whole_located`].
pub fn every_write_is_whole_located(func: &VerifiableFunction, local: usize) -> bool {
    body_every_write_is_whole_located(&func.body, local)
}

/// See [`body_unique_value_def`].
pub fn unique_value_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    body_unique_value_def(&func.body, local)
}

/// See [`body_value_defs`].
pub fn value_defs(func: &VerifiableFunction, local: usize) -> Option<Vec<(usize, &Rvalue)>> {
    body_value_defs(&func.body, local)
}

/// See [`body_unique_value_def_modulo_pointee_borrows`] — and read it before calling
/// this, because it is a NARROWER question than [`unique_value_def`] and carries a
/// caller-side obligation. The referent fold is its only caller.
pub fn unique_value_def_modulo_pointee_borrows(
    func: &VerifiableFunction,
    local: usize,
) -> Option<&Rvalue> {
    body_unique_value_def_modulo_pointee_borrows(&func.body, local)
}

/// See [`body_unique_initializing_def`] — and read it before calling this, because it
/// is NOT a value question and has a caller-side precondition.
pub fn unique_initializing_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    body_unique_initializing_def(&func.body, local)
}

/// See [`body_unique_value_call`].
pub fn unique_value_call(func: &VerifiableFunction, local: usize) -> Option<&Terminator> {
    body_unique_value_call(&func.body, local)
}

/// See [`body_unique_initializing_call`] — and read it before calling this, because it
/// is NOT a value question and has a caller-side precondition.
pub fn unique_initializing_call(func: &VerifiableFunction, local: usize) -> Option<&Terminator> {
    body_unique_initializing_call(&func.body, local)
}

/// See [`body_unique_value_modulo_whole_drops`].
pub(crate) fn unique_value_modulo_whole_drops(
    func: &VerifiableFunction,
    local: usize,
) -> Option<WholeDefinition<'_>> {
    body_unique_value_modulo_whole_drops(&func.body, local)
}

/// See [`body_unique_initializing_modulo_whole_drops`] — and read it before calling this,
/// because it is NOT a value question and has a caller-side precondition.
pub(crate) fn unique_initializing_modulo_whole_drops(
    func: &VerifiableFunction,
    local: usize,
) -> Option<WholeDefinition<'_>> {
    body_unique_initializing_modulo_whole_drops(&func.body, local)
}

/// See [`body_value_calls`] — the JOIN question; a fact built on it must be a
/// disjunction over every returned call.
pub fn value_calls(func: &VerifiableFunction, local: usize) -> Option<Vec<&Terminator>> {
    body_value_calls(&func.body, local)
}

/// See [`body_is_single_static_assignment`].
pub fn is_single_static_assignment(func: &VerifiableFunction, local: usize) -> bool {
    body_is_single_static_assignment(&func.body, local)
}

/// See [`body_is_single_static_assignment_modulo_pointee_borrows`] — the SSA question
/// asked with the same escape classifier as
/// [`unique_value_def_modulo_pointee_borrows`], so the two cannot answer differently
/// about the same local. Callers: the referent fold; the interval transfer's
/// parameter-store exemption (`store_through_unreseated_mut_param`), which asks whether
/// the parameter's own slot can be reseated; and (TRUST-10)
/// `generate::return_field_summary`'s call-site gate, which asks whether a POINTER
/// parameter can be rebound and keys nothing on its bare name — what it reaches is
/// versioned per point by the statement oracle.
pub fn is_single_static_assignment_modulo_pointee_borrows(
    func: &VerifiableFunction,
    local: usize,
) -> bool {
    body_is_single_static_assignment_modulo_pointee_borrows(&func.body, local)
}

/// See [`body_path_is_single_static_assignment`] — the PATH question, for a name whose
/// value lives in the place itself (a fat pointer's length) and not in its contents.
pub fn path_is_single_static_assignment(
    func: &VerifiableFunction,
    path: &trust_types::Place,
) -> bool {
    body_path_is_single_static_assignment(&func.body, path)
}

/// See [`body_place_index_locals_are_single_static_assignment`] — the INDEX-LOCAL
/// question, for a name that embeds an `Index(l)` projection by number.
pub fn place_index_locals_are_single_static_assignment(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    body_place_index_locals_are_single_static_assignment(&func.body, place)
}

/// See [`body_dest_fact_is_version_pinnable`].
pub fn dest_fact_is_version_pinnable(func: &VerifiableFunction, local: usize) -> bool {
    body_dest_fact_is_version_pinnable(&func.body, local)
}

/// See [`body_stmt_dest_fact_is_version_pinnable_at`].
pub fn stmt_dest_fact_is_version_pinnable_at(
    func: &VerifiableFunction,
    local: usize,
    block_index: usize,
    stmt_index: usize,
) -> bool {
    body_stmt_dest_fact_is_version_pinnable_at(&func.body, local, block_index, stmt_index)
}

/// See [`body_unique_defining_block`].
pub fn unique_defining_block(func: &VerifiableFunction, local: usize) -> Option<usize> {
    body_unique_defining_block(&func.body, local)
}

/// See [`body_storage_never_aliased`] — NOT a value question; ask
/// [`unique_value_def`] beside it.
pub fn storage_never_aliased(func: &VerifiableFunction, local: usize) -> bool {
    body_storage_never_aliased(&func.body, local)
}

/// See [`body_pointer_is_pinned`] — the POINTER, not its pointee.
pub fn pointer_is_pinned(func: &VerifiableFunction, local: usize) -> bool {
    body_pointer_is_pinned(&func.body, local)
}

#[cfg(test)]
#[path = "local_defs_tests.rs"]
mod local_defs_tests;
