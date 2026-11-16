//! Trust (D2 tier 1, 2026-09-24): the `ADAPTER_YIELD` modeled fact, CLOSURE SIDE.
//!
//! A local closure `C` handed BY VALUE, exactly once, to a std iterator adapter
//! (`Iterator::{all, any, position, find, filter, map, for_each, fold}`) over a
//! receiver the COMPILER traced to `<[T]>::windows(k)` / `chunks_exact(k)` /
//! `chunks(k)` with a constant `k >= 1`, or to an exclusive integer `Range` with
//! constant bounds (optionally under `Iterator::rev` / `Iterator::step_by`), is
//! only ever invoked by core on an item that receiver yields. That is std's
//! documented contract, it is not re-derived (std is built `-Ztrust-verify=off`),
//! and `docs/TCB.md` ("Modeled-fact axioms") carries it as `ADAPTER_YIELD`.
//!
//! Everything that DECIDES whether the premise applies lives in the compiler
//! (`rustc_mir_transform::trust_adapter_yield`): adapter identity by the resolved
//! instance's trait item (never a rendered name), receiver identity by `DefId`
//! and lang item, the occurrence discipline over the parent's pre-inlining MIR.
//! It hands this crate one [`ClosureAdapterPremise`] per admitted closure through
//! the owner-checked [`crate::VcgenContext`]. This module only
//!
//!  * re-checks, on the body actually being verified, that the named item
//!    parameter is a never-written, never-escaped PARAMETER of the right type
//!    (a closure that reassigns or `&mut`-borrows its item gets nothing), and
//!  * turns the premise into ENTRY facts on that parameter's name, merged into
//!    the two per-block yield-fact maps every consumer already honours
//!    (`build_slice_iter_yield_guard_map` for lengths, `build_range_yield_guard_map`
//!    for integer bounds).
//!
//! Conjoining the facts at EVERY block is licensed because they are entry facts on
//! a name that is never written: the parameter has exactly one value for the whole
//! body. That is the difference from the loop-payload facts, whose
//! `block_mentions_local` restriction must not be widened
//! (`memory/refuted-fixes-do-not-repropose.md`).
//!
//! FAIL-CLOSED: no context, a context owned by another function, a premise whose
//! parameter does not pass the gates below — each yields no fact, which is exactly
//! the pre-D2 behaviour.

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;
use trust_types::{BlockId, Formula, Operand, Place, Projection, Sort, Ty, VerifiableFunction};

/// What every item the admitted receiver yields satisfies.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AdapterYieldFact {
    /// `windows(len)` / `chunks_exact(len)`: every item is a sub-slice of length
    /// exactly `len`.
    SliceLenEq { len: u64 },
    /// `chunks(max)`: every item is a sub-slice of length in `[min, max]`
    /// (`min` is 1; a chunk is never empty).
    SliceLenIn { min: u64, max: u64 },
    /// `start..end` (constant bounds; also under `rev`/`step_by`): every item
    /// `i` satisfies `start <= i < end`.
    IntHalfOpen { start: i128, end: i128 },
}

impl AdapterYieldFact {
    fn family(&self) -> AdapterPremiseFamily {
        match self {
            Self::SliceLenEq { .. } | Self::SliceLenIn { .. } => AdapterPremiseFamily::SliceLen,
            Self::IntHalfOpen { .. } => AdapterPremiseFamily::IntRange,
        }
    }

    fn describe(&self) -> String {
        match self {
            Self::SliceLenEq { len } => format!("slice length {len}"),
            Self::SliceLenIn { min, max } => format!("slice length in [{min}, {max}]"),
            Self::IntHalfOpen { start, end } => format!("value in [{start}, {end})"),
        }
    }
}

/// One `ADAPTER_YIELD` premise for one closure body, minted by the compiler.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ClosureAdapterPremise {
    /// The closure body's MIR local of the parameter that receives the item
    /// (`_2` for every admitted adapter except `fold`, whose item is `_3`).
    /// Never `_0` or `_1` (the environment).
    pub item_local: usize,
    /// `filter`/`find` pass the item BEHIND ONE SHARED REFERENCE (`&Self::Item`);
    /// the fact is then about `*item_local`.
    pub item_deref: bool,
    /// Trust (2026-10-08): tuple FIELD path from the item to the value the fact is
    /// about, after the optional deref. `enumerate` yields `(index, item)`, so a
    /// receiver under one `enumerate` has `[1]`. Empty for every other receiver.
    #[serde(default)]
    pub item_fields: Vec<usize>,
    pub fact: AdapterYieldFact,
    /// Display only, for the disclosure (`Iterator::all`). Never read as authority.
    pub adapter: String,
    /// Display only, for the disclosure (`<[T]>::windows(2)`). Never read as
    /// authority.
    pub receiver: String,
}

impl ClosureAdapterPremise {
    /// The disclosure every row of a premise-bearing body carries (the human
    /// note and the JSON `modeled_facts` entry). Starts with the premise's name so
    /// a consumer can key on it.
    #[must_use]
    pub fn disclosure(&self) -> String {
        let mut item = match (self.item_deref, self.item_fields.is_empty()) {
            (true, true) => format!("*_{}", self.item_local),
            (true, false) => format!("(*_{})", self.item_local),
            (false, _) => format!("_{}", self.item_local),
        };
        for field in &self.item_fields {
            item.push_str(&format!(".{field}"));
        }
        format!(
            "ADAPTER_YIELD: core `{}` over `{}` invokes this closure only on items it yields; \
             assumed: item parameter `{item}` has {}",
            self.adapter,
            self.receiver,
            self.fact.describe()
        )
    }
}

/// Which per-block map a premise feeds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AdapterPremiseFamily {
    /// Merged into `build_slice_iter_yield_guard_map`.
    SliceLen,
    /// Merged into `build_range_yield_guard_map`.
    IntRange,
}

/// The entry facts `func`'s installed premises of `family` license, after the
/// closure-side gates. Empty — the pre-D2 behaviour — for every function the
/// compiler installed nothing for.
fn adapter_premise_entry_facts(
    func: &VerifiableFunction,
    family: AdapterPremiseFamily,
) -> Vec<Formula> {
    let premises = crate::adapter_yield_premises_for(&func.def_path);
    if premises.is_empty() {
        return Vec::new();
    }
    premises
        .iter()
        .filter(|premise| premise.fact.family() == family)
        .filter_map(|premise| premise_facts(func, premise))
        .flatten()
        .collect()
}

/// Merge `func`'s `family` premise facts into a per-block yield map, at EVERY
/// block (see the module doc for why that is licensed). A no-op — the map is
/// untouched, byte for byte — when there is no premise.
pub(crate) fn extend_with_adapter_premise_facts(
    func: &VerifiableFunction,
    map: &mut FxHashMap<BlockId, Vec<Formula>>,
    family: AdapterPremiseFamily,
) {
    let facts = adapter_premise_entry_facts(func, family);
    if facts.is_empty() {
        return;
    }
    for block in &func.body.blocks {
        map.entry(block.id).or_default().extend(facts.iter().cloned());
    }
}

/// The facts one premise licenses on THIS body, or `None` when a closure-side
/// gate refuses.
fn premise_facts(
    func: &VerifiableFunction,
    premise: &ClosureAdapterPremise,
) -> Option<Vec<Formula>> {
    let local = premise.item_local;
    // A PARAMETER other than the environment. `_0` is the return place and `_1`
    // the closure's own environment; neither is an item.
    if local < 2 || !crate::local_defs::is_parameter(func, local) {
        return None;
    }
    // Never written and never escaped: the parameter's entry value is its only
    // value, so a fact on its bare name is a fact about every read of it. A
    // `&mut`/`&raw` borrow, a reassignment, or a partial write refuses.
    if !crate::local_defs::is_single_static_assignment(func, local) {
        return None;
    }
    let local_ty = crate::local_ty_ref(func, local)?;
    let mut place = if premise.item_deref {
        // `&Self::Item`: a SHARED reference, and nothing writes through it.
        if !matches!(local_ty, Ty::Ref { mutable: false, .. }) {
            return None;
        }
        let place = Place { local, projections: vec![Projection::Deref] };
        if !crate::local_defs::path_is_single_static_assignment(func, &place) {
            return None;
        }
        place
    } else {
        Place::local(local)
    };
    // Trust (2026-10-08): the `enumerate` field path. The field of a never-written
    // parameter (or of its never-written-through pointee) is itself never written;
    // `path_is_single_static_assignment` re-checks that on the projected place.
    if !premise.item_fields.is_empty() {
        place.projections.extend(premise.item_fields.iter().map(|f| Projection::Field(*f)));
        if !crate::local_defs::path_is_single_static_assignment(func, &place) {
            return None;
        }
    }
    let item_ty = crate::place_ty_cow(func, &place)?;
    match &premise.fact {
        AdapterYieldFact::SliceLenEq { len } => {
            let len_f = shared_slice_len(func, &place, &item_ty)?;
            let len = Formula::Int(i128::from(*len));
            Some(
                std::iter::once(len_f)
                    .chain(stable_copy_slice_lens(func, &place))
                    .map(|len_f| Formula::Eq(Box::new(len_f), Box::new(len.clone())))
                    .collect(),
            )
        }
        AdapterYieldFact::SliceLenIn { min, max } => {
            if min > max {
                return None;
            }
            let len_f = shared_slice_len(func, &place, &item_ty)?;
            let (min, max) = (Formula::Int(i128::from(*min)), Formula::Int(i128::from(*max)));
            Some(
                std::iter::once(len_f)
                    .chain(stable_copy_slice_lens(func, &place))
                    .flat_map(|len_f| {
                        [
                            Formula::Ge(Box::new(len_f.clone()), Box::new(min.clone())),
                            Formula::Le(Box::new(len_f), Box::new(max.clone())),
                        ]
                    })
                    .collect(),
            )
        }
        AdapterYieldFact::IntHalfOpen { start, end } => {
            if !matches!(*item_ty, Ty::Int { .. }) {
                return None;
            }
            let var = Formula::var(&crate::place_to_var_name(func, &place), Sort::Int);
            Some(vec![
                Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(*start))),
                Formula::Lt(Box::new(var), Box::new(Formula::Int(*end))),
            ])
        }
    }
}

/// The length terms of every local that holds a COPY of the item for the whole
/// body: a single static assignment (one whole write, no partial write, no
/// `&mut`/`&raw` escape) whose one definition is `Use(Copy|Move(item_place))`,
/// of type `&[T]`.
///
/// WHY. Every access `w[i]` through a `&&[T]` item (`filter`/`find`) makes rustc
/// mint a fresh auto-deref temp, `_k = copy (*_2)`, and the index row reads
/// `_k`'s OWN length term `_k__slice_len`. The rvalue lane gives that row no
/// same-block definition of `_k` (a premise-independent gap: `fn g(s: &&[u32])
/// -> u32 { s[0] }` is refuted on the snapshot with `_7__slice_len#s1_0 = 0`), so
/// the premise on `*_2` alone never reaches it. The copy's value IS the item's
/// value — `_k` is written once, from a place that is never written — so its
/// length is the item's length and the same yield fact holds of it. This is a
/// DEFINITIONAL consequence of the premise, not a second premise.
///
/// The facts are bare-named; both consuming lanes version-rename them with the
/// row they are conjoined onto, exactly like the loop-payload facts.
fn stable_copy_slice_lens(func: &VerifiableFunction, item_place: &Place) -> Vec<Formula> {
    func.body
        .locals
        .iter()
        .filter(|decl| decl.index != item_place.local)
        .filter(|decl| is_shared_slice_ref(&decl.ty))
        .filter(|decl| !crate::local_defs::is_parameter(func, decl.index))
        .filter(|decl| crate::local_defs::is_single_static_assignment(func, decl.index))
        .filter(|decl| {
            matches!(
                crate::local_defs::unique_value_def(func, decl.index),
                Some(trust_types::Rvalue::Use(Operand::Copy(src) | Operand::Move(src)))
                    if src == item_place
            )
        })
        .filter_map(|decl| crate::slice_len_formula(func, &Operand::Copy(Place::local(decl.index))))
        .collect()
}

/// `&[T]` (a SHARED reference to a slice).
fn is_shared_slice_ref(ty: &Ty) -> bool {
    matches!(ty, Ty::Ref { mutable: false, inner } if matches!(inner.as_ref(), Ty::Slice { .. }))
}

/// The modeled length of the shared sub-slice at `place` — the SAME
/// place-keyed term (`{place}__slice_len`) the bounds rows of this body read
/// (`crate::slice_len_formula`). `None` unless `place` is an `&[T]`.
fn shared_slice_len(func: &VerifiableFunction, place: &Place, item_ty: &Ty) -> Option<Formula> {
    if !is_shared_slice_ref(item_ty) {
        return None;
    }
    crate::slice_len_formula(func, &Operand::Copy(place.clone()))
}
