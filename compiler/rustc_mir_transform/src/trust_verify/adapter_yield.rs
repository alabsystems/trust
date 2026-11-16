//! Trust (D2 tier 1, 2026-09-24): the `ADAPTER_YIELD` modeled fact, COMPILER side.
//!
//! ## What is assumed
//!
//! std's documented contract for a closure handed to a core iterator adapter:
//! `Iterator::{all, any, position, find, filter, map, for_each, fold}` invoke the
//! closure only on items the receiver yields (`filter`/`find` behind one `&`,
//! `fold` as the second argument). For the receivers admitted here the item set
//! is known statically:
//!
//! * `<[T]>::windows(k)` / `<[T]>::chunks_exact(k)`, `k` a constant `>= 1`: every
//!   item is a sub-slice of length exactly `k`;
//! * `<[T]>::chunks(k)`, `k` a constant `>= 1`: length in `[1, k]`;
//! * any of the three with a NON-constant `k`: length in `[1, usize::MAX]` (each
//!   constructor panics on a zero size, charged at its call);
//! * an exclusive integer `Range { start, end }` with constant bounds:
//!   `start <= i < end`;
//! * any of these under a stack of `Iterator::rev` / `step_by` / `filter` /
//!   `skip` / `take`, which hand on only inner items, unchanged, and
//!   `enumerate`, which pairs each inner item with its index: the fact is then
//!   about field 1 of the closure's item (`ClosureAdapterPremise::item_fields`).
//!
//! std is built `-Ztrust-verify=off`; nothing re-derives this. It is recorded as
//! `ADAPTER_YIELD` in `docs/TCB.md` ("Modeled-fact axioms"), checked against the
//! pinned sysroot source, including the core OVERRIDES a resolved call may land
//! on (`Rev::fold`/`find`, `StepBy::fold` and the `StepBy<Range<uN>>`
//! specialization that repurposes `end` as a remaining-count, `Filter::fold`/
//! `count`, `Map::fold`): each still applies the closure only to items of the
//! inner iterator.
//!
//! ## What this module decides (everything is by `DefId` / type / lang item)
//!
//! For each local closure `C` whose parent `P` is a non-generic, non-const,
//! non-`async` `fn`/method (never a closure, a coroutine, or a const context),
//! read `P`'s PRE-INLINING MIR — `mir_drops_elaborated_and_const_checked`,
//! borrowed before anything steals it (a stolen body admits nothing) — plus its
//! promoteds, and admit `C` only when:
//!
//! 1. ADAPTER IDENTITY. `C`'s value is an argument of exactly one `Call`, whose
//!    callee is a method of the `Iterator` LANG ITEM in the admitted list, at the
//!    argument position that method's signature gives its closure; the call's
//!    instance RESOLVES (`Instance::try_resolve`) to an `InstanceKind::Item` in an
//!    authentic foundational crate whose trait item is that same method. A user
//!    `impl Iterator` that overrides `all` resolves into the user's crate and is
//!    refused; core's own overrides are admitted.
//! 2. BY VALUE, ONCE. The argument's type is exactly `C` (never `&C`/`&mut C`).
//! 3. RECEIVER. The call's receiver (`&mut R` for the `&mut self` adapters, `R`
//!    by value otherwise) is a local written exactly once — by the admitted
//!    constructor — and used exactly once more, by this call (or its one `&mut`
//!    conduit, itself written once and consumed by this call). The constructor is
//!    an inherent method of `[T]` in an authentic foundational crate
//!    (`windows`/`chunks`/`chunks_exact`), or the `Range` lang-item aggregate
//!    with CONSTANT bounds, optionally through `Iterator::rev`/`step_by`/
//!    `filter`/`skip`/`take` resolved into a foundational crate.
//! 4. OCCURRENCE DISCIPLINE. Every mention of `C`'s type in `P` — local
//!    declarations, constant operands (including the adapter's own `FnDef`),
//!    located types, closure aggregates — is accounted for: the one closure value
//!    (a `const ZeroSized: C` operand, or a local written once by
//!    `Aggregate(Closure(C))` and moved once into the adapter), and, for
//!    `filter`/`map` only, the adapter's result, written once and consumed once
//!    by a core `Iterator` method — moved into it, or through one `&mut` conduit
//!    written once and moved once into it — whose result does not mention `C`,
//!    whose own generic arguments do not mention `C`, and which has no generic
//!    parameters of its own or (2026-10-04) whose own generic arguments AND the
//!    adapter's item type name only primitives, foundational-crate types and
//!    foundational-crate fn items (`fold(.., f64::min)`; an `unsafe fn` item has no
//!    `Fn` impl, and a fn item's own arguments are walked too), so its trait
//!    dispatch can only select a foundational impl and its callable argument is
//!    core code. The one exception (merge 2026-10-14) is a consumer whose own
//!    where-clauses are ALL `Fn`-family or sizedness bounds (`fold`, `any`, `all`,
//!    `find`, `position`): no impl it selects can receive the adapter value, so a
//!    local closure or fn item there is admitted on the first condition alone. A
//!    crate enabling specialization gets no premise. `_0` and the arguments never
//!    mention `C`; no promoted mentions it. So no user code, `unsafe` or not, can
//!    reach `C`'s value or a reference to it, and nothing but the admitted core
//!    code can invoke its body — PROVIDED the crate cannot name `C` elsewhere
//!    through an opaque alias, which is why a crate enabling
//!    `type_alias_impl_trait` or `impl_trait_in_assoc_type` gets no premise at all.
//!
//! What it does NOT decide: whether the closure body may use the premise. That
//! is re-gated in `trust_vcgen` (`generate::adapter_yield`) on the body actually
//! verified — the item parameter must be a never-written, never-escaped shared
//! parameter of the right type.
//!
//! Everything fails CLOSED: any mismatch installs nothing, which is exactly the
//! pre-D2 behaviour. `-Ztrust-no-adapter-yield` installs nothing at all.

use rustc_middle::mir::visit::{
    MutatingUseContext, NonMutatingUseContext, PlaceContext, TyContext, Visitor,
};
use rustc_middle::mir::{AggregateKind, BorrowKind, ConstOperand, Location, Promoted};

use super::*;

/// The admitted adapters: `(Iterator method, closure argument index, closure
/// parameter index of the item, item behind one `&`, receiver taken by `&mut self`,
/// result is a lazy adapter carrying the closure)`.
struct AdapterShape {
    name: &'static str,
    closure_arg: usize,
    item_param: usize,
    item_deref: bool,
    by_mut_ref: bool,
    lazy: bool,
}

const ADAPTERS: &[AdapterShape] = &[
    AdapterShape {
        name: "all",
        closure_arg: 1,
        item_param: 0,
        item_deref: false,
        by_mut_ref: true,
        lazy: false,
    },
    AdapterShape {
        name: "any",
        closure_arg: 1,
        item_param: 0,
        item_deref: false,
        by_mut_ref: true,
        lazy: false,
    },
    AdapterShape {
        name: "position",
        closure_arg: 1,
        item_param: 0,
        item_deref: false,
        by_mut_ref: true,
        lazy: false,
    },
    AdapterShape {
        name: "find",
        closure_arg: 1,
        item_param: 0,
        item_deref: true,
        by_mut_ref: true,
        lazy: false,
    },
    AdapterShape {
        name: "filter",
        closure_arg: 1,
        item_param: 0,
        item_deref: true,
        by_mut_ref: false,
        lazy: true,
    },
    AdapterShape {
        name: "map",
        closure_arg: 1,
        item_param: 0,
        item_deref: false,
        by_mut_ref: false,
        lazy: true,
    },
    AdapterShape {
        name: "for_each",
        closure_arg: 1,
        item_param: 0,
        item_deref: false,
        by_mut_ref: false,
        lazy: false,
    },
    AdapterShape {
        name: "fold",
        closure_arg: 2,
        item_param: 1,
        item_deref: false,
        by_mut_ref: false,
        lazy: false,
    },
];

/// Walk-depth bound for `rev`/`step_by` stacks over a range.
const RECEIVER_FUEL: u32 = 8;

/// The analysis-seam initializer, called from `rustc_interface::passes::analysis`
/// on a front-end-clean crate BEFORE `trust_init_backing_certificates` (which can
/// force `optimized_mir`, and with it this pass, for some bodies). A closure
/// verified before this seam sees an empty map and fails closed.
// The trace iterates the premise map only to SORT it before printing.
#[allow(rustc::potential_query_instability)]
pub fn trust_init_adapter_yield_premises(tcx: TyCtxt<'_>) {
    if !verification_enabled(tcx.sess)
        || with_crate_verification_state(tcx.sess, |state| state.adapter_yield_initialized)
    {
        return;
    }
    // A crate that can name a closure type crate-wide through an opaque alias
    // (`type P = impl Fn(..)`, `type_alias_impl_trait` / `impl_trait_in_assoc_type`)
    // defeats the occurrence accounting below, which reads only the PARENT's MIR:
    // another function can conjure `P` (e.g. `transmute::<(), P>(())` for a
    // capture-free closure, not UB) and invoke the body on items the adapter never
    // yielded. Measured by the D2 adversarial review (2026-09-25, probe fp18):
    // today only an unrelated unsafe-code row blocks it. Decline the premise
    // crate-wide rather than lean on that.
    let features = tcx.features();
    // Trust (2026-10-04): specialization lets a user impl select on the adapter's
    // concrete type (`impl<F> P for Map<Range<usize>, F>`) and so bind `F = C` in user
    // code; decline crate-wide for the same reason.
    let premises = if tcx.sess.opts.unstable_opts.trust_no_adapter_yield
        || features.type_alias_impl_trait()
        || features.impl_trait_in_assoc_type()
        || features.specialization()
        || features.min_specialization()
    {
        FxHashMap::default()
    } else {
        collect_premises(tcx)
    };
    if env_flag_enabled("TRUST_ADAPTER_YIELD_TRACE") {
        let mut rows: Vec<_> = premises
            .iter()
            .map(|(def, premises)| {
                (
                    def.local_def_index.as_u32(),
                    trust_mir_extract::safe_def_path_str(tcx, def.to_def_id()),
                    premises.iter().map(|p| p.disclosure()).collect::<Vec<_>>(),
                )
            })
            .collect();
        rows.sort();
        for (_, path, disclosures) in rows {
            eprintln!("TRUST_ADAPTER_YIELD_TRACE: {path}: {disclosures:?}");
        }
    }
    with_crate_verification_state(tcx.sess, |state| {
        state.adapter_yield_premises = premises;
        state.adapter_yield_initialized = true;
    });
}

/// The premises installed for the body being verified: its OWN item body (never a
/// promoted, never a shim).
pub(super) fn premises_for_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<trust_vcgen::ClosureAdapterPremise> {
    if body.source.promoted.is_some() {
        return Vec::new();
    }
    let ty::InstanceKind::Item(def) = body.source.instance else {
        return Vec::new();
    };
    let Some(local) = def.as_local() else {
        return Vec::new();
    };
    with_crate_verification_state(tcx.sess, |state| {
        state.adapter_yield_premises.get(&local).cloned().unwrap_or_default()
    })
}

/// Whether ANY premise was installed for `def` — keyed on installation, not on
/// whether vcgen's closure-side gates later used it. Such a body is never
/// check-elided (`elide_kernel_certified_checks`): a false premise may then yield
/// a panicking program reported panic-free, never a removed runtime check.
pub(super) fn body_carries_premise(tcx: TyCtxt<'_>, def: DefId) -> bool {
    let Some(local) = def.as_local() else {
        return false;
    };
    with_crate_verification_state(tcx.sess, |state| {
        state.adapter_yield_premises.get(&local).is_some_and(|premises| !premises.is_empty())
    })
}

/// The disclosure strings for `body` — the JSON `modeled_facts` entries and the
/// human note text. Empty for every body without a premise.
pub(super) fn modeled_facts<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<String> {
    premises_for_body(tcx, body).iter().map(|premise| premise.disclosure()).collect()
}

/// The human disclosure: one note per premise, on the closure's own span.
pub(super) fn note_premise_disclosure<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    for note in prepare_premise_disclosures(tcx, body) {
        note.emit(tcx);
    }
}

pub(super) fn prepare_premise_disclosures<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<PreparedLocatedNote> {
    let mut notes = Vec::new();
    for fact in modeled_facts(tcx, body) {
        notes.push(PreparedLocatedNote {
            span: body.span,
            report: PreparedHumanReport {
                summary: format!(
                    "Trust modeled fact {fact} (assumed for every row of this body, not \
                     re-derived; docs/TCB.md, Modeled-fact axioms)"
                ),
                notes: Vec::new(),
            },
        });
    }
    notes
}

// `is_stolen()` is untracked, exactly as at the other pre-steal seams
// (`trust_init_backing_certificates`, `trust_init_r1_attributions`): this is a
// driver-level walk, not a query, and a stolen body admits nothing (fail-closed).
// The parent map's keys are SORTED before use.
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
fn collect_premises(
    tcx: TyCtxt<'_>,
) -> FxHashMap<LocalDefId, Vec<trust_vcgen::ClosureAdapterPremise>> {
    let mut out = FxHashMap::default();
    let Some(iterator) = tcx.lang_items().iterator_trait() else {
        return out;
    };
    let mut by_parent: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
    for &def in tcx.mir_keys(()) {
        if tcx.def_kind(def) != DefKind::Closure {
            continue;
        }
        // A plain closure only: never a coroutine (`async` block) or a
        // coroutine-closure (`async ||`).
        if !matches!(
            tcx.type_of(def).instantiate_identity().skip_normalization().kind(),
            ty::Closure(..)
        ) {
            continue;
        }
        by_parent.entry(tcx.local_parent(def)).or_default().push(def);
    }
    let mut parents: Vec<LocalDefId> = by_parent.keys().copied().collect();
    parents.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    for parent in parents {
        if !parent_is_eligible(tcx, parent) {
            continue;
        }
        let elaborated = tcx.mir_drops_elaborated_and_const_checked(parent);
        // A stolen body is not read through `optimized_mir`: that MIR is
        // post-inlining and the occurrence discipline below is stated over the
        // pre-inlining body. Admit nothing.
        if elaborated.is_stolen() {
            continue;
        }
        let body = elaborated.borrow();
        if body.tainted_by_errors.is_some() {
            continue;
        }
        let promoted = tcx.promoted_mir(parent);
        let mut facts = BodyFacts::default();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            facts.visit_basic_block_data(bb, data);
        }
        let mut closures = by_parent.remove(&parent).unwrap_or_default();
        closures.sort_unstable_by_key(|def| def.local_def_index.as_u32());
        for closure in closures {
            if let Some(premise) =
                derive_premise(tcx, iterator, &body, promoted, &facts, closure.to_def_id())
            {
                out.insert(closure, vec![premise]);
            }
        }
    }
    out
}

pub(super) fn parent_is_eligible(tcx: TyCtxt<'_>, parent: LocalDefId) -> bool {
    matches!(tcx.def_kind(parent), DefKind::Fn | DefKind::AssocFn)
        && tcx.hir_body_const_context(parent).is_none()
        && !tcx.is_coroutine(parent.to_def_id())
        && !tcx.asyncness(parent.to_def_id()).is_async()
        && !tcx.generics_of(parent.to_def_id()).requires_monomorphization(tcx)
        && !crate::clean_origin_mir::is_clean_origin(tcx, parent)
}

/// Everything the accounting needs about one parent body, from ONE walk over its
/// basic blocks (never `required_consts`, never debug info — neither runs).
#[derive(Default)]
pub(super) struct BodyFacts<'tcx> {
    /// Every USE of every local (`NonUse` contexts — storage markers, debug info —
    /// excluded), in visit order.
    pub(super) uses: FxHashMap<Local, Vec<(PlaceContext, Location)>>,
    /// Every constant operand's type, where it occurs.
    pub(super) consts: Vec<(Location, Ty<'tcx>)>,
    /// Every closure aggregate, where it occurs.
    pub(super) closure_aggregates: Vec<(Location, DefId)>,
    /// Every type the visitor reports at a location (cast targets, projection
    /// types, …).
    pub(super) located_tys: Vec<(Location, Ty<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> for BodyFacts<'tcx> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if matches!(context, PlaceContext::NonUse(_)) {
            return;
        }
        self.uses.entry(local).or_default().push((context, location));
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        self.consts.push((location, constant.const_.ty()));
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Aggregate(kind, _) = rvalue
            && let AggregateKind::Closure(def, _) = **kind
        {
            self.closure_aggregates.push((location, def));
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>, context: TyContext) {
        if let TyContext::Location(location) = context {
            self.located_tys.push((location, ty));
        }
    }
}

/// `&[T]` (a SHARED reference to a slice).
fn is_shared_slice_ref(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Ref(_, inner, m) if !m.is_mut() && matches!(inner.kind(), ty::Slice(_)))
}

/// Is `ty` exactly the closure type `closure` (by `DefId`: the parent is
/// non-generic, so every occurrence of `C` in it is the same type up to erased
/// regions)?
pub(super) fn is_closure_type(ty: Ty<'_>, closure: DefId) -> bool {
    matches!(ty.kind(), ty::Closure(def, _) if *def == closure)
}

/// Does `ty` mention the closure type `closure` anywhere (behind references,
/// inside ADT/closure/`FnDef` generic arguments, …)?
pub(super) fn mentions_closure(ty: Ty<'_>, closure: DefId) -> bool {
    ty.walk().any(|arg| arg.as_type().is_some_and(|t| is_closure_type(t, closure)))
}

/// Any mention of `closure` in `body` at all (local declarations, constants,
/// closure aggregates, located types). Used to refuse a closure a PROMOTED
/// reaches.
pub(super) fn body_mentions_closure<'tcx>(body: &Body<'tcx>, closure: DefId) -> bool {
    if body.local_decls.iter().any(|decl| mentions_closure(decl.ty, closure)) {
        return true;
    }
    let mut facts = BodyFacts::default();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        facts.visit_basic_block_data(bb, data);
    }
    facts.consts.iter().any(|(_, ty)| mentions_closure(*ty, closure))
        || facts.located_tys.iter().any(|(_, ty)| mentions_closure(*ty, closure))
        || facts.closure_aggregates.iter().any(|(_, def)| *def == closure)
}

/// The uses of `local` that are not drops. A drop of a value holding the closure
/// runs its drop glue (its captures' destructors), never its body.
pub(super) fn non_drop_uses(facts: &BodyFacts<'_>, local: Local) -> Vec<(PlaceContext, Location)> {
    facts
        .uses
        .get(&local)
        .map(|uses| {
            uses.iter().copied().filter(|(context, _)| !context.is_drop()).collect::<Vec<_>>()
        })
        .unwrap_or_default()
}

pub(super) fn statement_at<'a, 'tcx>(
    body: &'a Body<'tcx>,
    location: Location,
) -> Option<&'a Statement<'tcx>> {
    body.basic_blocks.get(location.block)?.statements.get(location.statement_index)
}

/// The `Call` terminator at `location`, if `location` is exactly a terminator.
fn call_at<'a, 'tcx>(body: &'a Body<'tcx>, location: Location) -> Option<&'a TerminatorKind<'tcx>> {
    let data = body.basic_blocks.get(location.block)?;
    if location.statement_index != data.statements.len() {
        return None;
    }
    let kind = &data.terminator().kind;
    matches!(kind, TerminatorKind::Call { .. }).then_some(kind)
}

pub(super) fn terminator_location(body: &Body<'_>, bb: BasicBlock) -> Location {
    Location { block: bb, statement_index: body.basic_blocks[bb].statements.len() }
}

/// A whole-local operand (`copy _l` / `move _l`, no projection).
fn whole_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        _ => None,
    }
}

/// A resolved `Iterator` method call: the MIR callee is `method` (a method of the
/// `Iterator` lang item) and the instance resolves to an item in an authentic
/// foundational crate that IS that method or core's override of it. Returns the
/// method's name.
pub(super) fn authenticated_iterator_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    iterator: DefId,
    func: &Operand<'tcx>,
) -> Option<(DefId, ty::GenericArgs<'tcx>, String)> {
    let (method, args) = func.const_fn_def()?;
    if tcx.def_kind(method) != DefKind::AssocFn || tcx.trait_of_assoc(method) != Some(iterator) {
        return None;
    }
    let instance = ty::Instance::try_resolve(tcx, body.typing_env(tcx), method, args).ok()??;
    let ty::InstanceKind::Item(item) = instance.def else {
        return None;
    };
    if !crate_is_authentic_foundational(tcx, item.krate) {
        return None;
    }
    let trait_item = if item == method { Some(item) } else { tcx.trait_item_of(item) };
    if trait_item != Some(method) {
        return None;
    }
    Some((method, args, tcx.item_name(method).as_str().to_string()))
}

// `closure_locals` is iterated only for an order-independent `all`-style check.
#[allow(rustc::potential_query_instability)]
fn derive_premise<'tcx>(
    tcx: TyCtxt<'tcx>,
    iterator: DefId,
    body: &Body<'tcx>,
    promoted: &IndexVec<Promoted, Body<'tcx>>,
    facts: &BodyFacts<'tcx>,
    closure: DefId,
) -> Option<trust_vcgen::ClosureAdapterPremise> {
    let closure_ty = tcx.type_of(closure).instantiate_identity().skip_normalization();
    let ty::Closure(_, closure_args) = closure_ty.kind() else {
        return None;
    };
    // No promoted may carry the closure: a promoted `&C` is a second channel.
    if promoted.iter().any(|promoted| body_mentions_closure(promoted, closure)) {
        return None;
    }
    // The locals whose type mentions `C`. Never the return place or an argument.
    let closure_locals: FxHashSet<Local> = body
        .local_decls
        .iter_enumerated()
        .filter(|(_, decl)| mentions_closure(decl.ty, closure))
        .map(|(local, _)| local)
        .collect();
    if closure_locals.iter().any(|local| local.as_usize() <= body.arg_count) {
        return None;
    }

    // 1. The ONE call that receives the closure VALUE (type exactly `C`).
    let mut sites = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
            continue;
        };
        for (index, arg) in args.iter().enumerate() {
            if is_closure_type(arg.node.ty(&body.local_decls, tcx), closure) {
                sites.push((bb, index));
            }
        }
    }
    let [(adapter_bb, closure_arg)] = sites[..] else {
        return None;
    };
    let adapter_loc = terminator_location(body, adapter_bb);
    let TerminatorKind::Call { func, args, destination, .. } =
        &body.basic_blocks[adapter_bb].terminator().kind
    else {
        return None;
    };
    let (_, adapter_args, adapter_name) = authenticated_iterator_method(tcx, body, iterator, func)?;
    let shape = ADAPTERS.iter().find(|shape| shape.name == adapter_name)?;
    if closure_arg != shape.closure_arg || args.len() <= shape.closure_arg {
        return None;
    }
    // `F == C`, and `C` is not ALSO some other generic argument of the call.
    if adapter_args
        .iter()
        .filter(|arg| arg.as_type().is_some_and(|ty| is_closure_type(ty, closure)))
        .count()
        != 1
    {
        return None;
    }
    // The closure's own signature has the adapter's arity.
    let arity = if shape.name == "fold" { 2 } else { 1 };
    let sig = closure_args.as_closure().sig();
    let inputs = sig.skip_binder().inputs();
    let params: Vec<Ty<'tcx>> = match inputs {
        [single] => match single.kind() {
            ty::Tuple(fields) => fields.iter().collect(),
            _ => vec![*single],
        },
        many => many.to_vec(),
    };
    if params.len() != arity {
        return None;
    }
    let item_ty = params[shape.item_param];

    // 2. The closure value: a constant `C`, or a local written once by
    //    `Aggregate(Closure(C))` and moved once into this call.
    let closure_operand = &args[shape.closure_arg].node;
    let mut admitted_locs: Vec<Location> = vec![adapter_loc];
    let mut expected_consts_at_adapter = 1; // the adapter's own `FnDef`
    let mut admitted_locals: Vec<Local> = Vec::new();
    match closure_operand {
        Operand::Constant(_) => {
            expected_consts_at_adapter += 1;
            if facts.closure_aggregates.iter().any(|(_, def)| *def == closure) {
                return None;
            }
        }
        Operand::Copy(place) | Operand::Move(place) => {
            let local = place.as_local()?;
            let uses = non_drop_uses(facts, local);
            let [(first, first_loc), (second, second_loc)] = uses[..] else {
                return None;
            };
            if !matches!(first, PlaceContext::MutatingUse(MutatingUseContext::Store))
                || !matches!(
                    second,
                    PlaceContext::NonMutatingUse(
                        NonMutatingUseContext::Move | NonMutatingUseContext::Copy
                    )
                )
                || second_loc != adapter_loc
            {
                return None;
            }
            let creations: Vec<Location> = facts
                .closure_aggregates
                .iter()
                .filter(|(_, def)| *def == closure)
                .map(|(loc, _)| *loc)
                .collect();
            if creations != [first_loc] {
                return None;
            }
            let StatementKind::Assign(assign) = &statement_at(body, first_loc)?.kind else {
                return None;
            };
            let (dest, rvalue) = &**assign;
            if dest.as_local() != Some(local)
                || !matches!(rvalue, Rvalue::Aggregate(kind, _)
                    if matches!(**kind, AggregateKind::Closure(def, _) if def == closure))
            {
                return None;
            }
            admitted_locs.push(first_loc);
            admitted_locals.push(local);
        }
        _ => return None,
    }

    // 3. The receiver.
    let receiver = whole_local(&args.first()?.node)?;
    if !matches!(args.first()?.node, Operand::Move(_)) {
        return None;
    }
    let receiver_local = if shape.by_mut_ref {
        // `_b = &mut _r; adapter(move _b, ..)`, `_b` written once, used once.
        let uses = non_drop_uses(facts, receiver);
        let [(first, borrow_loc), (second, second_loc)] = uses[..] else {
            return None;
        };
        if !matches!(first, PlaceContext::MutatingUse(MutatingUseContext::Store))
            || !matches!(second, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move))
            || second_loc != adapter_loc
        {
            return None;
        }
        let StatementKind::Assign(assign) = &statement_at(body, borrow_loc)?.kind else {
            return None;
        };
        let (dest, rvalue) = &**assign;
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed) = rvalue else {
            return None;
        };
        if dest.as_local() != Some(receiver) {
            return None;
        }
        let borrowed = borrowed.as_local()?;
        (borrowed, PlaceContext::MutatingUse(MutatingUseContext::Borrow), borrow_loc)
    } else {
        (receiver, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move), adapter_loc)
    };
    let (fact, receiver_display, item_fields) = trace_receiver(
        tcx,
        body,
        iterator,
        facts,
        receiver_local.0,
        receiver_local.1,
        receiver_local.2,
        RECEIVER_FUEL,
    )?;
    // The receiver never mentions the closure (a type-level impossibility for
    // the admitted constructors, checked anyway: the accounting below relies on it).
    if closure_locals.contains(&receiver) || closure_locals.contains(&receiver_local.0) {
        return None;
    }

    // The item parameter's type matches the fact family.
    let item_matches = |ty: Ty<'tcx>| match &fact {
        trust_vcgen::AdapterYieldFact::SliceLenEq { .. }
        | trust_vcgen::AdapterYieldFact::SliceLenIn { .. } => is_shared_slice_ref(ty),
        trust_vcgen::AdapterYieldFact::IntHalfOpen { .. } => {
            matches!(ty.kind(), ty::Int(_) | ty::Uint(_))
        }
    };
    // The value the fact is about: the item (behind one `&` for `filter`/`find`),
    // then down the `enumerate` field path, each step a tuple field.
    let project = |mut ty: Ty<'tcx>| -> Option<Ty<'tcx>> {
        for &field in &item_fields {
            let ty::Tuple(fields) = ty.kind() else { return None };
            ty = *fields.get(field)?;
        }
        Some(ty)
    };
    let item_ok = if shape.item_deref {
        matches!(item_ty.kind(), ty::Ref(_, inner, m)
            if !m.is_mut() && project(*inner).is_some_and(|t| item_matches(t)))
    } else {
        project(item_ty).is_some_and(|t| item_matches(t))
    };
    if !item_ok {
        return None;
    }

    // 4. A lazy adapter's result carries the closure: written once here, and
    //    consumed once by a core `Iterator` method — MOVED into it (`last`,
    //    `fold`, `count`), or through ONE `&mut` conduit written once and moved
    //    once into it (`any`, `all`, `find`, `position` take `&mut self`), the
    //    same shape the adapter's own receiver is admitted in (step 3). The
    //    consumer's OWN generic arguments must not mention `C`, and (if any) must
    //    name only primitives and foundational-crate types — unless every own
    //    where-clause of the consumer is an `Fn`-family or sizedness bound.
    //
    //    Trust (2026-09-29): this used to demand a by-value consumer with no
    //    generics of its own, which refused `v.windows(2).map(|w| w[1])` under
    //    `fold(0, |a, b| a ^ b)` (generic `B`, `G`) and under `any(|x| x == 0)`
    //    (`&mut self`, generic `F`) — `[slice] FAILED` in the map closure on the
    //    ordinary-Rust sweep while `.last()` proved. Neither restriction reaches
    //    `C`: the result is still moved or `&mut`-borrowed exactly once, nothing
    //    else names it, and a generic argument that does not mention `C` cannot
    //    carry it. Every way into `C` is still one of `Map`'s/`Filter`'s own
    //    methods, which apply it only to items of the inner iterator.
    let mut expected_consts_at_consumer = None;
    if shape.lazy {
        let adapter_result = destination.as_local()?;
        if !closure_locals.contains(&adapter_result) {
            return declined("lazy result is not closure-typed");
        }
        let uses = non_drop_uses(facts, adapter_result);
        let [(first, first_loc), (second, second_loc)] = uses[..] else {
            return declined("lazy result is not used exactly twice");
        };
        if !matches!(first, PlaceContext::MutatingUse(MutatingUseContext::Call))
            || first_loc != adapter_loc
        {
            return declined("lazy result's first use is not the adapter call");
        }
        let (consumer_loc, consumer_receiver) = match second {
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                (second_loc, adapter_result)
            }
            PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                let StatementKind::Assign(assign) = &statement_at(body, second_loc)?.kind else {
                    return declined("conduit is not a statement");
                };
                let (dest, rvalue) = &**assign;
                if !matches!(rvalue, Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                    if borrowed.as_local() == Some(adapter_result))
                {
                    return declined("conduit is not a `&mut` of the result");
                }
                let conduit = dest.as_local()?;
                let conduit_uses = non_drop_uses(facts, conduit);
                let [(store, store_loc), (moved, moved_loc)] = conduit_uses[..] else {
                    return declined("conduit is not stored once and moved once");
                };
                if !matches!(store, PlaceContext::MutatingUse(MutatingUseContext::Store))
                    || store_loc != second_loc
                    || !matches!(moved, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move))
                {
                    return declined("conduit store/move shape");
                }
                admitted_locs.push(second_loc);
                admitted_locals.push(conduit);
                (moved_loc, conduit)
            }
            _ => return None,
        };
        let TerminatorKind::Call { func: consumer_func, args: consumer_args, .. } =
            call_at(body, consumer_loc)?
        else {
            return declined("consumer is not a call");
        };
        if whole_local(&consumer_args.first()?.node) != Some(consumer_receiver)
            || !matches!(consumer_args.first()?.node, Operand::Move(_))
        {
            return declined("consumer receiver is not the result moved");
        }
        let (consumer, consumer_generic_args, _) =
            authenticated_iterator_method(tcx, body, iterator, consumer_func)?;
        let generics = tcx.generics_of(consumer);
        let own_from = generics.parent_count;
        if consumer_generic_args
            .iter()
            .skip(own_from)
            .any(|arg| arg.as_type().is_none_or(|ty| mentions_closure(ty, closure)))
        {
            return declined("consumer generic argument mentions the closure");
        }
        // Trust (2026-10-04): `(0..3).map(|i| ..).sum::<f64>()` (a3d_solve
        // `dot_min_over_box`). A consumer with generics of its own was refused
        // outright. Its trait dispatch (`S: Sum<Self::Item>`, `B: FromIterator<..>`)
        // is selected on its OWN generic arguments AND on the adapter's item type,
        // so the consumer is admitted only when BOTH name nothing but primitives,
        // foundational-crate types and foundational-crate fn items (a callable
        // argument such as `f64::min`). Then coherence leaves only a foundational impl
        // (`<f64 as Sum<f64>>::sum`), which drives the adapter only through
        // `Iterator` methods, and those call the closure only on items the inner
        // iterator yields. A local item type would admit an orphan-legal user
        // `impl Sum<Local> for f64` that receives the adapter VALUE as a generic `I`
        // and can forge one (`transmute_copy` of a never-yielded `Range`) or
        // specialize on it — a false premise found by the 2026-10-04 review.
        //
        // Trust (merge 2026-10-14): the 2026-09-29 relaxation above (own arguments
        // need only not mention `C`) admitted exactly that forge (`sum::<f64>` over a
        // local item, and `sum::<Total>` with a user `impl Sum<f64> for Total`), so
        // the foundational test applies to it too. It is waived ONLY for a consumer
        // whose own where-clauses are all `Fn`/`FnMut`/`FnOnce` (with their
        // `Output` projections) or sizedness bounds — `fold`, `any`, `all`, `find`,
        // `position`: the only impl such a consumer selects on a local argument is
        // that argument's own call impl (a closure body or fn item), which receives
        // the accumulator and items, never the adapter value. Any other bound
        // (`Sum`, `Product`, `FromIterator`, `Try`, `DoubleEndedIterator`, ...)
        // keeps the foundational test.
        //
        // Trust (2026-10-15): core's `fold` is now `where Self: Sized + [const] Destruct,
        // F: [const] FnMut(B, Self::Item) -> B + [const] Destruct`, so its clauses carry two
        // `Destruct` bounds, and the waiver refused `fold` for them: `map(..).fold(..)`'s
        // closure lost its premise and was refuted (measured on the stage 1 of the
        // 2026-10-14 merge, `tests/ui/trust/adapter_yield/lazy_adapter_consumers.rs#on`).
        // `Destruct` is a builtin marker no crate may implement (`#[rustc_deny_explicit_impl]`;
        // "non-const bounds will always hold for every type"), so it selects no impl and
        // hands the adapter value to nothing; a `HostEffect` clause is the `[const]`
        // condition of such a bound, which constrains only a const evaluation. Both join
        // the sizedness and `Fn`-family bounds; every other bound keeps the foundational test.
        let only_callable_bounds = || {
            tcx.clauses_of(consumer).clauses.iter().all(|(clause, _)| {
                match clause.kind().skip_binder() {
                    ty::ClauseKind::Trait(pred) => {
                        tcx.is_sizedness_trait(pred.def_id())
                            || tcx.fn_trait_kind_from_def_id(pred.def_id()).is_some()
                            || tcx.is_lang_item(
                                pred.def_id(),
                                rustc_attr_ir::lang_items::LangItem::Destruct,
                            )
                    }
                    ty::ClauseKind::Projection(proj) => tcx.is_lang_item(
                        proj.def_id(),
                        rustc_attr_ir::lang_items::LangItem::FnOnceOutput,
                    ),
                    ty::ClauseKind::HostEffect(_) => true,
                    _ => false,
                }
            })
        };
        if generics.own_requires_monomorphization() && !only_callable_bounds() {
            let adapter_item = if shape.name == "map" {
                closure_args.as_closure().sig().skip_binder().output()
            } else {
                item_ty
            };
            if !generic_arg_is_foundational(tcx, adapter_item.into())
                || consumer_generic_args
                    .iter()
                    .skip(generics.parent_count)
                    .any(|arg| !generic_arg_is_foundational(tcx, arg))
            {
                if env_flag_enabled("TRUST_ADAPTER_YIELD_TRACE") {
                    for (clause, _) in tcx.clauses_of(consumer).clauses {
                        eprintln!("TRUST_ADAPTER_YIELD_TRACE: consumer clause: {clause:?}");
                    }
                }
                return declined(
                    "consumer is generic over non-foundational arguments and not only `Fn`-bound",
                );
            }
        }
        admitted_locs.push(consumer_loc);
        admitted_locals.push(adapter_result);
        expected_consts_at_consumer = Some(consumer_loc);
    } else if destination.as_local().is_none_or(|local| closure_locals.contains(&local)) {
        return declined("strict adapter destination");
    }

    // 5. THE ACCOUNTING: every mention of `C` is one of the admitted ones.
    //    Constants: the adapter's `FnDef` (+ the closure constant), the
    //    consumer's `FnDef`, nothing else anywhere.
    let mut consts_at_adapter = 0usize;
    let mut consts_at_consumer = 0usize;
    for (loc, ty) in &facts.consts {
        if !mentions_closure(*ty, closure) {
            continue;
        }
        if *loc == adapter_loc {
            consts_at_adapter += 1;
        } else if Some(*loc) == expected_consts_at_consumer {
            consts_at_consumer += 1;
        } else {
            return declined("closure constant outside the adapter/consumer");
        }
    }
    if consts_at_adapter != expected_consts_at_adapter
        || consts_at_consumer != usize::from(expected_consts_at_consumer.is_some())
    {
        return declined("closure constant count mismatch");
    }
    //    Located types: only at the admitted locations.
    if facts
        .located_tys
        .iter()
        .any(|(loc, ty)| mentions_closure(*ty, closure) && !admitted_locs.contains(loc))
    {
        return declined("closure-typed located type outside the admitted locations");
    }
    //    Locals: the admitted ones (whose uses were pinned above) and no other
    //    closure-typed local with any use at all.
    for local in &closure_locals {
        if admitted_locals.contains(local) {
            continue;
        }
        if !non_drop_uses(facts, *local).is_empty() {
            return declined("another closure-typed local is used");
        }
    }

    Some(trust_vcgen::ClosureAdapterPremise {
        // `_1` is the environment; the closure's parameters follow from `_2`.
        item_local: shape.item_param + 2,
        item_deref: shape.item_deref,
        item_fields,
        fact,
        adapter: format!("Iterator::{}", shape.name),
        receiver: receiver_display,
    })
}

/// Whether `arg` names only primitives and types and fn items defined in an authentic
/// foundational crate: no local ADT or fn item, closure, coroutine, `dyn`, alias,
/// parameter or unevaluated constant anywhere inside it.
/// Trust (2026-10-15): a premise declined in the lazy-consumer gate or the accounting
/// step, named under `TRUST_ADAPTER_YIELD_TRACE` (diagnostics only; the answer is the
/// same `None` either way).
fn declined<T>(why: &str) -> Option<T> {
    if env_flag_enabled("TRUST_ADAPTER_YIELD_TRACE") {
        eprintln!("TRUST_ADAPTER_YIELD_TRACE: declined: {why}");
    }
    None
}

fn generic_arg_is_foundational<'tcx>(tcx: TyCtxt<'tcx>, arg: ty::GenericArg<'tcx>) -> bool {
    arg.walk().all(|inner| match inner.kind() {
        ty::GenericArgKind::Lifetime(_) => true,
        ty::GenericArgKind::Const(c) => !c.has_param() && !c.has_aliases(),
        ty::GenericArgKind::Type(ty) => match ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Tuple(_)
            | ty::Array(..)
            | ty::Slice(_)
            | ty::Ref(..)
            | ty::RawPtr(..) => true,
            ty::Adt(adt, _) => crate_is_authentic_foundational(tcx, adt.did().krate),
            // A fn ITEM defined in a foundational crate (`fold(f64::INFINITY,
            // f64::min)`, a3d_solve `cylindricity_cert`); its own generic arguments
            // are visited by this same walk.
            ty::FnDef(def, _) => crate_is_authentic_foundational(tcx, def.krate),
            _ => false,
        },
    })
}

/// Trace an iterator receiver `local` to its admitted constructor. `local` must
/// be written exactly once (by the constructor) and used exactly once more — the
/// `(use_context, use_loc)` the caller already accounted for.
#[allow(clippy::too_many_arguments)]
fn trace_receiver<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    iterator: DefId,
    facts: &BodyFacts<'tcx>,
    local: Local,
    use_context: PlaceContext,
    use_loc: Location,
    fuel: u32,
) -> Option<(trust_vcgen::AdapterYieldFact, String, Vec<usize>)> {
    if fuel == 0 || local.as_usize() <= body.arg_count {
        return None;
    }
    let uses = non_drop_uses(facts, local);
    let [(def_context, def_loc), (second, second_loc)] = uses[..] else {
        return None;
    };
    if second != use_context || second_loc != use_loc {
        return None;
    }
    let typing_env = body.typing_env(tcx);
    match def_context {
        // A `Range { start, end }` aggregate with constant integer bounds.
        PlaceContext::MutatingUse(MutatingUseContext::Store) => {
            let StatementKind::Assign(assign) = &statement_at(body, def_loc)?.kind else {
                return None;
            };
            let (dest, rvalue) = &**assign;
            if dest.as_local() != Some(local) {
                return None;
            }
            let Rvalue::Aggregate(kind, ops) = rvalue else {
                return None;
            };
            let AggregateKind::Adt(adt, _, adt_args, _, None) = **kind else {
                return None;
            };
            if Some(adt) != tcx.lang_items().range_struct() || ops.len() != 2 {
                return None;
            }
            let element = adt_args.type_at(0);
            let signed = match element.kind() {
                ty::Int(_) => true,
                ty::Uint(_) => false,
                _ => return None,
            };
            let bound = |operand: &Operand<'tcx>| -> Option<i128> {
                let Operand::Constant(constant) = operand else {
                    return None;
                };
                if constant.const_.ty() != element {
                    return None;
                }
                let scalar = constant.const_.try_eval_scalar_int(tcx, typing_env)?;
                // At the scalar's OWN size: `to_i128`/`to_u128` assert a 16-byte
                // scalar and ICE on a `usize`/`u64` bound.
                let size = scalar.size();
                if signed {
                    Some(scalar.to_int(size))
                } else {
                    i128::try_from(scalar.to_uint(size)).ok()
                }
            };
            let mut ops = ops.iter();
            let start = bound(ops.next()?)?;
            let end = bound(ops.next()?)?;
            Some((
                trust_vcgen::AdapterYieldFact::IntHalfOpen { start, end },
                format!("{start}..{end}"),
                Vec::new(),
            ))
        }
        PlaceContext::MutatingUse(MutatingUseContext::Call) => {
            let TerminatorKind::Call { func, args, destination, .. } = call_at(body, def_loc)?
            else {
                return None;
            };
            if destination.as_local() != Some(local) {
                return None;
            }
            let (callee, _) = func.const_fn_def()?;
            // A core adapter that hands on only items of its inner iterator,
            // unchanged: `rev` / `step_by` (over any admitted receiver), and
            // `filter` / `skip` / `take` (Trust, 2026-10-08). Each yields a
            // sub-sequence of the inner items in some order; `filter`'s predicate
            // sees an item only behind `&`, and an admitted item is an integer or a
            // `&[T]`, neither of which it can change. `enumerate` yields
            // `(count, item)` for each inner item, so the fact moves to field 1.
            if tcx.trait_of_assoc(callee) == Some(iterator) {
                let (_, _, name) = authenticated_iterator_method(tcx, body, iterator, func)?;
                if !matches!(
                    name.as_str(),
                    "rev" | "step_by" | "filter" | "skip" | "take" | "enumerate"
                ) {
                    return None;
                }
                let inner_operand = &args.first()?.node;
                if !matches!(inner_operand, Operand::Move(_)) {
                    return None;
                }
                let inner = whole_local(inner_operand)?;
                let (fact, display, mut path) = trace_receiver(
                    tcx,
                    body,
                    iterator,
                    facts,
                    inner,
                    PlaceContext::NonMutatingUse(NonMutatingUseContext::Move),
                    def_loc,
                    fuel - 1,
                )?;
                // `enumerate` yields `(index, item)`: the inner item is field 1.
                if name == "enumerate" {
                    path.insert(0, 1);
                }
                return Some((fact, format!("({display}).{name}(..)"), path));
            }
            // `<[T]>::windows` / `chunks_exact` / `chunks` (a constant size gives the exact
            // length, a non-constant one `[1, usize::MAX]`):
            // an INHERENT method of the primitive slice type, which only the
            // foundational crates can define.
            let impl_def = tcx.inherent_impl_of_assoc(callee)?;
            if !crate_is_authentic_foundational(tcx, callee.krate)
                || !matches!(
                    tcx.type_of(impl_def).instantiate_identity().skip_normalization().kind(),
                    ty::Slice(_)
                )
                || args.len() != 2
            {
                return None;
            }
            let name = tcx.item_name(callee);
            if !matches!(name.as_str(), "windows" | "chunks_exact" | "chunks") {
                return None;
            }
            let Operand::Constant(size) = &args[1].node else {
                // Trust (2026-10-08): a size that is not a constant. All three
                // constructors panic on a zero size, a panic charged at the
                // constructor call, so every item they yield is a non-empty
                // sub-slice: length in `[1, usize::MAX]`.
                if args[1].node.ty(&body.local_decls, tcx) != tcx.types.usize {
                    return None;
                }
                let max = tcx.data_layout.pointer_size().unsigned_int_max();
                return Some((
                    trust_vcgen::AdapterYieldFact::SliceLenIn {
                        min: 1,
                        max: u64::try_from(max).ok()?,
                    },
                    format!("<[T]>::{name}(_)"),
                    Vec::new(),
                ));
            };
            if size.const_.ty() != tcx.types.usize {
                return None;
            }
            let k = size.const_.try_eval_target_usize(tcx, typing_env)?;
            if k == 0 {
                return None;
            }
            match name.as_str() {
                "windows" | "chunks_exact" => Some((
                    trust_vcgen::AdapterYieldFact::SliceLenEq { len: k },
                    format!("<[T]>::{name}({k})"),
                    Vec::new(),
                )),
                "chunks" => Some((
                    trust_vcgen::AdapterYieldFact::SliceLenIn { min: 1, max: k },
                    format!("<[T]>::chunks({k})"),
                    Vec::new(),
                )),
                _ => None,
            }
        }
        _ => None,
    }
}
