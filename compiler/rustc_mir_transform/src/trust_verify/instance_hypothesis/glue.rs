//! Trust (OD-1, 2026-10-06, "vtable-only discharge"; docs/DECISION_QUEUE.md "OD-1"
//! item 19): instances created through a VTABLE or DROP GLUE.
//!
//! Phase 1 minted a discharge row for every concrete instance a walked body NAMES (a
//! call or a fn-item value). An instance of a hypothesis-carrying generic that no body
//! names — one reached only through the vtable an unsizing coercion to `dyn` builds
//! (`&W(Bad) as &dyn Run` creates `<W<Bad> as Run>::run`), or through the drop glue
//! of a value (`drop(W(Bad))` runs `<W<Bad> as Drop>::drop`) — was charged nothing:
//! the carrier's per-site hypothesis was never discharged at that instance. Not a
//! false proof (strict is CONDITIONAL on the carrier's rows, certify refuses them),
//! but a disclosure gap.
//!
//! This module closes it for every vtable and drop glue a LOCAL body builds:
//!
//! * the walked body's own CONCRETE `Drop` and `UnsizeCast` mentions (read off
//!   `Body::mentioned_items`, the set the codegen mono collector reads, recorded
//!   before optimization so an inlined-away drop or coercion still counts);
//! * the still-generic ones of every LOCAL generic body (and local closure or
//!   coroutine) an instance is discharged through, instantiated at that instance
//!   ([`discharge_glue_of_instance`], called at the end of every
//!   `discharge_instance`), following still-generic calls into local generics that
//!   carry no hypothesis themselves, so a vtable built two generic calls down is
//!   reached too;
//! * a value of a concrete type handed to a DEPENDENCY generic, which may drop it
//!   (`mem::drop(w)`, `Option::take`): the type's drop glue is charged at the call
//!   (an over-approximation: a callee that never drops it is charged as if it did).
//!
//! Each concrete vtable contributes its method entries (`tcx.vtable_entries`, the
//! collector's source) and its drop entry; each drop glue contributes the destructor
//! (`Drop::drop`, resolved) of every ADT the walk of the type reaches — fields, enum
//! variants, element types, closure and coroutine captures, the pointee of a raw
//! pointer (an owning pointer's contents), and every generic type argument of an ADT
//! (so `Vec<W<Bad>>` reaches `W<Bad>` behind its raw buffer); a shared or mutable
//! reference is not followed (it owns nothing). A reached instance that is a carrier
//! is discharged exactly as a named one (`discharge_instance`); a local generic body
//! that carries nothing is walked for its own glue.
//!
//! Fail-closed choices, each one row and each an error on every fail-closed lane:
//! * a glue the walk cannot model (an unsizing shape it does not know, a type that
//!   is not concrete after normalization, a walk past [`GLUE_TYPE_NODE_CAP`] types or
//!   [`GLUE_DEPTH_CAP`] bodies) is an `unknown` row naming it;
//! * a reached local generic body whose `optimized_mir` is not complete and cannot be
//!   demanded without risking an E0391 cycle (on the query stack, in a mutual-recursion
//!   SCC, or reaching either through its direct local calls) is an `unknown` row
//!   ("verified after this body"), because whether it carries a hypothesis is not known
//!   yet; when it can be demanded, it is (its verification fills the ledger first).
//!
//! Not covered (still disclosed by the crate's inventory-incomplete row): a vtable a
//! DEPENDENCY's generic code builds from a type this crate hands it
//! (`Box::<dyn Error>::from(e)`), and a vtable or drop glue a dependency generic builds
//! at an instance created inside another dependency.

use std::rc::Rc;

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{Body, MentionedItem};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, GenericArgs, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use trust_types::{Outcome, TransportObligationResult};

use super::{Carriers, discharge_instance, discharge_row, with_ledger};

/// How many distinct types that need dropping one glue walk may visit ([`drop_reach`]).
/// Past it the glue is an `unknown` row: the walk stops, it never answers "nothing
/// reached". A type that needs no drop runs no destructor and is not visited, so the
/// cap counts only types whose glue runs code (measured: a 4225-element tuple of
/// distinct `Drop`-carrying structs, `tests/ui/trust/thread-spawn-census/
/// drop_free_types_not_refused.rs`, visits about 4300).
const GLUE_TYPE_NODE_CAP: usize = 1 << 16;

/// How deep one drop-glue walk may nest ([`drop_reach`]), a backstop: polymorphic
/// recursion (`struct P<T> { next: Option<Box<P<(T, T)>>> }`, whose walk would build ever
/// larger types; measured as a hang in
/// `tests/ui/trust/thread-spawn-census/polymorphic_recursion_is_unknown.rs`) is stopped
/// earlier, by [`GLUE_GROWTH_CAP`]. Past either cap the glue is an `unknown` row.
const GLUE_TYPE_DEPTH_CAP: u32 = 256;

/// How many times one drop-glue walk may meet the same ADT at strictly growing
/// arguments on one path ([`grows`]) before it stops with an `unknown` row. Real
/// polymorphic recursion (`P<T>` holding `P<(T, T)>`) grows without end and reaches
/// it; a finite nesting that grows fewer times is walked to its end.
const GLUE_GROWTH_CAP: usize = 8;

/// How deep the walk through local generic bodies may go ([`discharge_glue_of_instance`]).
/// Every (body, instance) is walked once per compilation, so the cap only stops
/// polymorphic recursion; past it the instance is an `unknown` row.
const GLUE_DEPTH_CAP: u32 = 32;

/// How many local bodies the "may this body be demanded" question may visit
/// ([`demand_callee_first`]); past it the answer is "no" (an `unknown` row).
const DEMAND_REACH_CAP: usize = 256;

/// The discharge-key block of a walked (body, instance): no MIR body has this many
/// blocks (see `OPAQUE_SITE_BLOCK`).
const GLUE_WALK_BLOCK: u32 = u32::MAX - 2;

/// The discharge-key block of a reached local generic that is not verified yet.
const GLUE_PENDING_BLOCK: u32 = u32::MAX - 3;

/// A mention that builds a vtable or runs drop glue.
#[derive(Clone, Copy, Debug)]
pub(super) enum Glue<'tcx> {
    /// A `Drop` terminator of a place of this type (after drop elaboration).
    Drop(Ty<'tcx>),
    /// An unsizing coercion `source` -> `target` (the mono collector's `UnsizeCast`).
    Unsize { source: Ty<'tcx>, target: Ty<'tcx> },
}

impl<'tcx> Glue<'tcx> {
    pub(super) fn has_non_region_param(self) -> bool {
        match self {
            Glue::Drop(ty) => ty.has_non_region_param(),
            Glue::Unsize { source, target } => {
                source.has_non_region_param() || target.has_non_region_param()
            }
        }
    }

    fn text(self) -> String {
        match self {
            Glue::Drop(ty) => format!("the drop glue of `{ty}`"),
            Glue::Unsize { source, target } => {
                format!("the unsizing coercion `{source}` -> `{target}`")
            }
        }
    }

    /// `self` at the concrete `args` of the body it was read from, normalized.
    fn instantiate(self, tcx: TyCtxt<'tcx>, args: GenericArgs<'tcx>) -> Option<Self> {
        let at = |ty: Ty<'tcx>| {
            tcx.try_instantiate_and_normalize_erasing_regions(
                args,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(tcx, ty),
            )
            .ok()
        };
        Some(match self {
            Glue::Drop(ty) => Glue::Drop(at(ty)?),
            Glue::Unsize { source, target } => {
                Glue::Unsize { source: at(source)?, target: at(target)? }
            }
        })
    }

    /// `self` (already free of parameters) normalized.
    fn normalized(self, tcx: TyCtxt<'tcx>) -> Option<Self> {
        self.instantiate(tcx, ty::GenericArgs::empty())
    }
}

/// What one body mentions, as the mono collector reads it.
pub(super) struct Mentions<'tcx> {
    pub(super) glue: Vec<(Glue<'tcx>, Span)>,
    /// Fn items (a call's callee or a value) and closures turned into fn pointers.
    pub(super) items: Vec<(DefId, GenericArgs<'tcx>, Span)>,
}

/// `body`'s mentioned items: the recorded set when the pipeline recorded one (always,
/// for an `optimized_mir`), else the same enumeration over `body` itself.
pub(super) fn mentions<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Mentions<'tcx> {
    let mut out = Mentions { glue: Vec::new(), items: Vec::new() };
    let mut take = |item: MentionedItem<'tcx>, span: Span| match item {
        MentionedItem::Fn(ty) => {
            if let ty::FnDef(def, args) = *ty.kind() {
                out.items.push((def, args.skip_binder(), span));
            }
        }
        MentionedItem::Closure(ty) => {
            if let ty::Closure(def, args) = *ty.kind() {
                out.items.push((def, args, span));
            }
        }
        MentionedItem::Drop(ty) => out.glue.push((Glue::Drop(ty), span)),
        MentionedItem::UnsizeCast { source_ty, target_ty } => {
            out.glue.push((Glue::Unsize { source: source_ty, target: target_ty }, span))
        }
    };
    match &body.mentioned_items {
        Some(recorded) => {
            for spanned in recorded {
                take(spanned.node, spanned.span);
            }
        }
        None => crate::mentioned_items::for_each_mentioned_item(tcx, body, |item, span, _| {
            take(item, span)
        }),
    }
    out
}

/// One instance a glue reaches: the item and its arguments, and how it was reached.
struct Reached<'tcx> {
    item: DefId,
    args: GenericArgs<'tcx>,
    how: String,
}

/// Every instance the concrete `glue` creates: vtable method entries and destructors,
/// plus the local closure and coroutine bodies whose own glue runs with it. `Err`
/// names what the walk could not model.
fn glue_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    glue: Glue<'tcx>,
    reached: &mut Vec<Reached<'tcx>>,
) -> Result<(), String> {
    match glue {
        Glue::Drop(ty) => drop_reach(tcx, ty, reached),
        Glue::Unsize { source, target } => {
            let mut tails = Vec::new();
            unsize_tails(tcx, source, target, 0, &mut tails)?;
            for (concrete, dyn_ty) in tails {
                vtable_reach(tcx, concrete, dyn_ty, reached);
                // The vtable's drop entry is `concrete`'s drop glue.
                drop_reach(tcx, concrete, reached)?;
            }
            Ok(())
        }
    }
}

/// The (concrete pointee, `dyn` type) pairs of a concrete unsizing coercion whose
/// target tail is a trait object built from a type that is not one (a `dyn` -> `dyn`
/// upcast reuses a vtable built elsewhere; a slice or `str` tail has none).
///
/// Trust (2026-10-10): shared with the CALL-REACH-1 call walk
/// (`sysroot_drop_reach::walk_built_dispatch`, D2), which walks these vtables.
pub(in crate::trust_verify) fn unsize_tails<'tcx>(
    tcx: TyCtxt<'tcx>,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
    depth: u32,
    out: &mut Vec<(Ty<'tcx>, Ty<'tcx>)>,
) -> Result<(), String> {
    let unmodelled =
        || format!("an unsizing coercion `{source}` -> `{target}` this walk does not model");
    if depth > 16 {
        return Err(unmodelled());
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let tails = |source_pointee: Ty<'tcx>, target_pointee: Ty<'tcx>| {
        let (from, to) =
            tcx.struct_lockstep_tails_for_codegen(source_pointee, target_pointee, typing_env);
        (matches!(to.kind(), ty::Dynamic(..)) && !matches!(from.kind(), ty::Dynamic(..)))
            .then_some((from, to))
    };
    match (source.kind(), target.kind()) {
        (&ty::Pat(source, _), &ty::Pat(target, _)) => {
            return unsize_tails(tcx, source, target, depth + 1, out);
        }
        (
            &ty::Ref(_, source_pointee, _),
            &ty::Ref(_, target_pointee, _) | &ty::RawPtr(target_pointee, _),
        )
        | (&ty::RawPtr(source_pointee, _), &ty::RawPtr(target_pointee, _)) => {
            out.extend(tails(source_pointee, target_pointee))
        }
        _ if let Some(source_boxed) = source.boxed_ty()
            && let Some(target_boxed) = target.boxed_ty() =>
        {
            out.extend(tails(source_boxed, target_boxed))
        }
        // A `CoerceUnsized` struct (`Rc`, `Arc`, `Pin`, `NonNull`, a user smart
        // pointer): every field whose type the coercion changes is walked; the one
        // that carries the pointer finds the tail, a `PhantomData` finds none.
        (&ty::Adt(source_adt, source_args), &ty::Adt(target_adt, target_args))
            if source_adt == target_adt && source_adt.is_struct() =>
        {
            for field in &source_adt.non_enum_variant().fields {
                let normalize = |ty: ty::Unnormalized<'tcx, Ty<'tcx>>| {
                    tcx.try_normalize_erasing_regions(typing_env, ty).map_err(|_| unmodelled())
                };
                let from = normalize(field.ty(tcx, source_args))?;
                let to = normalize(field.ty(tcx, target_args))?;
                if from != to {
                    unsize_tails(tcx, from, to, depth + 1, out)?;
                }
            }
        }
        // A struct holding no pointer (`PhantomData<A>` -> `PhantomData<B>`) builds
        // nothing; anything else is a shape this walk does not know.
        (&ty::Adt(source_adt, _), &ty::Adt(target_adt, _))
            if source_adt == target_adt && source_adt.all_fields().next().is_none() => {}
        _ => return Err(unmodelled()),
    }
    Ok(())
}

/// The method entries of the vtable of `concrete` as the trait object `dyn_ty`
/// (supertrait methods included), each with the local closure or coroutine bodies
/// its arguments name (a closure's `call` entry may be a shim around its body).
fn vtable_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    concrete: Ty<'tcx>,
    dyn_ty: Ty<'tcx>,
    reached: &mut Vec<Reached<'tcx>>,
) {
    let ty::Dynamic(predicates, ..) = *dyn_ty.kind() else { return };
    let Some(principal) = predicates.principal() else { return };
    let trait_ref =
        tcx.instantiate_bound_regions_with_erased(principal.with_self_ty(tcx, concrete));
    let how = format!("the vtable of `{concrete}` as `{dyn_ty}`");
    for entry in tcx.vtable_entries(trait_ref) {
        let ty::VtblEntry::Method(instance) = *entry else { continue };
        if let ty::InstanceKind::Item(item) = instance.def {
            reached.push(Reached { item, args: instance.args, how: how.clone() });
        }
        local_bodies_in_args(instance.args, &how, reached);
    }
}

/// The local closure and coroutine types `args` names, as bodies to walk.
fn local_bodies_in_args<'tcx>(
    args: GenericArgs<'tcx>,
    how: &str,
    reached: &mut Vec<Reached<'tcx>>,
) {
    for ty in args.types().flat_map(|ty| ty.walk()).filter_map(|arg| arg.as_type()) {
        if let ty::Closure(def, body_args) | ty::Coroutine(def, body_args) = *ty.kind()
            && def.is_local()
        {
            reached.push(Reached { item: def, args: body_args, how: how.to_string() });
        }
    }
}

/// The destructors the drop glue of the concrete `ty` may run, and the local
/// coroutine bodies whose saved state it drops (see the module doc for the walk).
fn drop_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    reached: &mut Vec<Reached<'tcx>>,
) -> Result<(), String> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let drop_fn = tcx
        .lang_items()
        .drop_trait()
        .and_then(|drop_trait| tcx.associated_item_def_ids(drop_trait).first().copied());
    let how = format!("the drop glue of `{ty}`");
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    // Each entry carries the ADTs on its path from `ty`, to recognise polymorphic
    // recursion (below).
    let mut stack: Vec<(Ty<'tcx>, u32, Rc<Vec<Ty<'tcx>>>)> = vec![(ty, 0, Rc::new(Vec::new()))];
    while let Some((current, depth, path)) = stack.pop() {
        // A type that needs no drop runs no destructor (`ManuallyDrop<T>`,
        // `PhantomData<T>`, `[u8; N]`): nothing below it is reached.
        if !seen.insert(current) || !current.needs_drop(tcx, typing_env) {
            continue;
        }
        if depth > GLUE_TYPE_DEPTH_CAP {
            return Err(format!(
                "the drop glue of `{ty}` nests deeper than {GLUE_TYPE_DEPTH_CAP} types"
            ));
        }
        if seen.len() > GLUE_TYPE_NODE_CAP {
            return Err(format!(
                "the drop glue of `{ty}` reaches more than {GLUE_TYPE_NODE_CAP} types"
            ));
        }
        let normalize = |field: ty::Unnormalized<'tcx, Ty<'tcx>>| {
            tcx.try_normalize_erasing_regions(typing_env, field)
                .map_err(|_| format!("a field of `{current}` (in `{ty}`) does not normalize"))
        };
        let mut children: Vec<Ty<'tcx>> = Vec::new();
        let mut child_path = Rc::clone(&path);
        match *current.kind() {
            ty::Adt(adt, args) => {
                // Polymorphic recursion: the same ADT again at arguments that strictly
                // GROW its ancestor's (`P<T>` holding `P<(T, T)>`; [`grows`]). Its drop
                // glue may be infinite, so this walk would not end. It is never skipped
                // (a growth that a projection ends — `S<T>` holding
                // `S<<T as Step>::Next>` — is finite, and its destructors run): the walk
                // goes on through at most [`GLUE_GROWTH_CAP`] growing repeats of one
                // ADT, and past that the glue is not established (an `unknown` row).
                let growths = path
                    .iter()
                    .filter(|&&ancestor| {
                        matches!(*ancestor.kind(), ty::Adt(other, ancestor_args)
                            if other == adt && grows(ancestor_args, args))
                    })
                    .count();
                if growths > GLUE_GROWTH_CAP {
                    return Err(format!(
                        "the drop glue of `{ty}` recurses polymorphically: `{current}` repeats an \
                         enclosing type at growing arguments more than {GLUE_GROWTH_CAP} times"
                    ));
                }
                if adt.has_dtor(tcx) {
                    let resolved = drop_fn.map(|drop_fn| {
                        ty::Instance::try_resolve(
                            tcx,
                            typing_env,
                            drop_fn,
                            tcx.mk_args(&[current.into()]),
                        )
                    });
                    match resolved {
                        Some(Ok(Some(ty::Instance {
                            def: ty::InstanceKind::Item(item),
                            args,
                        }))) => reached.push(Reached { item, args, how: how.clone() }),
                        _ => {
                            return Err(format!(
                                "the destructor of `{current}` (in `{ty}`) does not resolve"
                            ));
                        }
                    }
                }
                for field in adt.all_fields() {
                    children.push(normalize(field.ty(tcx, args))?);
                }
                children.extend(args.types());
                let mut extended = (*path).clone();
                extended.push(current);
                child_path = Rc::new(extended);
            }
            ty::Tuple(elements) => children.extend(elements.iter()),
            ty::Array(element, _) | ty::Slice(element) | ty::Pat(element, _) => {
                children.push(element)
            }
            // An owning pointer (`Unique`, `NonNull`) bottoms out in a raw pointer: its
            // pointee may be dropped through it.
            ty::RawPtr(pointee, _) => children.push(pointee),
            ty::Closure(_, args) => children.extend(args.as_closure().upvar_tys()),
            ty::CoroutineClosure(_, args) => {
                children.extend(args.as_coroutine_closure().upvar_tys())
            }
            ty::Coroutine(def, args) => {
                children.extend(args.as_coroutine().upvar_tys());
                if def.is_local() {
                    // Its saved locals are dropped by its own glue: walk its body.
                    reached.push(Reached { item: def, args, how: how.clone() });
                } else {
                    children.extend(args.types());
                }
            }
            ty::CoroutineWitness(def, args) => {
                if def.is_local() {
                    reached.push(Reached { item: def, args, how: how.clone() });
                } else {
                    children.extend(args.types());
                }
            }
            // Nothing owned: a reference, a trait object (its vtable's drop entry was
            // charged where the vtable was built), scalars and fn types.
            ty::Ref(..)
            | ty::Dynamic(..)
            | ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Foreign(_)
            | ty::FnDef(..)
            | ty::FnPtr(..) => {}
            ty::UnsafeBinder(_)
            | ty::Alias(..)
            | ty::Param(_)
            | ty::Bound(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => {
                return Err(format!("a part `{current}` of `{ty}` is not a concrete type"));
            }
        }
        stack.extend(children.into_iter().map(|child| (child, depth + 1, Rc::clone(&child_path))));
    }
    Ok(())
}

/// Whether `args` strictly grow `ancestor_args`, position by position, as the
/// arguments of one ADT: every lifetime is ignored, every const is equal, every type
/// is equal or holds the ancestor's type as a proper part, and at least one type is
/// not equal. (`S<0>` holding `S<1>` does not grow: it reaches `S<1>` once and then
/// `seen` ends the walk.)
fn grows<'tcx>(ancestor_args: GenericArgs<'tcx>, args: GenericArgs<'tcx>) -> bool {
    if ancestor_args.len() != args.len() {
        return false;
    }
    let mut strictly = false;
    for (ancestor, own) in ancestor_args.iter().zip(args.iter()) {
        match (ancestor.kind(), own.kind()) {
            (ty::GenericArgKind::Lifetime(_), ty::GenericArgKind::Lifetime(_)) => {}
            (ty::GenericArgKind::Const(a), ty::GenericArgKind::Const(b)) if a == b => {}
            (ty::GenericArgKind::Type(a), ty::GenericArgKind::Type(b)) => {
                if a != b {
                    if !b.walk().skip(1).any(|part| part.as_type() == Some(a)) {
                        return false;
                    }
                    strictly = true;
                }
            }
            _ => return false,
        }
    }
    strictly
}

/// Charge every instance the concrete `glue` (mentioned at `mention`) creates.
pub(super) fn discharge_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    glue: Glue<'tcx>,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    // Every type this module renders into row text is printed with full paths:
    // trimmed paths would demand a diagnostic (`must_produce_diag`), and a row is
    // not one.
    let Some(glue) = glue.normalized(tcx) else {
        rows.push(with_no_trimmed_paths!(unestablished_glue_row(
            tcx,
            glue,
            mention,
            "it does not normalize"
        )));
        return;
    };
    let mut reached = Vec::new();
    if let Err(why) = with_no_trimmed_paths!(glue_reach(tcx, glue, &mut reached)) {
        rows.push(with_no_trimmed_paths!(unestablished_glue_row(tcx, glue, mention, &why)));
        return;
    }
    for Reached { item, args, how } in reached {
        discharge_reached(tcx, root, item, args, &how, mention, depth, rows);
    }
}

/// The drop glue of every concrete type argument of a DEPENDENCY generic instance
/// `def::<args>` named at `mention`: the callee may drop a value of that type.
pub(super) fn discharge_dependency_call_drops<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    args: GenericArgs<'tcx>,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    for ty in args.types() {
        discharge_glue(tcx, root, Glue::Drop(ty), mention, depth, rows);
    }
}

fn unestablished_glue_row(
    tcx: TyCtxt<'_>,
    glue: Glue<'_>,
    mention: Span,
    why: &str,
) -> TransportObligationResult {
    let at = super::super::source_span_from_rustc_span(tcx, mention);
    discharge_row(
        format!(
            "instance discharge: the instances created by {} (at {}:{}) are not enumerated",
            glue.text(),
            at.file,
            at.line_start
        ),
        Some(at),
        Outcome::Unknown,
        format!(
            "not established: {why}; an instance this glue creates may carry an instance \
             hypothesis that is then never charged, so the glue is not established (an error on \
             every fail-closed lane)"
        ),
    )
}

/// One instance a glue reached: a carrier is discharged, a local generic body that
/// carries nothing is walked for its own glue, a local generic not verified yet is
/// verified first when that is safe and an `unknown` row when it is not.
pub(super) fn discharge_reached<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    item: DefId,
    args: GenericArgs<'tcx>,
    how: &str,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    let before = rows.len();
    if item.is_local() {
        // A body with no parameters of its own (a non-generic impl's method, a closure
        // or coroutine of a non-generic fn) carries no hypothesis and its glue is
        // concrete: its own verification charges it.
        if !has_instances(tcx, item) {
            return;
        }
        let known = Carriers::snapshot(tcx.sess).contains(tcx, item)
            || super::super::optimized_mir_if_completed(tcx, item).is_some();
        if !known {
            // Verifying it records its sites in the ledger (`TrustVerify` is the last
            // pass of its `optimized_mir`); its local callees are verified first.
            if item == root || !demand_callee_first(tcx, item) {
                pending_row(tcx, item, args, how, mention, rows);
                return;
            }
        }
        discharge_instance(tcx, root, item, args, mention, depth + 1, rows);
    } else if Carriers::snapshot(tcx.sess).contains(tcx, item) {
        discharge_instance(tcx, root, item, args, mention, depth + 1, rows);
    }
    for row in &mut rows[before..] {
        row.description.push_str(&format!(" [an instance created by {how}]"));
    }
}

/// Whether the local body `def` is generic, so that its glue can differ per instance.
/// A closure or coroutine is asked through its enclosing item (its own synthetic
/// arguments are no type parameters a caller chooses).
fn has_instances(tcx: TyCtxt<'_>, def: DefId) -> bool {
    tcx.generics_of(tcx.typeck_root_def_id(def)).requires_monomorphization(tcx)
}

/// The `unknown` row of a reached local generic that is not verified yet and cannot be
/// verified from here, once per interned instance.
fn pending_row<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: DefId,
    args: GenericArgs<'tcx>,
    how: &str,
    mention: Span,
    rows: &mut Vec<TransportObligationResult>,
) {
    let key = (item, GLUE_PENDING_BLOCK, args.as_ptr() as usize);
    if !with_ledger(tcx.sess, |ledger| ledger.published_discharges.insert(key)) {
        return;
    }
    let instance_text = trust_mir_extract::safe_def_path_str_with_args(tcx, item, args);
    let at = super::super::source_span_from_rustc_span(tcx, mention);
    rows.push(discharge_row(
        format!(
            "instance discharge: `{instance_text}` (an instance created by {how} at {}:{}) is a \
             generic body not verified yet",
            at.file, at.line_start
        ),
        Some(at),
        Outcome::Unknown,
        "not established: the generic body is verified after this one (a vtable or drop glue is \
         no call edge of the callee-first order) and its optimized MIR cannot be demanded here \
         without risking an E0391 query cycle, so whether it carries instance hypotheses is \
         unknown here; the instance is not established (an error on every fail-closed lane)"
            .to_string(),
    ));
}

/// Demand `tcx.optimized_mir(item)` (its verification, which fills the ledger) from
/// inside the running verification, CALLEE-FIRST, and answer whether it did. Nothing
/// is demanded unless the cycle oracle declines neither `item` nor any local body it
/// reaches through its direct local calls (the MIR inliner may demand those), within
/// [`DEMAND_REACH_CAP`] bodies. That set is then a DAG (a mutual-recursion SCC member
/// is declined), and its bodies are demanded in post-order, so every local callee of
/// `item` is verified (its `Via` records and sites in the ledger) before `item` is:
/// the order the crate-wide `trust_callee_first_demand_order` walk gives. Demanding
/// `item` alone would verify it before a callee declared after it, and refuse it for
/// the callee's missing record (OD-1 item 19 review, `vtable_carrier_declared_late`).
fn demand_callee_first(tcx: TyCtxt<'_>, item: DefId) -> bool {
    let Some(local) = item.as_local() else { return false };
    if !tcx.is_mir_available(item) {
        return false;
    }
    let mir_keys = tcx.mir_keys(());
    let mut seen = FxHashSet::default();
    let mut post_order = Vec::new();
    // (body, its callees are already on the stack)
    let mut stack = vec![(local, false)];
    while let Some((node, expanded)) = stack.pop() {
        if expanded {
            post_order.push(node);
            continue;
        }
        if !seen.insert(node) {
            continue;
        }
        if seen.len() > DEMAND_REACH_CAP
            || super::super::optimized_mir_query_would_cycle(tcx, node.to_def_id())
        {
            return false;
        }
        // A body outside the call graph's node set has no cached adjacency; its
        // elaborated MIR may already be stolen, so it is not read: not safe.
        if !mir_keys.contains(&node) || !super::super::trust_mir_call_graph_node_eligible(tcx, node)
        {
            return false;
        }
        stack.push((node, true));
        for &callee in tcx.trust_mir_direct_local_callees(node).iter().rev() {
            if !seen.contains(&callee) {
                stack.push((callee, false));
            }
        }
    }
    for node in post_order {
        if super::super::optimized_mir_if_completed(tcx, node.to_def_id()).is_none() {
            let _ = tcx.optimized_mir(node);
        }
    }
    true
}

/// Trust (OD-1 item 19): at the end of every `discharge_instance` of a LOCAL generic
/// body `def` at the concrete `args`, charge the vtables and drop glue its body builds
/// at parameter-mentioning types, instantiated at `args`, and walk on into the local
/// generic bodies (and closures) it calls at still-generic arguments. A carrier it
/// mentions is discharged at its instance too: a `Via` record covers only a CALL of
/// it, and a carrier reified into a fn pointer (a closure or a fn item value) has
/// none (OD-1-T6-CALLABLE review); a site a `Via` record already charged is not
/// published twice. Once per (body, interned instance) in the compilation.
pub(super) fn discharge_glue_of_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    def: DefId,
    args: GenericArgs<'tcx>,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    if !def.is_local()
        || def == root
        || !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
        || !has_instances(tcx, def)
        || args.has_non_region_param()
    {
        return;
    }
    let key = (def, GLUE_WALK_BLOCK, args.as_ptr() as usize);
    if !with_ledger(tcx.sess, |ledger| ledger.published_discharges.insert(key)) {
        return;
    }
    let instance_text = trust_mir_extract::safe_def_path_str_with_args(tcx, def, args);
    let unestablished = |why: &str| {
        let at = super::super::source_span_from_rustc_span(tcx, mention);
        discharge_row(
            format!(
                "instance discharge: the vtables and drop glue of `{instance_text}` (reached \
                 from {}:{}) are not enumerated",
                at.file, at.line_start
            ),
            Some(at),
            Outcome::Unknown,
            format!(
                "not established: {why}; an instance its vtables or drop glue create may carry \
                 an instance hypothesis that is then never charged (an error on every \
                 fail-closed lane)"
            ),
        )
    };
    if depth >= GLUE_DEPTH_CAP {
        rows.push(unestablished("the walk through generic bodies exceeds its depth cap"));
        return;
    }
    let body = match super::super::optimized_mir_if_completed(tcx, def) {
        Some(body) => body,
        // Demanded callee-first; `def` itself is then a completed query.
        None if demand_callee_first(tcx, def) => tcx.optimized_mir(def),
        // A generic of a mutual-recursion cycle that is not verified yet already has
        // its `unknown` row at every path that reaches it (`unverified_cycle_generic_row`
        // for a mention, the late-cycle reader for a sibling call, `SiteReadback::Cycle`
        // for a carrier): the instance is not established either way.
        None if super::is_local_cycle_generic(tcx, def) => return,
        None => {
            rows.push(unestablished(
                "its optimized MIR is not computed yet and cannot be demanded here without \
                 risking an E0391 query cycle",
            ));
            return;
        }
    };
    let mentioned = mentions(tcx, body);
    for (glue, _) in mentioned.glue {
        if !glue.has_non_region_param() {
            continue;
        }
        match glue.instantiate(tcx, args) {
            Some(glue) => discharge_glue(tcx, root, glue, mention, depth + 1, rows),
            None => rows.push(unestablished(&with_no_trimmed_paths!(format!(
                "{} does not instantiate at this instance",
                glue.text()
            )))),
        }
    }
    let carriers = Carriers::snapshot(tcx.sess);
    let mono_env = ty::TypingEnv::fully_monomorphized();
    for (callee, callee_args, _) in mentioned.items {
        if !callee_args.has_non_region_param() {
            continue;
        }
        let Ok(substituted) = tcx.try_instantiate_and_normalize_erasing_regions(
            args,
            mono_env,
            ty::EarlyBinder::bind(tcx, callee_args),
        ) else {
            rows.push(unestablished("a still-generic call does not instantiate at this instance"));
            continue;
        };
        let resolved = if tcx.is_closure_like(callee) {
            Some((callee, substituted))
        } else {
            match ty::Instance::try_resolve(tcx, mono_env, callee, substituted) {
                Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) => {
                    Some((item, args))
                }
                _ => None,
            }
        };
        let mut nested = Vec::new();
        local_bodies_in_args(substituted, "a closure handed on", &mut nested);
        if let Some((item, item_args)) = resolved {
            if item.is_local() {
                // A sibling generic of a mutual-recursion cycle that is not verified yet
                // is the late-cycle reader's: `def` is in its cycle (a callee outside it
                // completes first), and that reader publishes its `unknown` row.
                let pending_cycle_sibling = super::is_local_cycle_generic(tcx, item)
                    && super::super::optimized_mir_if_completed(tcx, item).is_none();
                if item != def && !pending_cycle_sibling {
                    if carriers.contains(tcx, item) || tcx.is_closure_like(item) {
                        // Trust (OD-1-T6-CALLABLE review, 2026-10-11): a carrier was
                        // skipped here because "a carrier's calls are its `Via`
                        // records". A `Via` record is minted for a CALL terminator
                        // only: a carrier REIFIED into a fn pointer — a closure
                        // (`MentionedItem::Closure`, `PointerCoercion::ClosureFnPointer`,
                        // `fn f<T>() -> fn(u32) -> u32 { |x| T::go(x) }`) or a fn item
                        // value (`c::<T>` returned as `fn(u32) -> u32`) — has none, so
                        // its sites were never charged at this instance (a silent
                        // omission). Every mention of a carrier is discharged here;
                        // one a `Via` record already discharged at this instance is
                        // deduplicated by `published_discharges` (keyed per site and
                        // interned instance). A closure not verified yet is verified
                        // first or gets an `unknown` row (`discharge_reached`).
                        discharge_reached(
                            tcx,
                            root,
                            item,
                            item_args,
                            "a still-generic mention (a call, or a value reified into a fn \
                             pointer)",
                            mention,
                            depth,
                            rows,
                        );
                    } else {
                        discharge_instance(tcx, root, item, item_args, mention, depth + 1, rows);
                    }
                }
            } else {
                discharge_dependency_call_drops(tcx, root, item_args, mention, depth + 1, rows);
            }
        }
        // Trust (OD-1 item 20, T6, 2026-10-10): a closure handed on may carry admitted
        // sites of its own (`instance_hypothesis::is_plain_closure_of_fn`), recorded
        // only once it is verified. Discharging it here before then read no records
        // and published nothing for its sites at this instance, silently. Routed
        // through `discharge_reached`: a closure not verified yet is verified first
        // (callee-first) when that is safe, and is an `unknown` row when it is not.
        for Reached { item, args, how } in nested {
            if item != def {
                discharge_reached(tcx, root, item, args, &how, mention, depth, rows);
            }
        }
    }
}
