//! Trust (2026-10-06, OD-1 item 14 amendment "DYN-RECEIVER-ROOT"; docs/DECISION_QUEUE.md
//! "OD-1-RG-CONCRETE"): which of a body's ARGUMENTS a virtual call's receiver was read
//! out of.
//!
//! OD-1 item 14 (`04c39335f3`) refutes a virtual call on an open, exported trait as
//! class (c) of "L0 refutation rows" when the trait object is the caller's choice: a
//! downstream `impl Tr for W { fn m(&self) -> u32 { panic!() } }` handed in makes
//! "panic-free for every value of that argument" constructively false. Its receiver
//! walk accepted only an argument read through DEREFERENCES (`&dyn Tr`, `&&dyn Tr`, a
//! reborrow). Every other way the caller hands the body its trait object kept the
//! row `runtime_checked`, so `--allow-l0-gaps` conditional-passed exactly the hole
//! item 14 closed (measured on stage 1 `c797f90c1` and on the fix branch's stage 1,
//! review of rg concrete-misclassified, 2026-10-05):
//!
//! ```text
//! pub fn a_box(env: Box<dyn Env>) -> u32 { env.arity() }          // Box deref: a Transmute of its NonNull
//! pub fn b_field(h: &Holder<'_>) -> u32 { h.env.arity() }          // a field
//! pub fn d_slice(v: &[&dyn Env]) -> u32 { v[0].arity() }           // an index
//! pub fn e_option(o: Option<&dyn Env>) -> u32 { match o { Some(e) => e.arity(), None => 0 } }
//! pub fn f_arc(e: Arc<dyn Env>) -> u32 { e.arity() }               // `Deref::deref`
//! pub fn c_vec(v: &Vec<Box<dyn Env>>) -> u32 { v[0].arity() }      // `Index::index`
//! pub fn h_iter(v: &[Box<dyn Env>]) -> u32 { for e in v { e.arity(); } 0 } // into_iter + next
//! ```
//!
//! ## The rule ([`argument_root`])
//!
//! A place is ARGUMENT-ROOTED when its local is one of the body's arguments, or a
//! non-argument local with exactly ONE definition (a whole-local assignment or call
//! destination; any partial write, second definition or other rvalue declines) whose
//! source is argument-rooted, at most [`HOPS`] definitions deep. Its projections may
//! be any READ of the value: `Deref`, `Field`, `Downcast`, `Index`, `ConstantIndex`,
//! `Subslice`, `OpaqueCast`, `UnwrapUnsafeBinder` — each reads part of what the
//! caller handed in. A definition's source is:
//!
//! * a copy, move, `CopyForDeref`, `&place` or `&raw place`;
//! * a `Transmute` / `PtrToPtr` cast whose TARGET's trait objects all occur in the
//!   SOURCE's type (the `Box<dyn Tr>` deref lowers to a transmute of its
//!   `NonNull<dyn Tr>`). An UNSIZING coercion (`&B as &dyn Tr`) is never a source:
//!   its vtable is the body's choice of `B`, not the caller's;
//! * the receiver of a call that RESOLVES (`Instance::try_resolve`, `Ok(Some(Item))`)
//!   to a `core` / `alloc` / `std` implementation of `Deref::deref`,
//!   `DerefMut::deref_mut`, `Index::index`, `IndexMut::index_mut`,
//!   `IntoIterator::into_iter` or `Iterator::next` — each returns (a view of) part of
//!   its receiver. A user `impl Deref` can return anything and is never a source.
//!
//! In a CLOSURE-LIKE body (closure, coroutine) the walk is item 14's original one
//! (dereferences and single-assignment copies only): a closure's environment is
//! built by the body that creates it, which may capture a trait object it built
//! itself, so a field of `_1` there is not, by itself, the caller's choice.
//!
//! ## Closure captures of the parent's parameter (CLOSURE-CAPTURE-ROOT)
//!
//! Trust (2026-10-11, docs/DECISION_QUEUE.md "CLOSURE-CAPTURE-ROOT"): one field of a
//! closure's environment IS the caller's choice — a capture of the enclosing
//! function's own PARAMETER. `pub fn f(p: &dyn Fn(u32) -> bool) { .. |n| p(n) .. }`
//! read `runtime_checked` while its `impl Fn` twin refuted (measured, a3d-wire
//! `sock::stale_instance_files`), so `--allow-l0-gaps` conditional-passed the dyn
//! spelling. [`closure_capture_root`] follows such a field back: the body is a plain
//! CLOSURE (not a coroutine), the place is `_1` [`Deref`] `.Field(k)` followed by
//! `Deref` (through a SHARED reference only) and `Field` reads, and
//! `closure_captures[k]` is an upvar whose captured HIR place is an IMMUTABLE simple
//! binding of a parameter of the typeck-root body, projected only by `Field` and
//! shared-reference `Deref`. A single-definition local of the closure body read
//! through `Field` (a truncated capture: `_3 = copy *_2; (*_3).env`) is followed the
//! same way, through shared-reference dereferences only, and only to that answer.
//! Everything else declines: a capture of a `let` local
//! (the `closure_upvar` control — the parent may have built that trait object), a
//! `mut` parameter or a deref through `&mut`/`Box`/a raw pointer (the parent may have
//! overwritten it before building the closure), a parameter of an intermediate
//! closure, any coroutine or async body. The answer is
//! [`ReceiverRoot::ParentArg`]; whether that parameter is the CALLER's choice is the
//! same rule a fn argument gets (`virtual_receiver_is_callers_choice`, including
//! DYN-ARG-PROVENANCE-1's private-fn exemption).
//!
//! ## Soundness direction
//!
//! This only ever ADDS refutations (a row moves from the disclosed `runtime_checked`
//! label to `failed`); it never removes one item 14 made: every place the old walk
//! accepted, this one accepts (a deref-only place, a single copy/move/reborrow
//! definition, four hops ⊂ [`HOPS`]). Every decline is still the `runtime_checked`
//! label, which strict and certify refuse anyway. Whether the trait object is
//! adversarial at all (open, exported principal) stays `virtual_dispatch_is_adversarial`.

use rustc_hir::{self as hir, BindingMode, ByRef, Mutability};
use rustc_middle::hir::place::{PlaceBase as HirPlaceBase, ProjectionKind as HirProjectionKind};
use rustc_middle::mir::{
    Body, CastKind, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::sym;
use rustc_span::symbol::kw;

/// Maximum definition chain the walk follows. The for-loop shape
/// (`next(&mut iter)` → `iter = into_iter(arg)` → the Box transmute → the receiver
/// reborrow) needs eight; item 14's original walk used four.
pub(super) const HOPS: u32 = 16;

/// Where a receiver was read from: one of the body's own arguments, or — in a closure
/// body — a capture of the typeck-root function's parameter `param` (0-based, the
/// HIR parameter index = MIR argument `param + 1`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ReceiverRoot {
    Arg(Local),
    ParentArg { fn_def: DefId, param: usize },
}

/// Which of `body`'s arguments (or, in a closure, which of its parent's parameters)
/// was `operand` read out of (see the module doc)? `None` on every uncertainty.
pub(super) fn argument_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<ReceiverRoot> {
    let closure_like = tcx.is_closure_like(body.source.def_id());
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_root(tcx, body, place, HOPS, closure_like)
        }
        _ => None,
    }
}

fn place_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    hops: u32,
    closure_like: bool,
) -> Option<ReceiverRoot> {
    // Trust (2026-10-11, CLOSURE-CAPTURE-ROOT): a closure's capture of its parent's
    // parameter (see the module doc).
    if closure_like && let Some(root) = closure_capture_root(tcx, body, place) {
        return Some(root);
    }
    let local = place.local;
    let is_arg = (1..=body.arg_count).contains(&local.as_usize());
    // Trust (2026-10-11, CLOSURE-CAPTURE-ROOT): in a closure, a `Field` read of a
    // NON-argument local is followed only toward a capture of the parent's parameter
    // (a truncated capture `h` read as `(*_3).env` after `_3 = copy *_2`, `_2 = copy
    // (*_1).0`), through shared-reference dereferences only; any other answer
    // declines below, as before.
    let capture_fields = closure_like
        && !is_arg
        && place.projection.iter().any(|elem| matches!(elem, ProjectionElem::Field(..)));
    let reads_only = place.projection.iter().enumerate().all(|(index, elem)| match elem {
        ProjectionElem::Deref | ProjectionElem::PhantomDeref => {
            !capture_fields || derefs_shared(tcx, body, place, index)
        }
        ProjectionElem::Field(..) => !closure_like || capture_fields,
        ProjectionElem::Downcast(..)
        | ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. }
        | ProjectionElem::OpaqueCast(_)
        | ProjectionElem::UnwrapUnsafeBinder(_) => !closure_like,
    });
    if !reads_only {
        return None;
    }
    if is_arg {
        return Some(ReceiverRoot::Arg(local));
    }
    if hops == 0 {
        return None;
    }
    let mut source: Option<Place<'tcx>> = None;
    let mut definitions = 0usize;
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign(boxed) = &stmt.kind else { continue };
            let (dest, rvalue) = &**boxed;
            if dest.local != local {
                continue;
            }
            definitions += 1;
            source = if dest.projection.is_empty() {
                rvalue_source(tcx, body, rvalue, closure_like)
            } else {
                None
            };
        }
        if let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind
            && destination.local == local
        {
            definitions += 1;
            source = if destination.projection.is_empty() && !closure_like {
                receiver_view_call_source(tcx, body, func, args.first().map(|a| &a.node))
            } else {
                None
            };
        }
    }
    if definitions != 1 {
        return None;
    }
    source
        .and_then(|from| place_root(tcx, body, &from, hops - 1, closure_like))
        .filter(|root| !capture_fields || matches!(root, ReceiverRoot::ParentArg { .. }))
}

/// Is the `index`-th projection of `place` (a `Deref`) a dereference of a SHARED
/// reference? A `&mut`, `Box` or raw pointer is a place the parent could have written.
fn derefs_shared<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    index: usize,
) -> bool {
    let base = Place::ty_from(place.local, &place.projection[..index], body, tcx).ty;
    matches!(base.kind(), ty::Ref(_, _, Mutability::Not))
}

fn rvalue_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
    closure_like: bool,
) -> Option<Place<'tcx>> {
    match rvalue {
        Rvalue::Ref(_, _, from) | Rvalue::CopyForDeref(from) => Some(*from),
        Rvalue::Use(Operand::Copy(from) | Operand::Move(from), _) => Some(*from),
        Rvalue::RawPtr(_, from) if !closure_like => Some(*from),
        Rvalue::Cast(
            // Trust (1.101): `ElaborateBoxDerefs` spells its temporary with the
            // dedicated `BoxDerefTransmute` of the box's `BoxRaw` field where
            // 1.99 spelled a `Transmute` of the `NonNull` two fields down; the
            // chase through it is the same read of the box's own pointer.
            CastKind::Transmute | CastKind::PtrToPtr | CastKind::BoxDerefTransmute,
            op @ (Operand::Copy(from) | Operand::Move(from)),
            target,
        ) if !closure_like && cast_keeps_trait_objects(op.ty(body, tcx), *target) => Some(*from),
        _ => None,
    }
}

/// Trust (2026-10-11, CLOSURE-CAPTURE-ROOT): is `place`, in a plain CLOSURE body, a
/// read of a capture of the typeck-root function's immutable parameter? `None` on
/// every uncertainty (see the module doc).
fn closure_capture_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<ReceiverRoot> {
    // The closure environment is MIR argument 1.
    if place.local.as_usize() != 1 || body.arg_count < 1 {
        return None;
    }
    let closure_def = body.source.def_id().as_local()?;
    let env_ty = body.local_decls[place.local].ty;
    let (closure_ty, env_by_ref) = match *env_ty.kind() {
        ty::Ref(_, inner, _) => (inner, true),
        _ => (env_ty, false),
    };
    // A plain closure only: a coroutine's (async block's) environment and its
    // `Pin<&mut _>` resume argument keep item 14's original walk.
    if !matches!(closure_ty.kind(), ty::Closure(..)) {
        return None;
    }
    let mut elems = place.projection.iter().enumerate();
    if env_by_ref && !matches!(elems.next(), Some((_, ProjectionElem::Deref))) {
        return None;
    }
    let Some((_, ProjectionElem::Field(upvar, _))) = elems.next() else { return None };
    // After the upvar: reads only, every dereference through a SHARED reference (a
    // `&mut`, `Box` or raw pointer is a place the parent could have written).
    for (index, elem) in elems {
        match elem {
            ProjectionElem::Field(..) => {}
            ProjectionElem::Deref => {
                if !derefs_shared(tcx, body, place, index) {
                    return None;
                }
            }
            _ => return None,
        }
    }
    let captured = tcx.closure_captures(closure_def).get(upvar.as_usize())?;
    let HirPlaceBase::Upvar(upvar_id) = captured.place.base else { return None };
    for (index, projection) in captured.place.projections.iter().enumerate() {
        match projection.kind {
            HirProjectionKind::Field(..) => {}
            HirProjectionKind::Deref => {
                let base = captured.place.ty_before_projection(index);
                if !matches!(base.kind(), ty::Ref(_, _, Mutability::Not)) {
                    return None;
                }
            }
            _ => return None,
        }
    }
    let var = upvar_id.var_path.hir_id;
    let root = tcx.typeck_root_def_id_local(closure_def);
    let root_body = tcx.hir_maybe_body_owned_by(root)?;
    let param = root_body.params.iter().position(|param| {
        param.pat.hir_id == var
            && matches!(
                param.pat.kind,
                hir::PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), _, _, None)
            )
    })?;
    Some(ReceiverRoot::ParentArg { fn_def: root.to_def_id(), param })
}

/// Every trait object `target` mentions also occurs in `source` (and there is one):
/// the cast re-types a pointer the caller supplied, it does not pick a vtable.
fn cast_keeps_trait_objects<'tcx>(source: Ty<'tcx>, target: Ty<'tcx>) -> bool {
    let dyns = |ty: Ty<'tcx>| {
        ty.walk()
            .filter_map(|arg| arg.as_type())
            .filter(|t| matches!(t.kind(), ty::Dynamic(..)))
            .collect::<Vec<_>>()
    };
    let in_target = dyns(target);
    let in_source = dyns(source);
    !in_target.is_empty() && in_target.iter().all(|t| in_source.contains(t))
}

/// The receiver place of a call that returns a view of its receiver: a `core` /
/// `alloc` / `std` implementation of one of the six receiver-view methods.
fn receiver_view_call_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    receiver: Option<&Operand<'tcx>>,
) -> Option<Place<'tcx>> {
    let (callee, gen_args) = func.const_fn_def()?;
    let trait_def = tcx.trait_of_assoc(callee)?;
    let name = tcx.item_name(callee);
    let lang = tcx.lang_items();
    let is_view = (Some(trait_def) == lang.deref_trait() && name == kw::Deref)
        || (Some(trait_def) == lang.deref_mut_trait() && name == sym::deref_mut)
        || (Some(trait_def) == lang.index_trait() && name == sym::index)
        || (Some(trait_def) == lang.index_mut_trait() && name == sym::index_mut)
        || (tcx.is_diagnostic_item(sym::IntoIterator, trait_def) && name == sym::into_iter)
        || (tcx.is_diagnostic_item(sym::Iterator, trait_def) && name == sym::next);
    if !is_view {
        return None;
    }
    let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), .. })) =
        ty::Instance::try_resolve(tcx, body.typing_env(tcx), callee, gen_args)
    else {
        return None;
    };
    let krate = tcx.crate_name(item.krate);
    if !(krate == sym::core || krate == sym::alloc || krate == sym::std) {
        return None;
    }
    match receiver? {
        Operand::Copy(place) | Operand::Move(place) => Some(*place),
        _ => None,
    }
}
