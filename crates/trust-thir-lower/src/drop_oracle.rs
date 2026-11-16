//! Trust (step 2 increment 4b, 2026-10-01): THE DROP ORACLE — rustc's own drop elaboration,
//! read from the built MIR, as a TEST ORACLE for the producer's drops (R-2: MIR is an oracle,
//! never a production input; this reads it and feeds nothing).
//!
//! Design: `docs/design/2026-09-29-step2-inc4-drops.md` §3.5 ("same places dropped at the same
//! points"). The effect-conservation gate (`effect_conservation.rs`) compares the drops the
//! producer claims (`drops::DropClaim`) with these, per body, and refuses the body for codegen
//! and strict on any difference (D18 OD-1: every drop checked as an event against MIR).
//!
//! # What it computes
//!
//! For every `Drop` terminator of the built body that is reachable from the entry along REAL
//! edges and whose place needs drop, the style rustc's `ElaborateDrops` pass will give it —
//! `Dead` (removed), `Static`, `Conditional` (behind a drop flag) or `Open` (expanded per field)
//! — computed exactly as that pass does (`rustc_mir_transform::elaborate_drops`):
//!
//! * the move data (`MoveData::gather_moves`) over the places whose type needs drop;
//! * `MaybeInitializedPlaces` (`exclude_inactive_in_otherwise`) and
//!   `MaybeUninitializedPlaces` (`mark_inactive_variants_as_uninit`), iterated to a
//!   fixpoint;
//! * `drop_style` in `Deep` mode over all children of the dropped path;
//! * a drop of a place with no exact move path (a drop-and-replace behind a pointer) stays an
//!   unconditional drop (`elaborate_drops`'s `LookupResult::Parent` arm);
//! * an `Open` drop (some children moved) is expanded the way `open_drop_for_adt` expands a
//!   struct, tuple or closure: each field with a move path by its own style, each field without
//!   one (never moved) under the parent's shallow style when its type needs drop. An open drop
//!   whose expansion drops nothing (`Pair::cut`'s `drop(self.held)` leaving only drop-free
//!   fields) is DEAD; one that drops something stays `Open` (the producer never claims one).
//!   Any other open place — an enum's variants, a box's contents, an array — is kept `Open`
//!   (live) without expansion, conservatively.
//!
//! It runs on a CLONE of the built body with the two rewrites the passes between `mir_built`
//! and `ElaborateDrops` make that change which states reach a drop: imaginary edges removed
//! (`CleanupPostBorrowck` turns `FalseEdge` / `FalseUnwind` into `Goto` of the real target) and
//! the return edge of a call into an uninhabited type removed (`LintAndRemoveUninhabited`). The
//! unwind refinements (`skipping_unreachable_unwind`) touch cleanup blocks only, and the oracle
//! reports normal-path drops only.
//!
//! # What it does not see
//!
//! A body that mentions an unrevealed opaque type (`needs_drop` and the move data would demand
//! the opaque's hidden type, a cycle through this body's own borrowck) and a coroutine body:
//! for both the oracle answers `None`, and the gate refuses any producer drop in such a body.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use rustc_middle::mir::{self, BasicBlock, Body, Local, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_mir_dataflow::impls::{MaybeInitializedPlaces, MaybeUninitializedPlaces};
use rustc_mir_dataflow::move_paths::{LookupResult, MoveData, MovePathIndex};
use rustc_mir_dataflow::{Analysis, move_path_children_matching, on_all_children_bits};
use rustc_span::Span;

use crate::drops::{DropIdentity, LiveStyle};

/// One `Drop` terminator, as rustc's elaboration will treat it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleDrop {
    pub block: BasicBlock,
    pub identity: DropIdentity,
    /// The dropped place's type, `type_id_hash`ed.
    pub ty: u128,
    pub span: Span,
    /// `None`: dead (elaboration removes it).
    pub style: Option<LiveStyle>,
    /// The place has a projection (a drop-and-replace of a sub-place).
    pub projected: bool,
}

/// The identity of a MIR local in the producer's terms: an argument by position, a user
/// binding by its `ItemLocalId`, anything else `Other`.
fn identity_of(body: &Body<'_>, local: Local) -> DropIdentity {
    if local.as_usize() >= 1 && local.as_usize() <= body.arg_count {
        return DropIdentity::Param((local.as_usize() - 1) as u32);
    }
    match body.local_decls[local].local_info.as_ref() {
        mir::ClearCrossCrate::Set(info) => match &**info {
            mir::LocalInfo::User(mir::BindingForm::Var(v)) => {
                DropIdentity::Var(v.binding_hir_local_id.as_u32())
            }
            _ => DropIdentity::Other,
        },
        mir::ClearCrossCrate::Clear => DropIdentity::Other,
    }
}

/// The built body as `ElaborateDrops` sees it, for the purposes of init/uninit at a drop.
fn cleaned<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Body<'tcx> {
    let mut b = body.clone();
    let parent_module = body.source.def_id().as_local().map(|d| tcx.parent_module_from_def_id(d));
    let typing_env = body.typing_env(tcx);
    for data in b.basic_blocks.as_mut().iter_mut() {
        let Some(term) = data.terminator.as_mut() else { continue };
        match &mut term.kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                let target = *real_target;
                term.kind = TerminatorKind::Goto { target, loop_hint_attrs: Default::default() };
            }
            TerminatorKind::Call { target, destination, .. } if target.is_some() => {
                let ty = destination.ty(&body.local_decls, tcx).ty;
                // `LintAndRemoveUninhabited`'s rule, asked only of a type the producer's reveal
                // funnel would lay out (the body has no opaque type, see `elaborated_drops`, but
                // a free alias can still expand to one). Otherwise the edge is kept: more code
                // reads as reachable, which only reports more drops (refuses more).
                if let Some(m) = parent_module {
                    if crate::layout_query_is_reentrant_safe_deep(tcx, ty)
                        && !ty.is_inhabited_from(tcx, m, typing_env)
                    {
                        *target = None;
                    }
                }
            }
            _ => {}
        }
    }
    b
}

/// Blocks reachable from the entry along normal (non-cleanup) edges.
fn reachable(body: &Body<'_>) -> Vec<bool> {
    let mut seen = vec![false; body.basic_blocks.len()];
    let mut stack = vec![mir::START_BLOCK];
    while let Some(bb) = stack.pop() {
        if body.basic_blocks[bb].is_cleanup || std::mem::replace(&mut seen[bb.as_usize()], true) {
            continue;
        }
        if let Some(t) = &body.basic_blocks[bb].terminator {
            for s in t.successors() {
                if !body.basic_blocks[s].is_cleanup {
                    stack.push(s);
                }
            }
        }
    }
    seen
}

/// `(maybe_init, maybe_uninit)` over `path` and all its children (`drop_style`'s `Deep` mode),
/// and how many paths that was.
fn deep_state(
    move_data: &MoveData<'_>,
    path: MovePathIndex,
    is_init: &dyn Fn(MovePathIndex) -> bool,
    is_uninit: &dyn Fn(MovePathIndex) -> bool,
) -> (bool, bool, usize) {
    let (mut some_init, mut some_uninit, mut children) = (false, false, 0usize);
    on_all_children_bits(move_data, path, |child| {
        some_init |= is_init(child);
        some_uninit |= is_uninit(child);
        children += 1;
    });
    (some_init, some_uninit, children)
}

/// Does an OPEN drop of `path` (of type `ty`) drop anything? See the module doc.
fn open_drop_is_live<'tcx>(
    tcx: TyCtxt<'tcx>,
    needs_drop: &dyn Fn(ty::Ty<'tcx>) -> bool,
    move_data: &MoveData<'tcx>,
    path: MovePathIndex,
    ty: ty::Ty<'tcx>,
    is_init: &dyn Fn(MovePathIndex) -> bool,
    is_uninit: &dyn Fn(MovePathIndex) -> bool,
    depth: usize,
) -> bool {
    if depth > 16 {
        return true;
    }
    let fields: Vec<ty::Ty<'tcx>> = match ty.kind() {
        ty::Adt(adt, args) if adt.is_struct() && !adt.is_box() && adt.destructor(tcx).is_none() => {
            adt.non_enum_variant()
                .fields
                .iter()
                .map(|f| f.ty(tcx, *args).skip_normalization())
                .collect()
        }
        ty::Tuple(tys) => tys.iter().collect(),
        ty::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
        _ => return true,
    };
    let parent_init = is_init(path);
    for (i, fty) in fields.into_iter().enumerate() {
        let child = move_path_children_matching(
            move_data,
            path,
            |elem| matches!(elem, mir::ProjectionElem::Field(f, _) if f.as_usize() == i),
        );
        match child {
            Some(c) => {
                let (init, uninit, n) = deep_state(move_data, c, is_init, is_uninit);
                match (init, uninit, n != 1) {
                    (false, _, _) => {}
                    (true, true, true) => {
                        if open_drop_is_live(
                            tcx,
                            needs_drop,
                            move_data,
                            c,
                            fty,
                            is_init,
                            is_uninit,
                            depth + 1,
                        ) {
                            return true;
                        }
                    }
                    _ => return true,
                }
            }
            None => {
                if parent_init && needs_drop(fty) {
                    return true;
                }
            }
        }
    }
    false
}

/// Every reachable normal-path `Drop` of a needs-drop place in `body` (the built MIR), with its
/// elaborated style. `None` when the oracle cannot run on this body (see the module doc).
pub fn elaborated_drops<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<Vec<OracleDrop>> {
    if body.has_opaque_types() || body.coroutine.is_some() {
        return None;
    }
    // A body with no `Drop` terminator has no drop to report; skip the move data and the two
    // fixpoints (this runs for every body the census sees).
    if !body.basic_blocks.iter().any(|bb| {
        bb.terminator.as_ref().is_some_and(|t| matches!(t.kind, TerminatorKind::Drop { .. }))
    }) {
        return Some(Vec::new());
    }
    let typing_env = body.typing_env(tcx);
    let body = cleaned(tcx, body);
    let needs_drop = |t: ty::Ty<'tcx>| crate::cycle_safe_needs_drop(tcx, typing_env, t);
    let move_data = MoveData::gather_moves(&body, tcx, needs_drop);
    let mut inits = MaybeInitializedPlaces::new(tcx, &body, &move_data)
        .exclude_inactive_in_otherwise()
        .iterate_to_fixpoint(tcx, &body, None)
        .into_results_cursor(&body);
    let mut uninits = MaybeUninitializedPlaces::new(tcx, &body, &move_data)
        .mark_inactive_variants_as_uninit()
        .iterate_to_fixpoint(tcx, &body, None)
        .into_results_cursor(&body);
    let live = reachable(&body);
    let mut out = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if !live[bb.as_usize()] {
            continue;
        }
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Drop { place, .. } = &term.kind else { continue };
        let place_ty = place.ty(&body.local_decls, tcx).ty;
        if !needs_drop(place_ty) {
            continue;
        }
        let loc = body.terminator_loc(bb);
        let style = match move_data.rev_lookup.find(place.as_ref()) {
            LookupResult::Exact(path) => {
                inits.seek_before_primary_effect(loc);
                uninits.seek_before_primary_effect(loc);
                let is_init = |p: MovePathIndex| inits.get().contains(p);
                let is_uninit = |p: MovePathIndex| uninits.get().contains(p);
                let (some_init, some_uninit, children) =
                    deep_state(&move_data, path, &is_init, &is_uninit);
                match (some_init, some_uninit, children != 1) {
                    (false, _, _) => None,
                    (true, false, _) => Some(LiveStyle::Static),
                    (true, true, false) => Some(LiveStyle::Conditional),
                    (true, true, true) => open_drop_is_live(
                        tcx,
                        &needs_drop,
                        &move_data,
                        path,
                        place_ty,
                        &is_init,
                        &is_uninit,
                        0,
                    )
                    .then_some(LiveStyle::Open),
                }
            }
            // A drop behind a pointer (drop-and-replace of `*p`): borrowck requires the place
            // initialized, and elaboration keeps the drop unconditional.
            LookupResult::Parent(_) => Some(LiveStyle::Static),
        };
        out.push(OracleDrop {
            block: bb,
            // A drop of a projected place (a drop-and-replace of `(*p).f` or `x.f`) is not a drop
            // of the local it starts from.
            identity: if place.projection.is_empty() {
                identity_of(&body, place.local)
            } else {
                DropIdentity::Other
            },
            ty: tcx.type_id_hash(place_ty).as_u128(),
            span: term.source_info.span,
            style,
            projected: !place.projection.is_empty(),
        });
    }
    Some(out)
}
