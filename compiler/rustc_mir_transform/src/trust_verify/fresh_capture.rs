//! Trust (2026-10-18, FRESH-CAPTURE-1; candidate-gate RCA precision T1): which
//! by-reference captures of a local closure hold, in EVERY value of the closure type
//! that exists at run time, the tag of a FRESH shared borrow — COMPILER side.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! ## Why
//!
//! CALL-HAVOC-ESCAPE-2 (`c871ae5f40`) havocs, at every call, the memory behind every
//! reference LOADED FROM MEMORY: such a reference was never retagged, so its bits may
//! be a raw pointer's (`transmute`d, `ptr::read`, a union field) with write
//! permission, and a callee may write its target in a defined execution. A closure's
//! by-reference capture `(*_1).k: &T` is loaded from memory, so
//! `|p| { let q = p / w; sink(q); p % w }` lost `w != 0` at `sink(q)` and the
//! remainder row FAILED with `w = 0` on a closure that cannot divide by zero
//! (aterm-conformance `scan.rs:1460`, aterm-control `selection.rs:357`; the seal
//! 321aaeda75 proved them, the 2026-10-16 candidate refuted them).
//!
//! ## What is decided here (by `DefId`, type and MIR shape only)
//!
//! For each local PLAIN closure `C` (never a coroutine or coroutine-closure) whose
//! parent `P` passes `adapter_yield::parent_is_eligible` (a non-generic, non-const,
//! non-`async` `fn`/method, not Clean-origin), over `P`'s PRE-INLINING MIR
//! (`mir_drops_elaborated_and_const_checked`, borrowed before anything steals it; a
//! stolen body admits nothing) and its promoteds:
//!
//! 1. ONE CONSTRUCTION. `P` holds exactly one `Aggregate(Closure(C), ops)`, assigned
//!    to a whole local `c` written by nothing else, never `_0` or an argument (an
//!    `impl Fn` return place's declared type is opaque and does not show `C`); no
//!    promoted mentions `C`; neither `_0` nor an argument of `P` mentions `C`.
//! 2. FRESH SHARED BORROWS. Capture `k` is admitted when its upvar type is a SHARED
//!    reference `&T` with `T: Freeze` and `ops[k]` is a `copy`/`move` of a whole local
//!    `b` that is written exactly once, by `b = &place` (`BorrowKind::Shared`), and used
//!    exactly once more, by this aggregate.
//! 3. ONLY CALLED. Every other non-drop use of `c` is a whole-local borrow `r = &c` /
//!    `r = &mut c` into a temp written once and MOVED once, as the receiver (argument
//!    0), into a call of `Fn::call` / `FnMut::call_mut`; or a move of `c` itself as
//!    argument 0 of `FnOnce::call_once`. The callee's generic `Self` is exactly `C`,
//!    and neither its argument-tuple type, nor the call's other arguments, nor its
//!    destination mentions `C`.
//! 4. ACCOUNTING. Every local of `P` whose type mentions `C` is `c`, one of those
//!    borrow temps, or has no non-drop use; every constant mentioning `C` is the
//!    `FnDef` operand of an admitted call; every located type mentioning `C` sits at
//!    an admitted location.
//!
//! Crate-wide, exactly as `adapter_yield`: a crate enabling `type_alias_impl_trait`,
//! `impl_trait_in_assoc_type`, `specialization` or `min_specialization` gets nothing
//! (an opaque alias names a closure type crate-wide; a specializing impl can bind a
//! generic to it).
//!
//! ## Why that suffices
//!
//! A value of type `C` comes into existence only by the closure aggregate, by a copy
//! or move of an existing `C` value, or by TYPE PUNNING at a type that mentions `C`
//! (`transmute`, `transmute_copy`, `ptr::read`, a union field, a raw-pointer cast):
//! the last needs code that NAMES `C`. `C` is nameable only inside `P` and inside
//! generic code `P` instantiates with a type mentioning `C`. Steps 1, 3 and 4 leave
//! no such instantiation but `C`'s own builtin call-trait methods, which run `C`'s
//! body (core's `call_once` shim for an `Fn` closure calls the same body) and only
//! read the captures; no promoted or nested body sees `C`, and `C` leaves `P`
//! through no argument, return value or other local. So every `C` value at run time
//! is a value step 1 constructed (or a copy of one), and its capture `k` holds the
//! tag that step 2's fresh shared borrow of `place` created. While a body reads
//! through that tag, a write to `place`'s `Freeze` bytes through any pointer not
//! derived from it makes EVERY LATER READ THROUGH IT undefined behaviour (Stacked
//! Borrows pops the tag's `SharedReadOnly` item; Tree Borrows disables the node),
//! and nothing derived from a shared tag may write `Freeze` bytes. That is the
//! premise CALL-HAVOC-ESCAPE-2 already rests its KEPT rule on for a retagged
//! reference LOCAL (`l = &place`: `path_defs::ref_local_is_retagged`), and owner
//! ruling R1's (docs/TCB.md, "Shared-reborrow immutability across a call"). So in
//! every defined execution a read of `*(*_1).k` after a call sees the value a read
//! before the call saw, and vcgen may keep the facts about it.
//!
//! What it does NOT decide: whether the closure body may use it. That is re-gated in
//! `trust_vcgen` (`generate::path_defs::premised_capture_fields`) on the body actually
//! verified: `_1` is a never-reseated SHARED `&C` parameter, the upvar is a shared
//! reference to pointer-free `Freeze` data (`pointee_is_read_only`), and no statement
//! or terminator of the body writes a place under `_1` or writes an unlocatable place.
//!
//! Everything fails CLOSED: any mismatch installs nothing, which is exactly the
//! CALL-HAVOC-ESCAPE-2 behaviour. A body that received the premise is never
//! check-elided (`elide_kernel_certified_checks`), keyed on installation.
//! `TRUST_FRESH_CAPTURE_TRACE=1` prints every admitted closure and every decline.

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext};
use rustc_middle::mir::{AggregateKind, BorrowKind, Location};

use super::adapter_yield::{
    BodyFacts, body_mentions_closure, is_closure_type, mentions_closure, non_drop_uses,
    parent_is_eligible, statement_at, terminator_location,
};
use super::*;

/// The analysis-seam initializer, called from `rustc_interface::passes::analysis`
/// beside `trust_init_adapter_yield_premises`, while each parent's
/// `mir_drops_elaborated_and_const_checked` is still borrowable. A closure verified
/// before this seam sees an empty map and fails closed.
// The trace iterates the map only to SORT it before printing.
#[allow(rustc::potential_query_instability)]
pub fn trust_init_fresh_capture_premises(tcx: TyCtxt<'_>) {
    if !verification_enabled(tcx.sess)
        || with_crate_verification_state(tcx.sess, |state| state.fresh_capture_initialized)
    {
        return;
    }
    let features = tcx.features();
    let premises = if features.type_alias_impl_trait()
        || features.impl_trait_in_assoc_type()
        || features.specialization()
        || features.min_specialization()
    {
        FxHashMap::default()
    } else {
        collect_premises(tcx)
    };
    if env_flag_enabled("TRUST_FRESH_CAPTURE_TRACE") {
        let mut rows: Vec<_> = premises
            .iter()
            .map(|(def, fields)| {
                (
                    def.local_def_index.as_u32(),
                    trust_mir_extract::safe_def_path_str(tcx, def.to_def_id()),
                    fields.clone(),
                )
            })
            .collect();
        rows.sort();
        for (_, path, fields) in rows {
            eprintln!("TRUST_FRESH_CAPTURE_TRACE: {path}: fresh shared capture fields {fields:?}");
        }
    }
    with_crate_verification_state(tcx.sess, |state| {
        state.fresh_capture_fields = premises;
        state.fresh_capture_initialized = true;
    });
}

/// The capture fields installed for the body being verified: its OWN item body (never
/// a promoted, never a shim).
pub(super) fn fields_for_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<usize> {
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
        state.fresh_capture_fields.get(&local).cloned().unwrap_or_default()
    })
}

/// Whether ANY capture field was installed for `def` — keyed on installation, not on
/// whether vcgen's gates later used it. Such a body is never check-elided.
pub(super) fn body_carries_premise(tcx: TyCtxt<'_>, def: DefId) -> bool {
    let Some(local) = def.as_local() else {
        return false;
    };
    with_crate_verification_state(tcx.sess, |state| {
        state.fresh_capture_fields.get(&local).is_some_and(|fields| !fields.is_empty())
    })
}

fn declined<T>(closure: DefId, why: &str) -> Option<T> {
    if env_flag_enabled("TRUST_FRESH_CAPTURE_TRACE") {
        eprintln!("TRUST_FRESH_CAPTURE_TRACE: declined {closure:?}: {why}");
    }
    None
}

// `is_stolen()` is untracked, exactly as at the other pre-steal seams: a stolen body
// admits nothing (fail-closed). The parent map's keys are SORTED before use.
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
fn collect_premises(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, Vec<usize>> {
    let mut out = FxHashMap::default();
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
            rustc_middle::mir::visit::Visitor::visit_basic_block_data(&mut facts, bb, data);
        }
        let mut closures = by_parent.remove(&parent).unwrap_or_default();
        closures.sort_unstable_by_key(|def| def.local_def_index.as_u32());
        for closure in closures {
            if let Some(fields) = derive_fields(tcx, &body, promoted, &facts, closure.to_def_id())
                && !fields.is_empty()
            {
                out.insert(closure, fields);
            }
        }
    }
    out
}

/// A whole local with exactly two non-drop uses, in either visit order: ONE `Store`
/// (returned) and one use at `use_loc` that `use_ok` accepts.
fn stored_once_then_used_at(
    facts: &BodyFacts<'_>,
    local: Local,
    use_loc: Location,
    use_ok: impl Fn(PlaceContext) -> bool,
) -> Option<Location> {
    let uses = non_drop_uses(facts, local);
    let [a, b] = uses[..] else {
        return None;
    };
    let is_store = |(context, _): (PlaceContext, Location)| {
        matches!(context, PlaceContext::MutatingUse(MutatingUseContext::Store))
    };
    let (store, other) = if is_store(a) { (a, b) } else { (b, a) };
    (is_store(store) && !is_store(other) && use_ok(other.0) && other.1 == use_loc)
        .then_some(store.1)
}

// `closure_locals` is iterated only for order-independent `any`/`all`-style checks.
#[allow(rustc::potential_query_instability)]
fn derive_fields<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    promoted: &IndexVec<rustc_middle::mir::Promoted, Body<'tcx>>,
    facts: &BodyFacts<'tcx>,
    closure: DefId,
) -> Option<Vec<usize>> {
    let closure_ty = tcx.type_of(closure).instantiate_identity().skip_normalization();
    let ty::Closure(_, closure_args) = closure_ty.kind() else {
        return None;
    };
    let upvars = closure_args.as_closure().upvar_tys();
    if upvars.is_empty() {
        return None;
    }
    if promoted.iter().any(|promoted| body_mentions_closure(promoted, closure)) {
        return declined(closure, "a promoted mentions the closure");
    }
    // The locals whose type mentions `C`. Never the return place or an argument.
    let closure_locals: FxHashSet<Local> = body
        .local_decls
        .iter_enumerated()
        .filter(|(_, decl)| mentions_closure(decl.ty, closure))
        .map(|(local, _)| local)
        .collect();
    if closure_locals.iter().any(|local| local.as_usize() <= body.arg_count) {
        return declined(closure, "the return place or an argument mentions the closure");
    }

    // 1. ONE CONSTRUCTION, into a whole local `c`.
    let creations: Vec<Location> = facts
        .closure_aggregates
        .iter()
        .filter(|(_, def)| *def == closure)
        .map(|(loc, _)| *loc)
        .collect();
    let [agg_loc] = creations[..] else {
        return declined(closure, "not exactly one closure aggregate");
    };
    let StatementKind::Assign(assign) = &statement_at(body, agg_loc)?.kind else {
        return declined(closure, "the aggregate is not an assignment");
    };
    let (dest, rvalue) = &**assign;
    let Rvalue::Aggregate(kind, ops) = rvalue else {
        return None;
    };
    if !matches!(**kind, AggregateKind::Closure(def, _) if def == closure) {
        return None;
    }
    let Some(c) = dest.as_local() else {
        return declined(closure, "the aggregate's destination is not a whole local");
    };
    // Never the return place or an argument: `_0`'s declared type may be an opaque
    // `impl Fn` whose `walk()` does not show `C`, and the caller then holds a `C`.
    if c.as_usize() <= body.arg_count {
        return declined(closure, "the closure is constructed into the return place");
    }
    if ops.len() != upvars.len() {
        return declined(closure, "aggregate operand count differs from the upvar count");
    }
    let mut admitted_locs: Vec<Location> = vec![agg_loc];
    let mut admitted_locals: Vec<Local> = vec![c];

    // 2. FRESH SHARED BORROWS, per capture.
    let typing_env = body.typing_env(tcx);
    let mut fields = Vec::new();
    for (k, (op, upvar_ty)) in ops.iter().zip(upvars.iter()).enumerate() {
        let ty::Ref(_, pointee, mutbl) = upvar_ty.kind() else { continue };
        if mutbl.is_mut() || !pointee.is_freeze(tcx, typing_env) {
            continue;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = op else { continue };
        let Some(b) = place.as_local() else { continue };
        if b.as_usize() <= body.arg_count || closure_locals.contains(&b) {
            continue;
        }
        let Some(def_loc) = stored_once_then_used_at(facts, b, agg_loc, |ctx| {
            matches!(
                ctx,
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Move | NonMutatingUseContext::Copy
                )
            )
        }) else {
            continue;
        };
        let Some(statement) = statement_at(body, def_loc) else { continue };
        let StatementKind::Assign(assign) = &statement.kind else { continue };
        let (dest, rvalue) = &**assign;
        if dest.as_local() == Some(b) && matches!(rvalue, Rvalue::Ref(_, BorrowKind::Shared, _)) {
            fields.push(k);
        }
    }
    if fields.is_empty() {
        return declined(closure, "no capture is a fresh shared borrow of `Freeze` data");
    }

    // 3. ONLY CALLED: every non-drop use of `c` but its one `Store`, the aggregate.
    let uses = non_drop_uses(facts, c);
    let stores: Vec<Location> = uses
        .iter()
        .filter(|(context, _)| {
            matches!(context, PlaceContext::MutatingUse(_)
            if !matches!(context, PlaceContext::MutatingUse(MutatingUseContext::Borrow)))
        })
        .map(|(_, loc)| *loc)
        .collect();
    if stores != [agg_loc] {
        return declined(closure, "the closure local is written other than by its construction");
    }
    let rest: Vec<(PlaceContext, Location)> =
        uses.iter().copied().filter(|(_, loc)| *loc != agg_loc).collect();
    let mut expected_consts: Vec<Location> = Vec::new();
    for (context, loc) in &rest {
        let call_loc = match context {
            // `r = &c` / `r = &mut c`, `r` moved once into the call.
            PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow)
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                let Some(statement) = statement_at(body, *loc) else {
                    return declined(closure, "a borrow of the closure is not a statement");
                };
                let StatementKind::Assign(assign) = &statement.kind else {
                    return declined(closure, "a borrow of the closure is not an assignment");
                };
                let (dest, rvalue) = &**assign;
                if !matches!(rvalue, Rvalue::Ref(_, _, borrowed) if borrowed.as_local() == Some(c))
                {
                    return declined(closure, "a borrow of a part of the closure");
                }
                let Some(r) = dest.as_local() else {
                    return declined(closure, "a closure borrow into a projection");
                };
                let r_uses = non_drop_uses(facts, r);
                let moves: Vec<Location> = r_uses
                    .iter()
                    .filter(|(context, _)| {
                        matches!(context, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move))
                    })
                    .map(|(_, loc)| *loc)
                    .collect();
                let [moved_loc] = moves[..] else {
                    return declined(closure, "a closure borrow is not moved exactly once");
                };
                if stored_once_then_used_at(facts, r, moved_loc, |ctx| {
                    matches!(ctx, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move))
                }) != Some(*loc)
                {
                    return declined(closure, "a closure borrow's store/move shape");
                }
                admitted_locs.push(*loc);
                admitted_locals.push(r);
                if !call_receives_closure_as_receiver(tcx, body, moved_loc, r, closure, false) {
                    return declined(
                        closure,
                        "a closure borrow reaches something but its own call",
                    );
                }
                moved_loc
            }
            // `FnOnce::call_once(move c, args)`.
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                if !call_receives_closure_as_receiver(tcx, body, *loc, c, closure, true) {
                    return declined(
                        closure,
                        "the closure value moves into something but its call",
                    );
                }
                *loc
            }
            _ => return declined(closure, "another use of the closure local"),
        };
        admitted_locs.push(call_loc);
        expected_consts.push(call_loc);
    }

    // 4. THE ACCOUNTING.
    let mut seen_consts: Vec<Location> = Vec::new();
    for (loc, ty) in &facts.consts {
        if !mentions_closure(*ty, closure) {
            continue;
        }
        if !expected_consts.contains(loc) {
            return declined(closure, "a constant mentioning the closure outside its calls");
        }
        seen_consts.push(*loc);
    }
    let mut want = expected_consts.clone();
    want.sort();
    seen_consts.sort();
    if seen_consts != want {
        return declined(closure, "closure-call constant count mismatch");
    }
    if facts
        .located_tys
        .iter()
        .any(|(loc, ty)| mentions_closure(*ty, closure) && !admitted_locs.contains(loc))
    {
        return declined(closure, "a located type mentions the closure outside the admitted sites");
    }
    for local in &closure_locals {
        if admitted_locals.contains(local) {
            continue;
        }
        if !non_drop_uses(facts, *local).is_empty() {
            return declined(closure, "another local mentioning the closure is used");
        }
    }
    Some(fields)
}

/// Whether the terminator at `loc` is a call of a `Fn`-family trait method whose
/// generic `Self` is exactly the closure type, receiving `receiver` (moved) as argument
/// 0 — `FnOnce::call_once` when `by_value`, `Fn::call` / `FnMut::call_mut` otherwise —
/// and whose argument-tuple type, other arguments and destination do not mention the
/// closure.
fn call_receives_closure_as_receiver<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loc: Location,
    receiver: Local,
    closure: DefId,
    by_value: bool,
) -> bool {
    if loc != terminator_location(body, loc.block) {
        return false;
    }
    let TerminatorKind::Call { func, args, destination, .. } =
        &body.basic_blocks[loc.block].terminator().kind
    else {
        return false;
    };
    let Some((method, generic_args)) = func.const_fn_def() else {
        return false;
    };
    let Some(trait_def) = tcx.trait_of_assoc(method) else {
        return false;
    };
    let Some(kind) = tcx.fn_trait_kind_from_def_id(trait_def) else {
        return false;
    };
    if by_value != matches!(kind, ty::ClosureKind::FnOnce) {
        return false;
    }
    // `<C as Fn<A>>::call`: generic args `[C, A]`.
    let mut generic_types = generic_args.iter().filter_map(|arg| arg.as_type());
    let Some(self_ty) = generic_types.next() else {
        return false;
    };
    if !is_closure_type(self_ty, closure) || generic_types.any(|ty| mentions_closure(ty, closure)) {
        return false;
    }
    let Some((first, others)) = args.split_first() else {
        return false;
    };
    if !matches!(&first.node, Operand::Move(place) if place.as_local() == Some(receiver)) {
        return false;
    }
    if others.iter().any(|arg| mentions_closure(arg.node.ty(&body.local_decls, tcx), closure)) {
        return false;
    }
    !mentions_closure(destination.ty(&body.local_decls, tcx).ty, closure)
}
