//! Trust: the once-initializer re-entrancy check.
//!
//! A `static` of type `std::sync::{OnceLock, LazyLock, Once}` whose initializer can
//! WAIT on that same cell deadlocks: std's `Once` has no thread-identity check, so
//! the initializing thread parks on its own `RUNNING` state forever (queue and futex
//! implementations alike; the `no_threads` one panics). The `core::cell::{OnceCell,
//! LazyCell}` twins panic instead (`reentrant init` / a poisoned `LazyCell`). There is
//! no legitimate instance of either, so this is a HARD ERROR with no `#[allow]` —
//! not a lint — and it is gated by NOTHING but front-end cleanliness: it runs with
//! `-Ztrust-verify=off`, the state of every ordinary build. The motivating defect is
//! aterm v0.65.0 (2026-08-30): `static ARMED: OnceLock<bool>` in
//! `debug_seamless_reexec_armed` had an initializer that called
//! `debug_seamless_reexec_armed()` — every update apply then hung the main thread.
//!
//! # How it works
//!
//! 1. **Census.** Every local `static` whose EXACT type is one of the five cells
//!    (diagnostic items on the types). A crate with none returns immediately, having
//!    paid one `type_of` per static and nothing else.
//! 2. **Per-body facts** (`trust_mir_once_body_facts`, disk-cached, MIR-free result):
//!    for each call in the body's MIR — the elaborated body, or `optimized_mir` for a
//!    coroutine, whose elaborated body is already stolen (`with_body`) — the WAITING
//!    methods (diagnostic items on
//!    `get_or_init`, `set`, `wait`, `call_once`, `force`, ... — see `waiting_method`)
//!    and `Deref`/`DerefMut` on the `Lazy*` types, recognised structurally. The
//!    receiver is resolved to a static through the `&(*_n)` reborrow chain down to
//!    the `Operand::Constant` whose provenance is `GlobalAlloc::Static` — and a
//!    receiver that is a call DESTINATION is followed into the (local, eligible)
//!    callee's return place, so an accessor fn's return names the cell too. The
//!    initializer a call starts is the closure or fn item its second argument's TYPE
//!    names; a `LazyLock`/`LazyCell` static takes its initializer from the static's
//!    own CTFE MIR (`LazyLock::new(f)`, through the `ClosureFnPointer`/`ReifyFnPointer`
//!    coercion) or, failing that, from the function provenance of its evaluated
//!    initializer.
//! 3. **Reachability.** From each initializer body, a worklist over
//!    `trust_mir_direct_local_callees` (closure ARGUMENTS are already edges there),
//!    plus local fn items passed as arguments, MINUS the values handed to a
//!    `std::thread` spawn entry point — those run on another thread, so a spawned
//!    thread that waits on the cell (aterm's `QUARANTINE` reaper) is not a self-wait.
//!    Cross-crate callees are opaque. A HIT is any reached body — the initializer
//!    itself included — with a wait on the SAME static. That also catches a two-cell
//!    cycle (A's initializer waits on B whose initializer waits on A) through the
//!    closure-argument edges.
//!
//! # Precision limits (all documented in the design note)
//!
//! False positives: reachability is path-insensitive inside callees, so a re-entrant
//! wait on a dead branch (`if false { f() }`) is flagged; a closure handed to a
//! NON-std spawner (a thread pool) is treated as synchronous. Deferred-callback
//! REGISTRATION inside an initializer (`std::panic::set_hook`, an atexit/registry
//! `register(f)`) is in that class ON PURPOSE: the init window is not safe for a
//! cell-reading callback — a panic inside the initializer runs a panic hook
//! re-entrantly — and repair 3 (`C.get()`, which never waits) keeps the pattern.
//! All carry the call
//! path and three repairs in the diagnostic. False negatives: a receiver reached
//! through a fn parameter, an ambiguous local (assignments — or followed call
//! returns — naming two DIFFERENT statics), a reference or a field, while a
//! receiver RETURNED by a call IS followed into the local callee's return place
//! (an accessor fn — `fn cell() -> &'static OnceLock<..>`, `const fn` included —
//! no longer hides the cell; a cross-crate or fn-pointer accessor stays opaque);
//! an initializer passed as a `fn` pointer or `dyn FnOnce`, and a fn item CAST to
//! a fn pointer before being passed (`register(f as fn())` erases the callback
//! edge above); `thread_local!` cells
//! (behind `LocalKey::with`); cross-crate callees and cells; a `std::thread` spawn
//! that the initializer JOINS (scoped threads included) — the edge is dropped as a
//! thread boundary; a `Copy` closure both spawned and called directly in one body.

use std::collections::VecDeque;

use rustc_abi::Size;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{ConstContext, LangItem};
use rustc_middle::mir::interpret::{GlobalAlloc, Scalar};
use rustc_middle::mir::trust_once::{TrustOnceBodyFacts, TrustOnceCellKind, TrustOnceWaitSite};
use rustc_middle::mir::{
    AggregateKind, Body, CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, GenericArgsRef, Instance, InstanceKind, ShimKind, TyCtxt, TypingEnv};
use rustc_span::{Span, Symbol, sym};

use crate::diagnostics::TrustOnceInitializerReentrancy;

/// Bound on the local-to-local walks (`&(*_n)` reborrow chains, fn-pointer
/// coercions). Real chains are two or three steps; the bound keeps the walk total on
/// odd MIR.
const OPERAND_WALK_DEPTH: u32 = 16;

// ---------------------------------------------------------------------------
// Cell identity
// ---------------------------------------------------------------------------

/// The cell kind of an ADT, by diagnostic item on the type.
fn cell_kind_of_adt(tcx: TyCtxt<'_>, adt_did: DefId) -> Option<TrustOnceCellKind> {
    Some(match tcx.get_diagnostic_name(adt_did)? {
        sym::OnceLock => TrustOnceCellKind::OnceLock,
        sym::LazyLock => TrustOnceCellKind::LazyLock,
        sym::Once => TrustOnceCellKind::Once,
        sym::OnceCell => TrustOnceCellKind::OnceCell,
        sym::LazyCell => TrustOnceCellKind::LazyCell,
        _ => return None,
    })
}

/// The cell kind a local `static` IS — its exact type, no peeling. `None` for
/// anything that is not a (non-nested) static of exactly one of the five cell types.
pub(crate) fn cell_kind_of_static(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<TrustOnceCellKind> {
    let DefKind::Static { nested: false, .. } = tcx.def_kind(def) else {
        return None;
    };
    let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
    cell_kind_of_adt(tcx, ty.ty_adt_def()?.did())
}

/// The waiting methods, by diagnostic item: the cell kind they belong to and whether
/// the call STARTS the cell's initializer (its second argument). `set`/`try_insert`
/// are here on purpose: on `OnceLock` they go through `initialize` and park on
/// `RUNNING` exactly like `get_or_init`; on `OnceCell` a `set` inside the initializer
/// makes the outer `try_init` panic `reentrant init`. `Lazy*::force*` start no
/// initializer of their own — the static carries it (`lazy_static_initializer`).
fn waiting_method(name: Symbol) -> Option<(TrustOnceCellKind, bool)> {
    use TrustOnceCellKind::*;
    Some(match name {
        sym::once_lock_get_or_init
        | sym::once_lock_get_mut_or_init
        | sym::once_lock_get_or_try_init
        | sym::once_lock_get_mut_or_try_init => (OnceLock, true),
        sym::once_lock_wait | sym::once_lock_set | sym::once_lock_try_insert => (OnceLock, false),
        sym::once_call_once | sym::once_call_once_force => (Once, true),
        sym::once_wait | sym::once_wait_force => (Once, false),
        sym::lazy_lock_force | sym::lazy_lock_force_mut => (LazyLock, false),
        sym::once_cell_get_or_init
        | sym::once_cell_get_mut_or_init
        | sym::once_cell_get_or_try_init
        | sym::once_cell_get_mut_or_try_init => (OnceCell, true),
        sym::once_cell_set | sym::once_cell_try_insert => (OnceCell, false),
        sym::lazy_cell_force | sym::lazy_cell_force_mut => (LazyCell, false),
        _ => return None,
    })
}

/// The `std::thread` entry points that run their closure/fn argument on ANOTHER
/// thread: not a synchronous edge for the walk.
fn is_thread_spawn(name: Symbol) -> bool {
    matches!(
        name,
        sym::thread_spawn
            | sym::thread_builder_spawn
            | sym::thread_builder_spawn_unchecked
            | sym::thread_builder_spawn_scoped
            | sym::thread_scope_spawn
    )
}

/// `<LazyLock<..> as Deref>::deref` / `DerefMut::deref_mut` (and the `LazyCell`
/// twins), recognised structurally: the callee is the `Deref`/`DerefMut` lang trait's
/// method and its `Self` type is a `Lazy*` cell. Every `*LAZY`, `LAZY.field` and
/// auto-deref'd `LAZY.method()` lowers to exactly this call.
fn lazy_deref_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    gen_args: GenericArgsRef<'tcx>,
) -> Option<TrustOnceCellKind> {
    let trait_did = tcx.trait_of_assoc(callee)?;
    if !(tcx.is_lang_item(trait_did, LangItem::Deref)
        || tcx.is_lang_item(trait_did, LangItem::DerefMut))
    {
        return None;
    }
    let self_ty = gen_args.get(0)?.as_type()?;
    let kind = cell_kind_of_adt(tcx, self_ty.ty_adt_def()?.did())?;
    kind.is_lazy().then_some(kind)
}

// ---------------------------------------------------------------------------
// Node filter
// ---------------------------------------------------------------------------

/// The bodies the walk may visit and the facts query may be demanded for. This MUST
/// stay identical to the SCC builder's filter in `trust_verify.rs`
/// (`trust_mir_mutually_recursive_functions`): both queries borrow
/// `mir_drops_elaborated_and_const_checked` unguarded, which is legal only for a body
/// whose elaborated MIR nothing STEALS before `optimized_mir` — i.e. not a
/// `#[rustc_comptime]` fn (`inner_mir_for_ctfe` steals it), not a static/const body,
/// not a Clean-origin def (served by a gated emission), and not a synthetic
/// coroutine body. A REAL coroutine (an `async fn`/`async` block body) passes the
/// filter but is never read through that borrow — see `with_body`.
pub(crate) fn is_eligible_body(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
        && matches!(tcx.hir_body_const_context(def), None | Some(ConstContext::ConstFn))
        && !crate::clean_origin_mir::is_clean_origin(tcx, def)
}

/// Run `f` on the MIR the check reads for `def`. An ordinary fn or closure is read
/// through its elaborated body, still unstolen when the driver hook runs. A
/// COROUTINE (an `async fn`/`async` block body) is read through `optimized_mir`:
/// `run_required_analyses` computes every coroutine's layout before `analysis` runs
/// the hooks, and `coroutine_layout` forces `optimized_mir`, whose first act is to
/// steal the elaborated body — reading the `Steal` then ICEs ("attempted to read
/// from stolen value"; measured 2026-08-30 on aterm v0.65.0's `aterm-gpu`, where
/// `async fn adapter_from_env` shares a crate with cell statics). Same routing as
/// the R1 caller scan (`tests/ui/trust/r1/flip_with_async_present.rs`). The
/// `optimized_mir` demand is a cache hit there, never a fresh steal.
fn with_body<'tcx, R>(tcx: TyCtxt<'tcx>, def: LocalDefId, f: impl FnOnce(&Body<'tcx>) -> R) -> R {
    if tcx.is_coroutine(def.to_def_id()) {
        f(tcx.optimized_mir(def))
    } else {
        let elaborated = tcx.mir_drops_elaborated_and_const_checked(def);
        let body = elaborated.borrow();
        f(&body)
    }
}

// ---------------------------------------------------------------------------
// Operand resolution
// ---------------------------------------------------------------------------

/// Every rvalue assigned to the bare local `local` in `body`.
fn assignments_to<'a, 'tcx>(
    body: &'a Body<'tcx>,
    local: rustc_middle::mir::Local,
) -> impl Iterator<Item = &'a Rvalue<'tcx>> + 'a {
    body.basic_blocks.iter().flat_map(move |block| {
        block.statements.iter().filter_map(move |statement| match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                (place.local == local && place.projection.is_empty()).then_some(rvalue)
            }
            _ => None,
        })
    })
}

/// Resolve a call RECEIVER operand to the local cell static it borrows, if it is one.
///
/// Observed shapes (built and elaborated MIR): `_3 = const {alloc1: &OnceLock<bool>};
/// _2 = &(*_3); get_or_init(move _2, ..)`, with a `*mut Cell` constant and a
/// `&mut (*_3)` / `&raw` for `static mut`; and `_3 = cell() -> [return: ..]; _2 =
/// &(*_3)` for a receiver produced by an ACCESSOR — a call destination has no
/// assignment statement, so call terminators are followed into the callee's return
/// place (`resolve_returned_static`). A pointer INTO a static (offset ≠ 0, i.e. a
/// cell that is a field of some other static) is rejected; the census then also
/// rejects the outer static because its exact type is not a cell. Two sources that
/// resolve to DIFFERENT statics make the receiver ambiguous — `None`, a documented
/// false negative — rather than a guess in a hard error.
fn resolve_static_receiver<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    depth: u32,
    borrowed: &mut Vec<LocalDefId>,
) -> Option<LocalDefId> {
    if depth == 0 {
        return None;
    }
    match operand {
        Operand::Constant(constant) => {
            let Scalar::Ptr(ptr, _) = constant.const_.try_to_scalar()? else {
                return None;
            };
            let (prov, offset) = ptr.into_raw_parts();
            if offset != Size::ZERO {
                return None;
            }
            match tcx.global_alloc(prov.alloc_id()) {
                GlobalAlloc::Static(did) => did.as_local(),
                _ => None,
            }
        }
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            let mut found: Option<LocalDefId> = None;
            for rvalue in assignments_to(body, place.local) {
                let resolved = match rvalue {
                    Rvalue::Use(inner, _) => {
                        resolve_static_receiver(tcx, body, inner, depth - 1, borrowed)
                    }
                    Rvalue::Ref(_, _, inner) | Rvalue::RawPtr(_, inner)
                        if matches!(inner.projection[..], [ProjectionElem::Deref]) =>
                    {
                        resolve_static_receiver(
                            tcx,
                            body,
                            &Operand::Copy(Place::from(inner.local)),
                            depth - 1,
                            borrowed,
                        )
                    }
                    _ => None,
                };
                match (found, resolved) {
                    (Some(a), Some(b)) if a != b => return None,
                    (None, Some(b)) => found = Some(b),
                    _ => {}
                }
            }
            // A call DESTINATION (`_n = cell()`) has no assignment statement:
            // follow the callee into its return place, merged under the same
            // ambiguity rule as the assignments above.
            for block in body.basic_blocks.iter() {
                let TerminatorKind::Call { func, destination, .. } = &block.terminator().kind
                else {
                    continue;
                };
                if destination.local != place.local || !destination.projection.is_empty() {
                    continue;
                }
                let resolved = resolve_returned_static(tcx, body, func, depth - 1, borrowed);
                match (found, resolved) {
                    (Some(a), Some(b)) if a != b => return None,
                    (None, Some(b)) => found = Some(b),
                    _ => {}
                }
            }
            found
        }
        Operand::RuntimeChecks(_) => None,
    }
}

/// The local cell static a CALLEE returns a reference to, if its return place
/// resolves to one — how an accessor fn (`fn cell() -> &'static OnceLock<..> {
/// &ARMED }`, `const fn` included) is followed. Local, eligible callees only (a
/// cross-crate accessor is opaque); a trait callee resolves through
/// `Instance::try_resolve` first, like `edge_span`. `borrowed` carries every body
/// whose MIR the current resolution chain already holds a borrow on: re-entering
/// one (a self-recursive accessor) would nest a read borrow of the same `Steal`,
/// so such a callee is skipped instead — a documented false negative, like any
/// other unresolved receiver.
fn resolve_returned_static<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    depth: u32,
    borrowed: &mut Vec<LocalDefId>,
) -> Option<LocalDefId> {
    if depth == 0 {
        return None;
    }
    let (callee, gen_args) = func.const_fn_def()?;
    let callee = match Instance::try_resolve(tcx, body.typing_env(tcx), callee, gen_args) {
        Ok(Some(instance)) => instance.def_id(),
        _ => callee,
    };
    let callee = callee.as_local()?;
    if !is_eligible_body(tcx, callee) || borrowed.contains(&callee) {
        return None;
    }
    borrowed.push(callee);
    let returned = with_body(tcx, callee, |callee_body| {
        resolve_static_receiver(
            tcx,
            callee_body,
            &Operand::Copy(Place::return_place()),
            depth,
            borrowed,
        )
    });
    borrowed.pop();
    returned
}

/// The closure or fn item an operand's TYPE names (one `&` peeled). This is how an
/// initializer argument, a spawned value, and a fn-value edge are identified: a
/// closure value is its own type whatever produced it, and a fn item is a `FnDef`.
fn fn_value_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<DefId> {
    let ty = operand.ty(&body.local_decls, tcx);
    let ty = match ty.kind() {
        ty::Ref(_, inner, _) => *inner,
        _ => ty,
    };
    match ty.kind() {
        ty::Closure(did, _) | ty::FnDef(did, _) => Some(*did),
        _ => None,
    }
}

/// Like `fn_value_def`, but also sees through a `fn` POINTER produced in this body:
/// `_1 = move _2 as fn() -> T (ClosureFnPointer)` / `(ReifyFnPointer)`, a `Use`, or a
/// closure `Aggregate`. Used on a `Lazy*::new(f)` argument in a static's CTFE MIR,
/// where `F` defaults to `fn() -> T` and the closure is coerced before the call.
fn resolve_fn_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    depth: u32,
) -> Option<DefId> {
    if depth == 0 {
        return None;
    }
    if let Some(did) = fn_value_def(tcx, body, operand) {
        return Some(did);
    }
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    for rvalue in assignments_to(body, place.local) {
        let resolved = match rvalue {
            Rvalue::Use(inner, _) => resolve_fn_value(tcx, body, inner, depth - 1),
            Rvalue::Cast(
                CastKind::PointerCoercion(
                    PointerCoercion::ClosureFnPointer(_) | PointerCoercion::ReifyFnPointer(_),
                    _,
                ),
                inner,
                _,
            ) => resolve_fn_value(tcx, body, inner, depth - 1),
            Rvalue::Aggregate(kind, _) => match **kind {
                AggregateKind::Closure(did, _) => Some(did),
                _ => None,
            },
            _ => None,
        };
        if resolved.is_some() {
            return resolved;
        }
    }
    None
}

// ---------------------------------------------------------------------------
// The per-body facts query
// ---------------------------------------------------------------------------

fn push_unique(list: &mut Vec<LocalDefId>, def: LocalDefId) {
    if !list.contains(&def) {
        list.push(def);
    }
}

/// Provider of `trust_mir_once_body_facts`.
///
/// Trust: this borrow is unguarded BY CONSTRUCTION, exactly like
/// `trust_mir_direct_local_callees`: the only caller is the whole-crate walk in this
/// module, which demands the query only for bodies passing `is_eligible_body` — and
/// the accessor follow (`resolve_returned_static`) borrows OTHER bodies' MIR under
/// the same filter, through `with_body`, at the same pre-steal moment. Do NOT
/// "harden" it with `is_stolen()` — that is untracked by the query system and this
/// query is `cache_on_disk`, so the cached result would depend on query ORDER.
pub(crate) fn trust_mir_once_body_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> TrustOnceBodyFacts {
    with_body(tcx, def_id, |body| collect_body_facts(tcx, def_id, body))
}

/// The facts of one body, whichever MIR `with_body` handed over. `def` is the
/// body's own id — the seed of the accessor follow's borrow guard.
fn collect_body_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    body: &Body<'tcx>,
) -> TrustOnceBodyFacts {
    let mut facts = TrustOnceBodyFacts::default();
    if body.tainted_by_errors.is_some() {
        return facts;
    }
    for block in body.basic_blocks.iter() {
        let terminator = block.terminator();
        let (func, args, fn_span) = match &terminator.kind {
            TerminatorKind::Call { func, args, fn_span, .. }
            | TerminatorKind::TailCall { func, args, fn_span, .. } => (func, args, *fn_span),
            _ => continue,
        };
        let Some((callee, gen_args)) = func.const_fn_def() else {
            continue;
        };
        let diagnostic_name = tcx.get_diagnostic_name(callee);

        // Thread boundary: whatever this call receives runs on another thread.
        if diagnostic_name.is_some_and(is_thread_spawn) {
            for arg in args.iter() {
                if let Some(local) = fn_value_def(tcx, body, &arg.node).and_then(DefId::as_local) {
                    push_unique(&mut facts.spawned, local);
                }
            }
            continue;
        }

        // A local fn item passed as a VALUE may be invoked synchronously by the callee.
        for arg in args.iter() {
            if let ty::FnDef(did, _) = *arg.node.ty(&body.local_decls, tcx).kind()
                && let Some(local) = did.as_local()
                && !tcx.is_constructor(did)
                && tcx.is_mir_available(did)
            {
                push_unique(&mut facts.fn_value_edges, local);
            }
        }

        // A waiting call on a local cell static?
        let (kind, starts_initializer) = match diagnostic_name.and_then(waiting_method) {
            Some(method) => method,
            None => match lazy_deref_kind(tcx, callee, gen_args) {
                Some(kind) => (kind, false),
                None => continue,
            },
        };
        let Some(receiver) = args.first() else {
            continue;
        };
        let mut borrowed = vec![def];
        let Some(cell) =
            resolve_static_receiver(tcx, body, &receiver.node, OPERAND_WALK_DEPTH, &mut borrowed)
        else {
            continue;
        };
        if cell_kind_of_static(tcx, cell) != Some(kind) {
            continue;
        }
        let initializer = if starts_initializer {
            args.get(1).and_then(|f| fn_value_def(tcx, body, &f.node))
        } else {
            None
        };
        facts.waits.push(TrustOnceWaitSite {
            cell,
            kind,
            method: tcx.item_name(callee),
            span: fn_span,
            initializer,
        });
    }
    facts.fn_value_edges.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    facts.spawned.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    facts
}

// ---------------------------------------------------------------------------
// Lazy statics: the initializer lives in the static
// ---------------------------------------------------------------------------

/// The initializer body of a `LazyLock`/`LazyCell` static and the span to label as
/// its start (the `Lazy*::new(..)` call when it is visible, else the static's span).
fn lazy_static_initializer(tcx: TyCtxt<'_>, cell: LocalDefId) -> Option<(DefId, Span)> {
    let def_span = tcx.def_span(cell);
    let ty = tcx.type_of(cell).instantiate_identity().skip_norm_wip();
    let ty::Adt(_, args) = ty.kind() else {
        return None;
    };
    let f_ty = args.get(1)?.as_type()?;
    match f_ty.kind() {
        // `LazyLock<T, {closure}>` / `LazyLock<T, fn-item>`: the type names the body.
        ty::Closure(did, _) | ty::FnDef(did, _) => return Some((*did, def_span)),
        // A hand-written `FnOnce` impl (`#![feature(fn_traits)]`): its `call_once`.
        ty::Adt(..) => {
            let fn_once = tcx.lang_items().fn_once_trait()?;
            let call_once = tcx
                .associated_items(fn_once)
                .filter_by_name_unhygienic(sym::call_once)
                .next()?
                .def_id;
            let call_args = tcx.mk_args(&[f_ty.into(), tcx.types.unit.into()]);
            return match Instance::try_resolve(
                tcx,
                TypingEnv::fully_monomorphized(),
                call_once,
                call_args,
            ) {
                Ok(Some(Instance { def: InstanceKind::Item(did), .. })) => Some((did, def_span)),
                _ => None,
            };
        }
        _ => {}
    }
    // `F` is a fn pointer — the default `fn() -> T` — so the body behind it is visible
    // only in the static's own initializer MIR: `LazyLock::new(move _1)` where `_1` is
    // the coerced closure or fn item. `mir_for_ctfe` of a static is computed (and its
    // elaborated body stolen) by `check_crate`'s `eval_static_initializer` long before
    // this driver-level hook runs; demanding it here is a cache hit, never a steal of
    // something still needed.
    let body = tcx.mir_for_ctfe(cell.to_def_id());
    for block in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, args, fn_span, .. } = &block.terminator().kind
            && let Some((callee, _)) = func.const_fn_def()
            && matches!(
                tcx.get_diagnostic_name(callee),
                Some(sym::lazy_lock_new | sym::lazy_cell_new)
            )
            && let Some(arg) = args.first()
            && let Some(did) = resolve_fn_value(tcx, body, &arg.node, OPERAND_WALK_DEPTH)
        {
            return Some((did, *fn_span));
        }
    }
    // Fallback (e.g. `LazyLock::new` reached through a `const fn` helper): the evaluated
    // static's function provenance names the initializer.
    let alloc = tcx.eval_static_initializer(cell.to_def_id()).ok()?;
    for (_, prov) in alloc.inner().provenance().ptrs().iter() {
        if let GlobalAlloc::Function { instance } = tcx.global_alloc(prov.alloc_id()) {
            match instance.def {
                InstanceKind::Shim(ShimKind::ClosureOnce { closure, .. }) => {
                    return Some((closure, def_span));
                }
                InstanceKind::Item(did) | InstanceKind::Shim(ShimKind::Reify(did, _)) => {
                    return Some((did, def_span));
                }
                _ => {}
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// The whole-crate walk
// ---------------------------------------------------------------------------

/// One (cell, initializer) pair to walk from, with the span that starts it.
#[derive(Clone, Copy)]
struct Start {
    cell: LocalDefId,
    kind: TrustOnceCellKind,
    initializer: DefId,
    span: Span,
}

/// Trust: the driver-level entry point, called from `rustc_interface::passes::analysis`
/// on a front-end-clean crate BEFORE anything steals `optimized_mir`, and under no
/// other gate. Emits one hard error per (cell, initializer) pair whose initializer
/// can reach a wait on its own cell, in `DefIndex` order.
pub fn trust_check_once_initializer_reentrancy(tcx: TyCtxt<'_>) {
    // 1. Census — the pre-filter. One `type_of` per static; nothing else for a crate
    //    without a cell-typed static.
    let mut cells: Vec<(LocalDefId, TrustOnceCellKind)> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter_map(|def| cell_kind_of_static(tcx, def).map(|kind| (def, kind)))
        .collect();
    if cells.is_empty() {
        return;
    }
    cells.sort_unstable_by_key(|(def, _)| def.local_def_index.as_u32());

    // 2. Every body the walk may visit, in a deterministic order.
    let mut nodes: Vec<LocalDefId> =
        tcx.mir_keys(()).iter().copied().filter(|&def| is_eligible_body(tcx, def)).collect();
    nodes.sort_unstable_by_key(|def| def.local_def_index.as_u32());

    // 3. Every initializer start: a waiting call that names its initializer, plus the
    //    initializer each `Lazy*` static carries.
    let mut starts: Vec<Start> = Vec::new();
    for &node in &nodes {
        for site in tcx.trust_mir_once_body_facts(node).waits.iter() {
            if let Some(initializer) = site.initializer {
                starts.push(Start {
                    cell: site.cell,
                    kind: site.kind,
                    initializer,
                    span: site.span,
                });
            }
        }
    }
    for &(cell, kind) in &cells {
        if kind.is_lazy()
            && let Some((initializer, span)) = lazy_static_initializer(tcx, cell)
        {
            starts.push(Start { cell, kind, initializer, span });
        }
    }
    starts.sort_by_key(|start| {
        (
            start.cell.local_def_index.as_u32(),
            start.initializer.krate.as_u32(),
            start.initializer.index.as_u32(),
            start.span,
        )
    });
    starts.dedup_by_key(|start| (start.cell, start.initializer));

    // 4. Walk each start once.
    for start in starts {
        check_start(tcx, start);
    }
}

/// The synchronous edges out of `body`: the adjacency query's callees (direct calls,
/// resolved trait calls, closure ARGUMENTS) plus local fn items passed as arguments,
/// minus whatever the body hands to a `std::thread` spawn entry point.
fn synchronous_callees(
    tcx: TyCtxt<'_>,
    body: LocalDefId,
    facts: &TrustOnceBodyFacts,
) -> Vec<LocalDefId> {
    // The adjacency query borrows the elaborated MIR unguarded, so a coroutine — whose
    // elaborated body is already stolen (`with_body`) — gets the query's own extraction
    // applied to its `optimized_mir` instead of the query.
    let direct: Vec<LocalDefId> = if tcx.is_coroutine(body.to_def_id()) {
        crate::trust_verify::trust_direct_local_callees_of_body(tcx, tcx.optimized_mir(body))
    } else {
        tcx.trust_mir_direct_local_callees(body).to_vec()
    };
    let mut callees: Vec<LocalDefId> = direct
        .into_iter()
        .filter(|callee| !facts.spawned.contains(callee))
        .chain(facts.fn_value_edges.iter().copied())
        .collect();
    callees.sort_unstable_by_key(|callee| callee.local_def_index.as_u32());
    callees.dedup();
    callees
}

fn check_start(tcx: TyCtxt<'_>, start: Start) {
    // A cross-crate initializer (`C.get_or_init(String::new)`) is opaque.
    let Some(initializer) = start.initializer.as_local() else {
        return;
    };
    if !is_eligible_body(tcx, initializer) {
        return;
    }
    let mut parent: FxHashMap<LocalDefId, LocalDefId> = FxHashMap::default();
    let mut visited: FxHashSet<LocalDefId> = FxHashSet::default();
    visited.insert(initializer);
    let mut queue: VecDeque<LocalDefId> = VecDeque::from([initializer]);
    while let Some(body) = queue.pop_front() {
        let facts = tcx.trust_mir_once_body_facts(body);
        if let Some(site) = facts.waits.iter().find(|site| site.cell == start.cell) {
            report(tcx, start, initializer, body, &parent, site);
            return;
        }
        for callee in synchronous_callees(tcx, body, facts) {
            if is_eligible_body(tcx, callee) && visited.insert(callee) {
                parent.insert(callee, body);
                queue.push_back(callee);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

/// The span of the call in `from` that reaches `to` — a direct or resolved call, or
/// the argument that passes `to` as a closure/fn value. Error path only: re-scans the
/// MIR of `from` (`with_body`) once per hop.
fn edge_span(tcx: TyCtxt<'_>, from: LocalDefId, to: LocalDefId) -> Option<Span> {
    with_body(tcx, from, |body| {
        let typing_env = body.typing_env(tcx);
        for block in body.basic_blocks.iter() {
            let (func, args, fn_span) = match &block.terminator().kind {
                TerminatorKind::Call { func, args, fn_span, .. }
                | TerminatorKind::TailCall { func, args, fn_span, .. } => (func, args, *fn_span),
                _ => continue,
            };
            if let Some((callee, gen_args)) = func.const_fn_def() {
                let resolved = match Instance::try_resolve(tcx, typing_env, callee, gen_args) {
                    Ok(Some(instance)) => instance.def_id(),
                    _ => callee,
                };
                if resolved == to.to_def_id() {
                    return Some(fn_span);
                }
            }
            for arg in args.iter() {
                if fn_value_def(tcx, body, &arg.node) == Some(to.to_def_id()) {
                    return Some(arg.span);
                }
            }
        }
        None
    })
}

/// `ARMED.get_or_init(..)`, `*LAZY`, `LazyLock::force(&LAZY)`: the wait as the user
/// wrote it, for the call-path note.
fn render_wait(tcx: TyCtxt<'_>, site: &TrustOnceWaitSite) -> String {
    let cell = tcx.item_name(site.cell.to_def_id());
    let method = site.method;
    match site.kind {
        TrustOnceCellKind::LazyLock | TrustOnceCellKind::LazyCell => {
            if matches!(method, sym::deref | sym::deref_mut) {
                format!("*{cell}")
            } else {
                let ty =
                    if site.kind == TrustOnceCellKind::LazyLock { "LazyLock" } else { "LazyCell" };
                format!("{ty}::{method}(&{cell})")
            }
        }
        _ => format!("{cell}.{method}(..)"),
    }
}

fn report(
    tcx: TyCtxt<'_>,
    start: Start,
    initializer: LocalDefId,
    hit_body: LocalDefId,
    parent: &FxHashMap<LocalDefId, LocalDefId>,
    site: &TrustOnceWaitSite,
) {
    // The path from the initializer to the body holding the re-entrant wait.
    let mut chain = vec![hit_body];
    let mut current = hit_body;
    while let Some(&up) = parent.get(&current) {
        chain.push(up);
        current = up;
    }
    chain.reverse();
    debug_assert_eq!(chain[0], initializer);
    let hops: Vec<Span> =
        chain.windows(2).filter_map(|hop| edge_span(tcx, hop[0], hop[1])).collect();
    let mut path: Vec<String> =
        chain.iter().map(|def| format!("`{}`", tcx.def_path_str(def.to_def_id()))).collect();
    path.push(format!("`{}`", render_wait(tcx, site)));

    let cell = tcx.item_name(start.cell.to_def_id()).to_string();
    let failure = if start.kind.deadlocks() {
        "deadlocks — the initializing thread parks forever"
    } else {
        "panics (reentrant init)"
    };
    let reentry = if hit_body == initializer {
        format!("waiting on `{cell}` in it")
    } else {
        format!("calling `{}`", tcx.def_path_str(hit_body.to_def_id()))
    };
    let (hoist, peek) = match start.kind {
        TrustOnceCellKind::OnceLock | TrustOnceCellKind::OnceCell => (
            format!("`{cell}.get_or_init(|| v)` (or `{cell}.set(v)` before any reader)"),
            format!("{cell}.get()"),
        ),
        TrustOnceCellKind::Once => {
            (format!("`{cell}.call_once(|| use(v))`"), format!("{cell}.is_completed()"))
        }
        TrustOnceCellKind::LazyLock => (
            "a `OnceLock` set from that value before any reader".to_string(),
            format!("LazyLock::get(&{cell})"),
        ),
        TrustOnceCellKind::LazyCell => (
            "a `OnceCell` set from that value before any reader".to_string(),
            format!("LazyCell::get(&{cell})"),
        ),
    };
    tcx.dcx().emit_err(TrustOnceInitializerReentrancy {
        wait_span: site.span,
        start_span: (start.span != site.span).then_some(start.span),
        hops,
        cell_span: tcx.def_span(start.cell),
        cell,
        kind: start.kind.path().to_string(),
        failure: failure.to_string(),
        path: path.join(" -> "),
        reentry,
        hoist,
        peek,
    });
}
