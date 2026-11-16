//! Rustc's layout of the tuple types a FAITHFUL extraction names (2026-09-29).
//!
//! `trust_types::Ty::Tuple` carries no layout, so the bridge had no byte offset for
//! a tuple field on any lane: it guessed `index * size_of(field)` until 2026-09-28,
//! and has emitted an unknown offset since. This module records rustc's own
//! `layout_of` answer for every concrete tuple the faithful lane lowers, and
//! `extract_function_with_purpose_observed` stamps the table onto the function as
//! `VerifiableFunction::tuple_layouts` — the same per-extraction, thread-local shape as
//! the R0 datatype-definition table (`ty_convert::DatatypeDefScope`).
//!
//! FAITHFUL LANE ONLY, for the reason `Ty::Adt::layout` is: a non-empty table is
//! hash-visible, so filling it on a verifier lane would move shipped pins.
//!
//! THE QUERY IS CYCLE-SAFE (and `extractor_layout_of` / `resolution_may_reenter` apply
//! the same funnel to every other layout and resolution of the extractor while it runs
//! inside `mir_built`). This runs inside `mir_built`, where a `layout_of` that
//! normalizes through an unrevealed opaque re-enters a query on the stack (E0391).
//! The guard below is the #48 funnel (`crate::ctfe_reentrancy::
//! layout_query_is_reentrant_safe_deep`, which the THIR producer's
//! `cycle_safe_layout_of` reads too): the type's own flags, then the fields of every
//! LOCAL ADT it names anywhere, and the `layout_of` precondition (no escaping bound
//! vars). Declining only leaves a tuple without a row — its field addresses then name
//! no offset — and never guesses.

use std::cell::RefCell;

use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_types::fx::FxHashMap;
use trust_types::{LayoutTarget, TupleLayoutInfo, TupleLayouts, Ty as TrustTy};

#[derive(Default)]
struct Collector {
    /// A scope is open: rows recorded outside one would never be stamped.
    active: bool,
    target: Option<LayoutTarget>,
    rows: Vec<TupleLayoutInfo>,
    /// Exact `(interned rust_ty, lowered TrustTy)` pairs already recorded in this
    /// scope. Skipping exact repeats avoids redundant `layout_of` queries and
    /// `serde_json::to_string` deduplication in `TupleLayouts::from_rows`, while
    /// distinct `rust_ty` preimages sharing one `lowered` key still both push rows
    /// so `TupleLayouts::from_rows` preserves conflict detection.
    seen_exact: FxHashMap<usize, Vec<TrustTy>>,
}

thread_local! {
    static COLLECTOR: RefCell<Collector> = RefCell::new(Collector::default());
}

/// RAII scope for ONE function's tuple-layout table: cleared on entry and on drop,
/// so a table never inherits a row from the previously extracted function.
pub(crate) struct TupleLayoutScope(());

impl TupleLayoutScope {
    pub(crate) fn begin() -> Self {
        crate::ty_convert::bump_extraction_scope_epoch();
        COLLECTOR.with(|c| *c.borrow_mut() = Collector { active: true, ..Collector::default() });
        TupleLayoutScope(())
    }
}

impl Drop for TupleLayoutScope {
    fn drop(&mut self) {
        crate::ty_convert::bump_extraction_scope_epoch();
        COLLECTOR.with(|c| *c.borrow_mut() = Collector::default());
    }
}

/// The table recorded so far in the current scope (conflicting rows for one tuple
/// are dropped by `TupleLayouts::from_rows`).
pub(crate) fn collected_tuple_layouts() -> TupleLayouts {
    COLLECTOR.with(|c| {
        let mut c = c.borrow_mut();
        c.seen_exact.clear();
        if c.rows.is_empty() && c.target.is_none() {
            return TupleLayouts::default();
        }
        TupleLayouts::from_rows(c.target.take(), std::mem::take(&mut c.rows))
    })
}

/// Record rustc's layout of `rust_ty`, which the faithful lane lowered to `lowered`.
/// Declines silently (no row) off the faithful lane, outside a scope, for a type the
/// query cannot safely be asked about, and for any layout answer that does not have
/// one entry per field.
pub(crate) fn record_tuple_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
    rust_ty: ty::Ty<'tcx>,
    lowered: &TrustTy,
) {
    if !crate::ty_convert::faithful_scalars() {
        return;
    }
    let (ty::Tuple(rust_fields), TrustTy::Tuple(fields)) = (rust_ty.kind(), lowered) else {
        return;
    };
    let ty_id = crate::interned_ty_identity(rust_ty);
    let skip_or_inactive = typing_env.is_none()
        || rust_fields.len() != fields.len()
        || COLLECTOR.with(|c| {
            let c = c.borrow();
            !c.active
                || c.seen_exact
                    .get(&ty_id)
                    .is_some_and(|seen| seen.iter().any(|prev| prev == lowered))
        });
    if skip_or_inactive {
        return;
    }
    let Some(layout) = cycle_safe_layout_of(tcx, rust_ty) else { return };
    if layout.fields.count() != fields.len() {
        return;
    }
    let mut field_sizes = Vec::with_capacity(fields.len());
    let mut field_aligns = Vec::with_capacity(fields.len());
    for field in rust_fields.iter() {
        let Some(field_layout) = cycle_safe_layout_of(tcx, field) else { return };
        field_sizes.push(field_layout.size.bytes());
        field_aligns.push(field_layout.align.bytes());
    }
    let lowered_owned = lowered.clone();
    let row = TupleLayoutInfo {
        tuple: lowered_owned.clone(),
        size: layout.size.bytes(),
        align: layout.align.bytes(),
        field_offsets: (0..fields.len()).map(|i| layout.fields.offset(i).bytes()).collect(),
        field_sizes,
        field_aligns,
    };
    COLLECTOR.with(|c| {
        let mut c = c.borrow_mut();
        c.seen_exact.entry(ty_id).or_default().push(lowered_owned);
        c.target.get_or_insert_with(|| {
            let target = &tcx.sess.target;
            LayoutTarget {
                triple: target.llvm_target.to_string(),
                pointer_size: u32::from(target.pointer_width / 8),
                little_endian: matches!(target.endian, rustc_abi::Endian::Little),
            }
        });
        c.rows.push(row);
    });
}

/// `layout_of`, declined wherever the THIR producer's #48 funnel declines it. The type
/// is then monomorphic, so it is asked with an EMPTY parameter environment: `layout_of`
/// normalizes its environment's clauses in the post-analysis mode too, and a body's
/// clauses can name an opaque (`ConstArgHasType(N, Bar)` for a `const N: Bar` with a
/// type-alias-impl-trait `Bar`, measured on
/// `tests/ui/type-alias-impl-trait/const_generic_type.rs`), whose `type_of` that reveal
/// demands from inside `mir_built`.
fn cycle_safe_layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<ty::layout::TyAndLayout<'tcx>> {
    if !crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty)
        || ty.has_escaping_bound_vars()
    {
        return None;
    }
    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty)).ok()
}

/// `layout_of` for every other site of the extractor. Inside `mir_built`
/// (`ctfe_reentrancy::frozen`) it is [`cycle_safe_layout_of`]: `layout_of` normalizes
/// in the post-analysis typing mode whatever environment it is handed, so it REVEALS
/// opaque types, and the unguarded sites re-entered an opaque's `type_of` — measured on
/// `tests/ui/coroutine/issue-87142.rs`: `layout_of(NonNull<<() as Provider>::Coro>)` from
/// the faithful struct-layout fill, inside `mir_built` of the coroutine that defines
/// `Coro` (E0391). Outside `mir_built` — the verifier, at `optimized_mir` time, outside
/// every type-system query — it is `layout_of` itself, unchanged. A declined layout is
/// each site's existing "no layout" answer.
pub(crate) fn extractor_layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    te: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<ty::layout::TyAndLayout<'tcx>> {
    if crate::ctfe_reentrancy::frozen() {
        cycle_safe_layout_of(tcx, ty)
    } else {
        tcx.layout_of(te.as_query_input(ty)).ok()
    }
}

/// Must an `Instance::try_resolve` of `def_id` over `args` be declined on this thread now?
/// Inside `mir_built`, for arguments the #48 funnel would not lay out: resolution selects
/// in the post-analysis typing mode (`codegen_select_candidate`), so it reveals opaque
/// types as `layout_of` does, and resolving a coroutine's method can demand its by-move
/// body (`mir_built` of a coroutine). And for a TRAIT item whose selection meets an impl
/// where-clause naming an opaque, however clean `args` are (`impl Prim for u8 where Tait:
/// Debug`: the codegen-mode selection normalizes it and reveals `Tait`, inside `mir_built`
/// of `Tait`'s own defining body an E0391 on valid Rust — OPAQUE-IMPL-WHERE-LEAK-1,
/// [`crate::ctfe_reentrancy::resolution_reveal_free`]). A declined resolution is each
/// site's existing "unresolved" answer.
pub(crate) fn resolution_may_reenter<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    crate::ctfe_reentrancy::frozen()
        && (!args
            .types()
            .all(|ty| crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty))
            || !crate::ctfe_reentrancy::resolution_reveal_free(
                tcx,
                ty::ParamEnv::empty(),
                def_id,
                args,
            ))
}
