//! Trust (IOERROR-PAYLOAD-1, 2026-10-27): a `dyn core::error::Error` whose every
//! possible concrete type is a sysroot type.
//!
//! `std::io::Error` holds, in its `Custom` representation, a
//! `Box<dyn error::Error + Send + Sync>`. Every walk that asks "can this type's
//! code reach code this compilation does not verify"
//! (`ty_reaches_foreign_user_code`, the drop-reach and call-reach walks of
//! `sysroot_drop_reach`) answers "yes" at any `dyn`, so every std routine
//! instantiated at `io::Error` and every drop of an `io::Result` is a masked
//! fail-closed source. MEASURED (2026-10-27, `docs/DECISION_QUEUE.md`
//! IOERROR-PAYLOAD-1): `let _ = append(path, bytes)` (a local fn returning
//! `io::Result<()>`) and `OpenOptions::new()...open(path)?` were refused for that
//! reason alone, and the claude-code-alab harness, which has no dependency at all,
//! lost a dozen functions to it.
//!
//! THE FACT. A value of type `dyn Error + Send + Sync` is made only by an unsizing
//! coercion from a type `T: Error + Send + Sync`. So its concrete type is a type
//! that implements `core::error::Error`. When
//!
//!  1. every crate of the graph other than the one being compiled is `core`,
//!     `alloc` or `std`, or a crate resident in this compiler's own sysroot that the
//!     crate being compiled does not name (std's private implementation crates):
//!     no dependency, no `proc_macro`, no `test`, no `rustc_private` crate, and
//!  2. the crate being compiled has no impl of `core::error::Error`,
//!
//! every such `T` is a sysroot type: a sysroot crate's non-generic `Error` impl, or
//! a sysroot generic impl at some type arguments (`PoisonError<L>`,
//! `SendError<L>`; the blanket `&T`/`Box<T>`/`Arc<T>` impls bottom out in one of
//! those). Its destructor and its `Error`/`Display`/`Debug` methods are sysroot
//! code, and what it does with a local type argument is that type's own code —
//! a local body this crate verifies as its own root. Condition
//!
//!  3. no local item is `#[trust::skip]` (a closure or impl inside one included),
//!     and every function of every local impl of a sysroot trait is held to this
//!     crate's verification (`local_item_is_held_to_this_rule`)
//!
//! keeps the last clause true: a payload at a local type runs that type's
//! `Drop::drop`, through a sysroot impl that formats it (`IntoInnerError<W>`'s
//! derived `Debug`) its `Debug`/`Display`, through a sysroot destructor that calls
//! its argument (`BufWriter<W>` flushes through `W::write`, `vec::Splice<I>` pulls
//! `I::next`, which can be a local closure) that code — each a local body this
//! crate verifies — and sysroot code.
//!
//! So under 1-3 (and with no global allocator or allocation-error handler of this
//! crate) the trait object reaches only the sysroot and this crate's verified
//! bodies, which is exactly what the masking walk and the CALL walk ask
//! ([`dyn_is_closed_error_object`]); what they grant is a tolerated
//! (runtime-checked) row, never a proof. The destructor walk
//! (`sysroot_drop_reach`'s `ReachMode::SysrootOnly`) does NOT take the rule: it
//! credits a closed drop as panic-free sysroot code and opens at every local
//! body, and a payload's drop can run local code (`BufWriter<W>`, `Splice<I>`
//! above) whatever destructors the crate defines — so no crate-level condition
//! short of "no local code at all" would stand in for its walk. Nor does the
//! global-allocator walk, and the masking walk's DROP and `main`-termination
//! consumers ask it under [`withheld`], so they answer as on main. Anything else
//! — a `dyn` whose principal is not `core::error::Error`, one with a non-auto
//! additional bound, any graph with a dependency, any local `Error` impl, any
//! `#[trust::skip]` item — keeps every walk's answer as it was. The verdict is one
//! per compilation.
//!
//! THE SECOND HALF (measured on the first build of this rule). In this toolchain
//! `io::Error` lives in core, which has no allocator: its `Custom` holds the payload
//! as `NonNull<dyn Error + Send + Sync>` beside two `fn` pointers alloc stores at
//! construction (`error_drop`, `outer_drop`), and `kind()` reads std's OS error
//! table (`OsFunctions`, three `fn` pointers) out of a global. Closing the `dyn`
//! alone moved no verdict: the walks still met those pointers. So, in the same
//! graph and when the crate being compiled does not enable `core_io_internals`
//! (the unstable feature behind the only two ways to store such a pointer), the
//! masking walk takes those `fn` pointer fields as closed
//! ([`io_error_fn_pointer_field_is_closed`]) and the reach walks follow a call
//! through `error_drop`/`outer_drop` inside core's `Custom`/`CustomOwner`
//! destructors as the drop of a `Box<T>` — alloc's `drop_box_raw::<T>`, the only
//! function the library stores there ([`io_error_drop_pointer_box_pointee`]).

use std::cell::{Cell, RefCell};

use rustc_attr_ir::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Symbol;
use rustc_span::def_id::{DefId, LOCAL_CRATE};

thread_local! {
    /// The crate-graph verdict, per compilation (keyed by the local crate's
    /// `StableCrateId`).
    static GRAPH_VERDICT: RefCell<Option<(u64, bool)>> = const { RefCell::new(None) };
    /// How many [`withheld`] scopes are open: while any is, the rule answers "not
    /// closed" everywhere, as on main.
    static WITHHELD: Cell<u32> = const { Cell::new(0) };
}

/// Run `f` with the rule WITHHELD: every question it asks of this module answers
/// as on main (a `dyn Error` and core's `io::Error` `fn` pointers are open).
///
/// The rule is a fact about what a CALL can reach, for the walks that grant a
/// call a tolerated row. Some consumers of the masking walk ask the opposite
/// question — a DROP credited as panic-free (`foundational_destructor_foreign_
/// reach`, shared by the masked-glue scan and the memory-safe drop arm) or
/// `main`'s `Termination` dispatch, where "reaches foreign or dynamic code" is
/// what DEFERS an error type to the runtime-checked entry row (`entry_
/// termination_dispatch_rows`, `error_layer_defers_to_entry_row`) — and for them
/// "closed" would either credit a drop the destructor walk does not, or move an
/// `io::Error` out of the entry row into a stricter `Debug` gate it fails. They
/// run under this scope, so their answers are main's. A caller must use a memo
/// only inside one scope: the masking walk's memo would carry an answer across.
pub(super) fn withheld<R>(f: impl FnOnce() -> R) -> R {
    struct Close;
    impl Drop for Close {
        fn drop(&mut self) {
            WITHHELD.with(|depth| depth.set(depth.get() - 1));
        }
    }
    WITHHELD.with(|depth| depth.set(depth.get() + 1));
    let _close = Close;
    f()
}

/// Is `ty` a `dyn core::error::Error (+ auto traits)` trait object in a crate graph
/// where every value of it is a sysroot type (the module doc's conditions 1-3)?
pub(super) fn dyn_is_closed_error_object<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::Dynamic(predicates, ..) = ty.kind() else { return false };
    let Some(error_trait) = error_trait_did(tcx) else { return false };
    if !super::crate_is_authentic_core(tcx, error_trait.krate) {
        return false;
    }
    let mut principal_is_error = false;
    for predicate in predicates.iter() {
        match predicate.skip_binder() {
            ty::ExistentialPredicate::Trait(trait_ref) => {
                if trait_ref.def_id != error_trait {
                    return false;
                }
                principal_is_error = true;
            }
            ty::ExistentialPredicate::AutoTrait(_) => {}
            // An associated-type binding names a trait with one; `Error` has none.
            ty::ExistentialPredicate::Projection(_) => return false,
        }
    }
    principal_is_error && crate_graph_error_payloads_are_sysroot(tcx)
}

/// Core's `io::error` internals whose `fn` pointer fields the rule speaks for.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IoInternal {
    /// `core::io::error::Custom`: `error_drop`, `outer_drop`.
    Custom,
    /// `core::io::error::CustomOwner`, whose destructor calls `outer_drop`.
    CustomOwner,
    /// `core::io::error::OsFunctions`: the OS error table std installs.
    OsFunctions,
}

/// Which core `io::error` internal `did` is: an ADT of authentic core at that
/// path (the path is read inside an authenticated crate, never across crates).
fn core_io_error_internal(tcx: TyCtxt<'_>, did: DefId) -> Option<IoInternal> {
    if !super::crate_is_authentic_core(tcx, did.krate) {
        return None;
    }
    match trust_mir_extract::safe_def_path_str(tcx, did).as_str() {
        "core::io::error::Custom" => Some(IoInternal::Custom),
        "core::io::error::CustomOwner" => Some(IoInternal::CustomOwner),
        "core::io::error::OsFunctions" => Some(IoInternal::OsFunctions),
        _ => None,
    }
}

/// Only sysroot code fills the `fn` pointers of core's `io::error` internals:
/// the closed graph of [`crate_graph_error_payloads_are_sysroot`], and the crate
/// being compiled does not enable `core_io_internals`, the unstable feature behind
/// `Custom::from_raw` and `Error::from_raw_os_error_with_functions` — the only
/// ways to store a pointer there. In the library those are called only by
/// alloc's `custom_owner_from_box` (storing its `drop_box_raw::<dyn Error + Send +
/// Sync>` and `drop_box_raw::<Custom>`) and std's `Error::from_raw_os_error`
/// (std's `FUNCTIONS` table); core's own `OsFunctions::DEFAULT` holds core
/// closures.
fn io_internals_filled_by_sysroot_only(tcx: TyCtxt<'_>) -> bool {
    crate_graph_error_payloads_are_sysroot(tcx)
        && !tcx
            .features()
            .enabled_lib_features()
            .iter()
            .any(|feature| feature.gate_name.as_str() == "core_io_internals")
}

/// Trust (IOERROR-PAYLOAD-1, second half, 2026-10-27): may the masking walk take a
/// `fn` pointer FIELD of the sysroot ADT `adt` as closed? Only for core's
/// `io::error::Custom` and `OsFunctions`, in a graph where only sysroot code fills
/// them ([`io_internals_filled_by_sysroot_only`]). In this toolchain `io::Error`
/// lives in core and drops its custom payload through `Custom`'s two pointers, so
/// without this the `dyn Error` closure never changes an answer.
pub(super) fn io_error_fn_pointer_field_is_closed(tcx: TyCtxt<'_>, adt: DefId) -> bool {
    matches!(core_io_error_internal(tcx, adt), Some(IoInternal::Custom | IoInternal::OsFunctions))
        && io_internals_filled_by_sysroot_only(tcx)
}

/// Trust (IOERROR-PAYLOAD-1, second half): in `method`, the `drop` of core's
/// `Custom` or `CustomOwner`, a call through `fn_ptr_ty = unsafe fn(NonNull<T>)` is
/// alloc's `drop_box_raw::<T>` — `drop(Box::<T>::from_non_null(ptr))` — whenever
/// only sysroot code fills those pointers. Returns `T`, so the walk can follow the
/// drop of a `Box<T>` instead of opening at the pointer. `None` for any other
/// body, pointer type or graph.
pub(super) fn io_error_drop_pointer_box_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    fn_ptr_ty: Ty<'tcx>,
) -> Option<Ty<'tcx>> {
    let impl_did = tcx.trait_impl_of_assoc(method)?;
    if !tcx.is_lang_item(tcx.impl_trait_id(impl_did), LangItem::Drop) {
        return None;
    }
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    let ty::Adt(self_def, _) = self_ty.kind() else { return None };
    if !matches!(
        core_io_error_internal(tcx, self_def.did()),
        Some(IoInternal::Custom | IoInternal::CustomOwner)
    ) || !io_internals_filled_by_sysroot_only(tcx)
    {
        return None;
    }
    if !matches!(fn_ptr_ty.kind(), ty::FnPtr(..)) {
        return None;
    }
    let sig = tcx.instantiate_bound_regions_with_erased(fn_ptr_ty.fn_sig(tcx));
    let [arg] = sig.inputs() else { return None };
    let ty::Adt(non_null, non_null_args) = arg.kind() else { return None };
    if !tcx.is_lang_item(non_null.did(), LangItem::NonNull)
        || !super::crate_is_authentic_core(tcx, non_null.did().krate)
        || !sig.output().is_unit()
    {
        return None;
    }
    Some(non_null_args.type_at(0))
}

/// `core::error::Error` by its diagnostic item. rustc predefines no `sym` for it,
/// and adding one to `rustc_span` would rebuild every compiler crate for one
/// lookup; the name is interned here instead (callers also authenticate the
/// defining crate as core, `crate_is_authentic_core`).
#[allow(rustc::symbol_intern_string_literal)]
fn error_trait_did(tcx: TyCtxt<'_>) -> Option<rustc_span::def_id::DefId> {
    tcx.get_diagnostic_item(Symbol::intern("Error"))
}

/// The module doc's conditions 1-3, once per compilation.
fn crate_graph_error_payloads_are_sysroot(tcx: TyCtxt<'_>) -> bool {
    if WITHHELD.with(|depth| depth.get()) > 0 {
        return false;
    }
    let key = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    if let Some(verdict) =
        GRAPH_VERDICT.with(|cell| cell.borrow().and_then(|(k, v)| (k == key).then_some(v)))
    {
        return verdict;
    }
    let verdict = compute_graph_verdict(tcx);
    if super::env_flag_enabled("TRUST_VANILLA_DEBUG") {
        eprintln!("[IOERROR_PAYLOAD] crate-graph dyn Error payloads are sysroot: {verdict}");
    }
    GRAPH_VERDICT.with(|cell| *cell.borrow_mut() = Some((key, verdict)));
    verdict
}

fn compute_graph_verdict(tcx: TyCtxt<'_>) -> bool {
    // 1. Every crate is `core`/`alloc`/`std`, or resident in this compiler's sysroot
    //    AND reached only through them (std's private implementation crates). A
    //    crate this crate names directly (a dependency, `proc_macro`, `test`, a
    //    `rustc_private` crate), or one with no recorded edge, fails it.
    let graph_is_std_alone = tcx.crates(()).iter().all(|&krate| {
        let did = krate.as_def_id();
        trust_mir_extract::def_is_in_real_sysroot_crate(tcx, did)
            || (trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, did)
                && tcx.extern_crate(krate).is_some_and(|edge| !edge.is_direct()))
    });
    if !graph_is_std_alone {
        return false;
    }
    // 1'. No global allocator or allocation-error handler of this crate: a payload's
    //     drop frees through the global allocator, and the walks that ask whether a
    //     body reaches a user allocator (`body_global_allocator_reach`) never take
    //     this rule; this keeps the two questions from meeting at all.
    if tcx.has_global_allocator(LOCAL_CRATE) || tcx.has_alloc_error_handler(LOCAL_CRATE) {
        return false;
    }
    let local_impls = tcx.all_local_trait_impls(());
    // 2. No local impl of `core::error::Error`.
    let Some(error_trait) = error_trait_did(tcx) else { return false };
    if local_impls.get(&error_trait).is_some_and(|impls| !impls.is_empty()) {
        return false;
    }
    // 3. No local body is `#[trust::skip]` (`item_has_trust_skip_attr` reads the
    //    item's ancestors, so a closure inside a skipped function counts), and every
    //    function of every local impl of a sysroot trait is held to this crate's own
    //    verification (`local_item_is_held_to_this_rule`: local, with MIR, not
    //    `#[trust::skip]`), the impl itself not `#[trust::skip]`. A sysroot payload
    //    at a local type runs that type's `Drop`, its `Debug`/`Display`
    //    (`IntoInnerError<W>`'s derived `Debug` formats `W`) and the trait methods a
    //    sysroot destructor calls (`BufWriter<W>`'s `W::write`) only through such
    //    impls, and a local closure (`vec::Splice<Map<_, F>>` calls `F`) only
    //    through a body this crate owns.
    if tcx.hir_body_owners().any(|owner| super::item_has_trust_skip_attr(tcx, owner.to_def_id())) {
        return false;
    }
    for (trait_did, impls) in local_impls {
        if trait_did.is_local()
            || !trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, *trait_did)
        {
            continue;
        }
        for impl_did in impls.iter().map(|local| local.to_def_id()) {
            if super::item_has_trust_skip_attr(tcx, impl_did) {
                return false;
            }
            for &item in tcx.associated_item_def_ids(impl_did) {
                if matches!(tcx.def_kind(item), DefKind::AssocFn)
                    && !super::local_item_is_held_to_this_rule(tcx, item)
                {
                    return false;
                }
            }
        }
    }
    true
}
