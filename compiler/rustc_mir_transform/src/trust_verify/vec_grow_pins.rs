//! Trust (std-call-summaries, 2026-10-11): the compiler's pins for the bridge's
//! `Vec<u8>` grow summaries (`trust_ir_bridge::CompilerAllocGrowPins`).
//!
//! The bridge discharges the capacity-overflow panic of a `Vec<u8>` grow call
//! (`<Vec<u8> as io::Write>::{write, write_all}`, `Vec::<u8>::extend_from_slice`)
//! under the MAX_LIVE_ALLOC_BYTES TCB axiom (docs/TCB.md). That discharge rests on
//! facts the bridge cannot read off its input, so they are decided here, where
//! `TyCtxt` is, and carried on a channel only the compiler-context entry points can
//! fill:
//!
//! * THE OOM GATE. The summary treats allocation failure as an abort. In this tree
//!   that is true exactly when no allocation-error hook can be installed: std's
//!   `rust_oom` calls the hook set by `std::alloc::set_alloc_error_hook`, which "may
//!   choose to panic" (and the unwind is catchable), and there is no `-Zoom=panic`
//!   any more. `crate_graph_may_install_alloc_error_hook` is the existing,
//!   metadata-backed decision of that question (docs/TCB.md, "Allocation failure
//!   aborts — unless an allocation-error hook is installed"). Since 2026-10-12 it
//!   also answers `true` when a crate other than the real `std` defines an
//!   `#[alloc_error_handler]` (which replaces the abort route and may panic).
//!   Before 2026-10-11 the grow summary consulted no such gate.
//! * THE IDENTITY of `<alloc::vec::Vec<u8, alloc::alloc::Global>>::extend_from_slice`
//!   as a `trust_types::CalleeIdentity` (`DefId` plus generic-argument digest, the
//!   same function the extractor stamps every call with:
//!   `trust_mir_extract::callee_identity_for`). The verifier lane renders the real
//!   std `Vec` receiver as `Ty::Seq`, which drops the allocator and carries no
//!   `len` field, so neither the allocator nor the pointer width is visible to the
//!   bridge there. This identity carries the method (the real `alloc`'s inherent
//!   `Vec::extend_from_slice`, found from the `Vec` diagnostic item of a
//!   sysroot-resident `alloc`, never by a rendered path), the element (`u8`) and
//!   the allocator (`Global`, by its lang item, resident in the same `alloc`). It
//!   is minted only on a target whose pointer width is 64 (the axiom is a 64-bit
//!   fact) and only when the oom gate holds.
//!
//! Every miss returns the fail-closed default: the bridge then keeps the blanket
//! may-panic row exactly as before.

use rustc_attr_ir::lang_items::LangItem;
use rustc_middle::ty::{self, TyCtxt};

use super::crate_graph_may_install_alloc_error_hook;

/// The pins for this compilation. Cheap: a handful of queries, no body walk.
pub(super) fn compiler_alloc_grow_pins(tcx: TyCtxt<'_>) -> trust_ir_bridge::CompilerAllocGrowPins {
    let alloc_failure_aborts = !crate_graph_may_install_alloc_error_hook(tcx);
    let vec_u8_global_extend_from_slice = (alloc_failure_aborts
        && tcx.data_layout.pointer_size().bits() == 64)
        .then(|| vec_u8_global_extend_from_slice_identity(tcx))
        .flatten();
    if std::env::var_os("TRUST_VEC_GROW_PIN_DEBUG").is_some() {
        eprintln!(
            "[VEC_GROW_PIN] alloc_failure_aborts={alloc_failure_aborts} \
             vec_u8_global_extend_from_slice={vec_u8_global_extend_from_slice:?}"
        );
    }
    trust_ir_bridge::CompilerAllocGrowPins { alloc_failure_aborts, vec_u8_global_extend_from_slice }
}

/// The instance identity of `<Vec<u8, Global>>::extend_from_slice` in the
/// compiler's own `alloc`, or `None` on any surprise (fail-closed).
fn vec_u8_global_extend_from_slice_identity(
    tcx: TyCtxt<'_>,
) -> Option<trust_types::CalleeIdentity> {
    let vec = tcx.get_diagnostic_item(rustc_span::sym::Vec)?;
    // The diagnostic item is a source attribute; residency is the identity
    // (SEQ-RESIDENCY-1): the `alloc` this compiler ships, by name and artifact.
    if tcx.crate_name(vec.krate).as_str() != "alloc"
        || !trust_mir_extract::is_real_sysroot_crate(tcx, vec.krate)
    {
        return None;
    }
    let global = tcx.lang_items().get(LangItem::GlobalAlloc)?;
    if global.krate != vec.krate {
        return None;
    }
    // Exactly ONE inherent `extend_from_slice` on `Vec`; more than one is a
    // `core`/`alloc` shape this code was not written for.
    let mut found = None;
    for &impl_did in tcx.inherent_impls(vec) {
        for &item in tcx.associated_item_def_ids(impl_did) {
            if tcx.item_name(item).as_str() == "extend_from_slice" {
                if found.is_some() {
                    return None;
                }
                found = Some(item);
            }
        }
    }
    let item = found?;
    // `impl<T: Clone, A: Allocator> Vec<T, A> { pub fn extend_from_slice(&mut self,
    // other: &[T]) }`: two impl parameters, none of its own, and a safe signature.
    let generics = tcx.generics_of(item);
    if generics.count() != 2 || !generics.own_params.is_empty() {
        return None;
    }
    if !tcx.fn_sig(item).skip_binder().safety().is_safe() {
        return None;
    }
    let global_ty = ty::Ty::new_adt(tcx, tcx.adt_def(global), ty::GenericArgs::empty());
    let args = tcx.mk_args(&[tcx.types.u8.into(), global_ty.into()]);
    trust_mir_extract::callee_identity_for(tcx, item, args)
}

/// Trust (std-call-summaries P2 review, item 5): run the panic-free intrinsic mint's
/// negative self-test (`trust_mir_extract::panic_free_intrinsic_mint_selftest`) once
/// per process when `TRUST_PANIC_FREE_MINT_SELFTEST=1`, and turn every failing case
/// into a compile error. Diagnostic-only: it grants nothing, and with the variable
/// unset it does nothing. `tests/ui/trust/panic_free_intrinsic_mint_selftest.rs` runs
/// it, so deleting one of the mint's gates or making its fallback walker answer
/// `true` is a red UI test.
pub(super) fn run_panic_free_mint_selftest_once(tcx: TyCtxt<'_>) {
    use std::sync::atomic::{AtomicBool, Ordering};
    static RAN: AtomicBool = AtomicBool::new(false);
    if std::env::var_os("TRUST_PANIC_FREE_MINT_SELFTEST").is_none()
        || RAN.swap(true, Ordering::Relaxed)
    {
        return;
    }
    for failure in trust_mir_extract::panic_free_intrinsic_mint_selftest(tcx) {
        tcx.dcx().err(format!("Trust panic-free intrinsic mint self-test failed: {failure}"));
    }
}
