// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Source evidence for a shared receiver snapshot, independent of its layout.
//!
//! A local lifetime-GAT field can prevent the conservative layout walk from
//! answering even when the referent is concrete and Freeze. Ask the existing
//! leak-free trait solver the actual Freeze goal; never infer it from a mapped
//! struct or invent a field offset. Ambiguity and hidden-type proposals refuse.

use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use trust_mir_extract::ctfe_reentrancy as cr;

pub(super) fn source_receiver_snapshot_is_freeze<'tcx>(
    tcx: TyCtxt<'tcx>,
    pointee: Ty<'tcx>,
) -> bool {
    // A receiver read from a signature may still name its enclosing binder.
    // Regions affect neither Freeze nor the stored value; type/const binders
    // remain and fail the ordinary source guard.
    let pointee = ty::fold_regions(tcx, pointee, |_, _| tcx.lifetimes.re_erased);
    if !cr::layout_query_is_reentrant_safe(pointee)
        || pointee.has_non_region_param()
        // The transitive source-field walk already guards other analysis-time
        // trait/normalization questions against evaluating a non-leaf constant.
        || cr::needs_drop_may_evaluate_non_leaf_constant(tcx, pointee)
    {
        return false;
    }
    let Some(freeze) = tcx.lang_items().freeze_trait() else {
        return false;
    };
    cr::trait_holds_leak_free(tcx, ty::ParamEnv::empty(), pointee, freeze)
}
