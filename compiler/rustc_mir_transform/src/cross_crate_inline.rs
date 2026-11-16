use rustc_attr_ir::{InlineAttr, find_attr};
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::*;
use rustc_middle::query::Providers;
use rustc_middle::ty::TyCtxt;
use rustc_session::config::{InliningThreshold, OptLevel};
use rustc_span::{bug, sym};

use crate::{clean_origin_mir, inline, pass_manager as pm};

pub(super) fn provide(providers: &mut Providers) {
    providers.cross_crate_inlinable = cross_crate_inlinable;
}

fn cross_crate_inlinable(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    // Clean definitions outside the Compiler F1 rlib lane remain cross-crate
    // inlinable: their gated MIR travels and the importer produces its own
    // copy through readmission. Synthetic definitions have no HIR body, so
    // consult the registry before the ordinary attribute-driven policy.
    if clean_origin_mir::is_clean_origin(tcx, def_id) {
        // The Compiler F1 rlib inventories public synthetic definitions and
        // emits their native symbols. Preserve those bytes across a Rust
        // consumer instead of asking its backend to compile another copy.
        // The collector re-admits imported Clean definitions before linking;
        // the metadata's gated MIR remains available for CTFE/readmission.
        if matches!(
            tcx.sess.opts.unstable_opts.codegen_backend.as_deref(),
            Some("trust-cg" | "trust_cg")
        ) && tcx.sess.trust_cg_frontend_is_trust_ir()
            && tcx.sess.trust_cg_f1_backend_is_compiler()
            && tcx.crate_types().contains(&rustc_structures::CrateType::Rlib)
        {
            return false;
        }
        return true;
    }
    let codegen_fn_attrs = tcx.codegen_fn_attrs(def_id);
    // If this has an extern indicator, then this function is globally shared and thus will not
    // generate cgu-internal copies which would make it cross-crate inlinable.
    if codegen_fn_attrs.contains_extern_indicator() {
        return false;
    }

    // This just reproduces the logic from Instance::requires_inline.
    match tcx.def_kind(def_id) {
        DefKind::Ctor(..) | DefKind::Closure | DefKind::SyntheticCoroutineBody => return true,
        DefKind::Fn | DefKind::AssocFn => {}
        _ => return false,
    }

    // From this point on, it is valid to return true or false.
    if tcx.sess.opts.unstable_opts.cross_crate_inline_threshold == InliningThreshold::Always {
        return true;
    }

    if find_attr!(tcx, def_id, RustcIntrinsic) {
        // Intrinsic fallback bodies are always cross-crate inlineable.
        // To ensure that the MIR inliner doesn't cluelessly try to inline fallback
        // bodies even when the backend would implement something better, we stop
        // the MIR inliner from ever inlining an intrinsic.
        return true;
    }

    if let hir::Constness::Const { always: true } = tcx.constness(def_id) {
        // Comptime functions only exist during const eval and can never be passed
        // to codegen. The const eval MIR pipeline also doesn't inline anything at all.
        return false;
    }

    // Obey source annotations first; this is important because it means we can use
    // #[inline(never)] to force code generation.
    match codegen_fn_attrs.inline {
        InlineAttr::Never => return false,
        InlineAttr::Hint | InlineAttr::Always | InlineAttr::Force { .. } => return true,
        _ => {}
    }

    // If the crate is likely to be mostly unused, use cross-crate inlining to defer codegen until
    // the function is referenced, in order to skip codegen for unused functions. This is
    // intentionally after the check for `inline(never)`, so that `inline(never)` wins.
    if tcx.sess.opts.unstable_opts.hint_mostly_unused {
        return true;
    }

    let reliable_f16 = tcx.sess.config.contains(&(sym::target_has_reliable_f16, None));
    let reliable_f128 = tcx.sess.config.contains(&(sym::target_has_reliable_f128, None));
    if !reliable_f16 || !reliable_f128 {
        let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
        for ty in
            sig.inputs().skip_binder().iter().chain(std::iter::once(&sig.output().skip_binder()))
        {
            // FIXME(f16,f128): in order to avoid crashes building `core`, inline on targets that
            // have issues to skip codegen if the function is not used.
            if (!reliable_f16 && ty == &tcx.types.f16) || (!reliable_f128 && ty == &tcx.types.f128)
            {
                return true;
            }
        }
    }

    // Don't do any inference when incremental compilation is enabled; the additional inlining that
    // inference permits also creates more work for small edits.
    if tcx.sess.opts.incremental.is_some() {
        return false;
    }

    // Don't do any inference if codegen optimizations are disabled and also MIR inlining is not
    // enabled. This ensures that we do inference even if someone only passes -Zinline-mir,
    // which is less confusing than having to also enable -Copt-level=1.
    let inliner_will_run =
        pm::should_run_pass(&inline::Inline, &pm::PassCtx::for_body(tcx, def_id.to_def_id()))
            || inline::ForceInline::should_run_pass_for_callee(tcx, def_id.to_def_id());
    if matches!(tcx.sess.opts.optimize, OptLevel::No) && !inliner_will_run {
        return false;
    }

    if !tcx.is_mir_available(def_id) {
        return false;
    }

    let threshold = match tcx.sess.opts.unstable_opts.cross_crate_inline_threshold {
        InliningThreshold::Always => return true,
        InliningThreshold::Sometimes(threshold) => threshold,
        InliningThreshold::Never => return false,
    };

    let mir = tcx.optimized_mir(def_id);
    // Each basic block has at least one terminator, which counts as 1 statement.
    if mir.basic_blocks.len() > threshold {
        return false;
    }

    // The threshold that we check here balances the desire to make more things
    // inlinable cross crates against the growth in incremental CGU size that happens when too many
    // things in the sysroot are made inlinable.
    // Permitting calls causes the size of some incremental CGUs to grow, because more functions are
    // made inlinable out of the sysroot or dependencies.
    // Assert terminators are similar to calls, but do not have the same impact on compile time, so
    // those are just treated as statements.
    // A threshold exists at all because we don't want to blindly mark a huge function as inlinable.
    let mut statements = 0;
    for block in mir.basic_blocks.iter() {
        for statement in &block.statements {
            // Don't count StorageLive/StorageDead in the inlining cost.
            match statement.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
                _ => {
                    statements += 1;
                    if statements > threshold {
                        return false;
                    }
                }
            }
        }

        statements += 1;
        if statements > threshold {
            return false;
        }

        match &block.terminator().kind {
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(mir, tcx).ty;
                if !ty.is_trivially_pure_clone_copy() {
                    return false;
                }
            }
            TerminatorKind::Call { func, .. } => {
                // We track calls because they make our function not a leaf (and in theory, the
                // number of calls indicates how likely this function is to perturb other CGUs).
                // But there are a handful of intrinsics such as raw_eq that should not block
                // cross-crate-inlining. Adding a broad exception for all intrinsics benchmarks well
                // and seems more sustainable than an ever-growing list of intrinsics to ignore.
                if let Some((fn_def_id, _)) = func.const_fn_def()
                    && find_attr!(tcx, fn_def_id, RustcIntrinsic)
                {
                    continue;
                }
                return false;
            }
            TerminatorKind::TailCall { .. } | TerminatorKind::UnwindResume => {
                return false;
            }
            TerminatorKind::Assert { unwind, .. } | TerminatorKind::InlineAsm { unwind, .. } => {
                if let UnwindAction::Cleanup(_) = unwind {
                    return false;
                }
            }
            TerminatorKind::Return
            | TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindTerminate(_) => {}
            kind @ (TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop) => {
                bug!("{kind:?} should not be in runtime MIR");
            }
        }
    }

    true
}
