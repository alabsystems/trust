//! Explicit D17 per-instance MIR TEST-ORACLE. No emitted body, flip or proof authority.
//!
//! The default-off tracked option is fenced by the driver to a diagnostic lane. Its incumbent
//! is the independently retained raw `mir_built` body, normalized by rustc at THIS instance's
//! concrete args. Its subject is the actual `Lowered` about to enter instance admission, with
//! all its original producer flags/callee/provenance records. Neither is replaced by a registry's
//! generic green body. Any missing input, unsupported construct or mismatch refuses this lane.
//! The private clone also removes only drop scaffolding whose instantiated place type needs no
//! drop. The unchanged comparator's symbolic normalizations remain its comparison boundary.

use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};

use crate::mir_differential::{self, DerivedVerdict};
use crate::{InstanceRefusal, Lowered};

fn refused(detail: impl Into<String>) -> InstanceRefusal {
    InstanceRefusal::OracleRefused(format!("per-instance MIR seam TEST-ORACLE: {}", detail.into()))
}

/// `false` means no measurement was requested for this body, never agreement.
/// Only a successful comparison returns `true`; callers cannot supply a verdict.
pub(crate) fn compare<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    lowered: &Lowered,
) -> Result<bool, InstanceRefusal> {
    // Deliberately before even reading the oracle table: ordinary production admission has
    // no added MIR dependency. Monomorphic bodies are relinked from their handoff, not appended.
    if !tcx.sess.opts.unstable_opts.trust_ir_instance_seam_test
        || instance.args.iter().all(|arg| arg.as_region().is_some())
    {
        return Ok(false);
    }
    if instance.args.has_non_region_param() {
        return Err(refused("instance args are not concrete"));
    }
    let def = instance.def_id().as_local().ok_or_else(|| refused("nonlocal source body"))?;
    let built = tcx
        .trust_instance_seam_sibling(def)
        .ok_or_else(|| refused("missing or duplicate-poisoned raw built sibling"))?;
    let mut built = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, built.clone()),
        )
        .map_err(|error| refused(format!("built sibling normalization failed: {error:?}")))?;
    if built.has_non_region_param() {
        return Err(refused("normalized built sibling still has a non-region parameter"));
    }
    normalize_drop_free_scaffolding(tcx, &mut built)?;
    // Negative controls alter only a private clone of the real source-produced subject. A
    // failed mutation cannot be an inert green test. No mutated module can reach the assembler.
    let mutated;
    let subject = if let Some(mode) =
        tcx.sess.opts.unstable_opts.trust_test_instance_seam_mutation.as_deref()
    {
        mutated = mutate_subject(lowered, mode)?;
        &mutated
    } else {
        lowered
    };
    let snapshot = trust_mir_extract::extract_function_faithful(tcx, &built);
    let report = mir_differential::compare_derived(tcx, def, subject, &built, Some(&snapshot));
    accept_report(
        report.verdict,
        &report.detail,
        report.markers_exact,
        tcx.sess.emit_lifetime_markers(),
        &report.markers_detail,
    )?;
    // A mutation request is a negative control, never an admitting oracle mode. Even if a future
    // comparator normalization erases it, it must not publish a measured-success row.
    if tcx.sess.opts.unstable_opts.trust_test_instance_seam_mutation.is_some() {
        return Err(refused("negative control unexpectedly agreed"));
    }
    Ok(true)
}

/// Raw generic MIR retains drop scaffolding before monomorphization: for example,
/// `ident<T>(x: T) -> T { x }` moves `_1` into `_0`, then has a `Drop(_1)` terminator.
/// After THIS instance's normalization, a place whose concrete type needs no drop has no
/// destructor to execute or unwind from. Follow only that terminator's ordinary target in
/// this private oracle clone. Refuse every remaining real or unresolved drop here, including
/// cleanup/dead blocks outside the comparator's reachable traversal. The raw sibling is untouched.
fn normalize_drop_free_scaffolding<'tcx>(
    tcx: TyCtxt<'tcx>,
    built: &mut Body<'tcx>,
) -> Result<(), InstanceRefusal> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let locals = &built.local_decls;
    for block in built.basic_blocks.as_mut().iter_mut() {
        let Some(terminator) = block.terminator.as_mut() else { continue };
        let TerminatorKind::Drop { place, target, .. } = &terminator.kind else { continue };
        let ty = place.ty(locals, tcx).ty;
        if ty.has_non_region_param() {
            return Err(refused("built sibling has an unresolved drop place type"));
        }
        if ty.needs_drop(tcx, typing_env) {
            return Err(refused("built sibling has a drop-bearing place"));
        }
        terminator.kind =
            TerminatorKind::Goto { target: *target, loop_hint_attrs: Default::default() };
    }
    Ok(())
}

fn accept_report(
    verdict: DerivedVerdict,
    detail: &str,
    markers_exact: bool,
    lifetime_markers: bool,
    markers_detail: &str,
) -> Result<(), InstanceRefusal> {
    if verdict != DerivedVerdict::DerivedAgreed {
        return Err(refused(format!("{verdict:?}: {detail}")));
    }
    // Preserve the comparator's exact marker channel wherever codegen emits those markers.
    if lifetime_markers && !markers_exact {
        return Err(refused(format!("storage-marker channel: {markers_detail}")));
    }
    Ok(())
}

fn mutate_subject(lowered: &Lowered, mode: &str) -> Result<Lowered, InstanceRefusal> {
    let mut subject = lowered.clone();
    let constant = subject
        .module
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.body)
        .find(|n| {
            matches!(
                n.inst,
                trust_ir::Inst::Const {
                    ty: trust_ir::Ty::Bool,
                    value: trust_ir::Constant::Bool(_)
                }
            )
        });
    let Some(node) = constant else {
        return Err(refused("negative control requires an actual source-produced bool constant"));
    };
    match (&mut node.inst, mode) {
        (trust_ir::Inst::Const { value: trust_ir::Constant::Bool(value), .. }, "bool-constant") => {
            *value = !*value;
        }
        (_, "undef-constant") => node.inst = trust_ir::Inst::Undef { ty: trust_ir::Ty::Bool },
        _ => return Err(refused("invalid negative-control mode")),
    }
    Ok(subject)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_actual_agreement_can_be_disclosed() {
        assert!(accept_report(DerivedVerdict::DerivedAgreed, "equal", true, true, "exact").is_ok());
        for verdict in [DerivedVerdict::DerivedMismatch, DerivedVerdict::DerivedUnsupported] {
            let failure = accept_report(verdict, "retained reason", true, false, "exact");
            assert!(matches!(failure, Err(InstanceRefusal::OracleRefused(why))
                if why.contains("retained reason") && why.contains(&format!("{verdict:?}"))));
        }
        assert!(
            accept_report(DerivedVerdict::DerivedAgreed, "equal", false, true, "different")
                .is_err()
        );
        // At O0 marker erasure is part of the existing comparator's documented boundary.
        assert!(
            accept_report(DerivedVerdict::DerivedAgreed, "equal", false, false, "different")
                .is_ok()
        );
    }
}
