use rustc_attr_ir::find_attr;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_span::sym;
use tracing::trace;

use super::ConstCx;
use crate::check_consts::check::Checker;
use crate::check_consts::rustc_allow_const_fn_unstable;

/// Returns `true` if we should use the more precise live drop checker that runs after drop
/// elaboration.
pub fn checking_enabled(ccx: &ConstCx<'_, '_>) -> bool {
    // Const-stable functions must always use the stable live drop checker...
    if ccx.enforce_recursive_const_stability() {
        // ...except if they have the feature flag set via `rustc_allow_const_fn_unstable`.
        return rustc_allow_const_fn_unstable(
            ccx.tcx,
            ccx.body.source.def_id().expect_local(),
            sym::const_precise_live_drops,
        );
    }

    ccx.tcx.features().const_precise_live_drops()
}

/// Look for live drops in a const context.
///
/// This is separate from the rest of the const checking logic because it must run after drop
/// elaboration.
pub fn check_live_drops<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
    let ccx = ConstCx::new(tcx, body);
    if ccx.const_kind.is_none() {
        return;
    }

    if find_attr!(tcx, body.source.def_id(), RustcDoNotConstCheck) {
        return;
    }

    if !checking_enabled(&ccx) {
        return;
    }

    // I know it's not great to be creating a new const checker, but I'd
    // rather use it so we can deduplicate the error emitting logic that
    // it contains.
    let mut checker = Checker::new(&ccx);

    for (bb, block) in body.basic_blocks.iter_enumerated() {
        trace!("visit_basic_block_data: bb={:?} is_cleanup={:?}", bb, block.is_cleanup);

        // Ignore drop terminators in cleanup blocks.
        if block.is_cleanup {
            continue;
        }

        let terminator = block.terminator();
        let location = body.terminator_loc(bb);
        trace!("visit_terminator: terminator={:?} location={:?}", terminator, location);

        if let mir::TerminatorKind::Drop { place: dropped_place, .. } = &terminator.kind {
            checker.check_drop_terminator(
                *dropped_place,
                location,
                terminator.source_info.span,
            );
        }
    }
}
