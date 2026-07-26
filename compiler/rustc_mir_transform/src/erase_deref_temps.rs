//! This pass converts all `DerefTemp` locals into normal temporaries
//! and turns their `CopyForDeref` rvalues into normal copies.

use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

struct EraseDerefTempsVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for EraseDerefTempsVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, _: Location) {
        if let &mut Rvalue::CopyForDeref(place) = rvalue {
            // We do *NOT* want a retag here! This assignment might copy a mutable reference we
            // can't actually copy, we just need it temporarily to create another pointer.
            *rvalue = Rvalue::Use(Operand::Copy(place), WithRetag::No)
        }
    }

    fn visit_local_decl(&mut self, _: Local, local_decl: &mut LocalDecl<'tcx>) {
        if local_decl.is_deref_temp() {
            let info = local_decl.local_info.as_mut().unwrap_crate_local();
            **info = LocalInfo::Boring;
        }
    }
}

pub(super) struct EraseDerefTemps;

impl<'tcx> crate::MirPass<'tcx> for EraseDerefTemps {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Trust: `CopyForDeref` rvalues are only ever produced by the Derefer
        // pass, assigning into fresh `DerefTemp`-flagged locals — and
        // `local_info` is still `ClearCrossCrate::Set` at this phase (cleared
        // later, in the runtime cleanup passes). Bodies without a deref temp
        // (the large majority) skip the whole-body visit.
        if !body.local_decls.iter().any(|decl| decl.is_deref_temp()) {
            return;
        }
        EraseDerefTempsVisitor { tcx }.visit_body_preserves_cfg(body);
    }

    fn is_required(&self) -> bool {
        true
    }
}
