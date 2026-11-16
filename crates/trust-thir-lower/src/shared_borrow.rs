//! Shared place identity and the source condition required to copy a referent.
//!
//! A representable non-Freeze local uses the existing whole-lifetime promotion
//! machinery. Its shared borrow is the promoted slot itself. Other fresh
//! snapshots require affirmative source Freeze evidence; a mapped scalar or
//! aggregate spelling cannot establish the absence of interior mutability.
//! A whole tracked owned temporary can instead be materialized at its first
//! borrow, provided drop placement proves its unique home on the finished body.
//! That admission never applies to a snapshot of an existing referent.

use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Span;

use crate::{LowerCx, is_freeze_without_reveal};

pub(super) fn source_snapshot_is_freeze<'tcx>(tcx: TyCtxt<'tcx>, pointee: Ty<'tcx>) -> bool {
    // Unknown generic shapes cannot borrow a concrete instance's admission.
    !pointee.has_non_region_param()
        && is_freeze_without_reveal(tcx, pointee, ty::TypingEnv::fully_monomorphized())
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    pub(super) fn require_shared_snapshot_freeze(&mut self, span: Span, pointee: Ty<'tcx>) -> bool {
        let pointee = self.monomorphize(pointee);
        if source_snapshot_is_freeze(self.tcx, pointee) {
            true
        } else {
            self.unsupported.push((format!("{span:?}"), "Borrow(snapshot requires Freeze)"));
            false
        }
    }
}
