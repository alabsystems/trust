//! Expected E0451: even actual compiler types/IDs cannot construct this record.
#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::LocalDefId;
fn forge<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    argument: usize,
    source_ty: ty::Ty<'tcx>,
    declaration: ty::AdtDef<'tcx>,
) -> nominal_parameter::NominalParameterObservation<'tcx> {
    nominal_parameter::NominalParameterObservation {
        tcx,
        owner,
        argument,
        source_ty,
        declaration,
        _not_send_sync: Default::default(),
    }
}
fn main() {}
