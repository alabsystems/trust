//! Expected E0451: a caller-supplied real Body cannot construct query custody.
#![feature(rustc_private)]
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate trust_mir_extract;
extern crate trust_types;
#[path = "../../src/nominal_body.rs"]
mod nominal_body;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
pub use trust_mir_extract::{ctfe_reentrancy, extract_function_faithful};
fn forge<'tcx>(
    nominal: nominal_parameter::NominalParameterObservation<'tcx>,
    body: &'tcx rustc_middle::mir::Body<'tcx>,
    argument_local: rustc_middle::mir::Local,
    source_attributes: &'tcx [rustc_attr_ir::Attribute],
) -> nominal_body::NominalBodyObservation<'tcx> {
    nominal_body::NominalBodyObservation { nominal, body, argument_local, source_attributes }
}
fn main() {}
