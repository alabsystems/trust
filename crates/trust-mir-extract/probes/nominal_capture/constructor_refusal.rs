//! Expected E0451: supplied extractor output cannot construct live capture custody.
#![feature(rustc_private)]
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate trust_mir_extract;
extern crate trust_types;
#[path = "../../src/nominal_body.rs"]
mod nominal_body;
#[path = "../../src/nominal_capture.rs"]
mod nominal_capture;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
pub use trust_mir_extract::{ctfe_reentrancy, extract_function_faithful};
fn forge<'tcx>(
    source: nominal_body::NominalBodyObservation<'tcx>,
    function: trust_types::VerifiableFunction,
) -> nominal_capture::FaithfulNominalCapture<'tcx> {
    nominal_capture::FaithfulNominalCapture { source, function }
}
fn main() {}
