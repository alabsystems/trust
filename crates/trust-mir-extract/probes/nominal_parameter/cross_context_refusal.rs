//! Expected E0277: never make live TyCtxt observation Send to another compiler.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
struct ForeignCompiler<'a, 'tcx>(&'a nominal_parameter::NominalParameterObservation<'tcx>);
impl rustc_driver::Callbacks for ForeignCompiler<'_, '_> {}
fn transfer<'tcx>(original: &nominal_parameter::NominalParameterObservation<'tcx>) {
    rustc_driver::run_compiler(&[], &mut ForeignCompiler(original));
}
fn main() {}
