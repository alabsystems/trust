//! Expected E0277: live observation is not a Clone/cached source identity.
#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
fn require_clone<T: Clone>() {}
fn main() {
    require_clone::<nominal_parameter::NominalParameterObservation<'static>>();
}
