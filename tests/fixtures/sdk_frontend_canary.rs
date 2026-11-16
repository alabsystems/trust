// Trust: SDK dependency smoke only; verification is explicitly disabled.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;

pub fn callbacks_are_available(_: &mut (dyn rustc_driver::Callbacks + Send)) {}
pub fn compiler_is_available(_: &rustc_interface::interface::Compiler) {}
pub fn context_is_available<'tcx>(_: rustc_middle::ty::TyCtxt<'tcx>) {}
