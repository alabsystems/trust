// Compile-fail control: these guards own thread-local freeze authority.
// Compile with the coherent native MirExtract component pair. Both Send bounds
// must reject with E0277; accepting either is a policy-lifetime regression.
#![feature(rustc_private)]
extern crate trust_mir_extract;
use trust_mir_extract::ctfe_reentrancy::{Freeze, LayoutQuerySafetyContext};
fn require_send<T: Send>() {}
fn main() {
    require_send::<Freeze>();
    require_send::<LayoutQuerySafetyContext<'static>>();
}
