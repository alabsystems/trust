//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libgen
//@ trust-ladder-row: Trust strict verification failed for `user_dep_generic_names_boom_undeclared::main`
//! OD-1 phase 2, the UNDECLARED twin of `user_dep_generic_names_boom_declared`:
//! `libgen` is not in the declared bundling scope, so its MIR is not read and no
//! discharge row is minted; the call to `f::<Boom>` keeps its fail-closed generic
//! absent-callee row and strict refuses on it. Going green means an undeclared
//! dependency instance lost its fail-closed row.
extern crate libgen;
fn main() { let _ = libgen::f(&libgen::Boom); }
