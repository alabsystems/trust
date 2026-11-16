//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libgen
//@ trust-ladder-xcrate-declare: libgen
//@ trust-ladder-row: Trust instance discharge not established for `user_dep_generic_names_boom_declared::main`
//! OD-1 PHASE 2 (2026-10-05). The open dispatch lives in the DEPENDENCY's generic
//! `libgen::f`; this binary creates the instance `f::<Boom>`, and `<Boom as Tr>::m`
//! panics. The site is re-derived here from `libgen`'s encoded MIR and the
//! instance's discharge row must FAIL (the callee is re-derived, D4-A, and is not
//! panic-free). Before phase 2 this row refused only on the call's generic
//! absent-callee row, which a correct `f::<Good>` shares; refusing for any reason
//! but the discharge means a named panicking dependency instance went uncharged.
extern crate libgen;
fn main() { let _ = libgen::f(&libgen::Boom); }
