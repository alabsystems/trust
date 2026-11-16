//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Refuted 2026-09-16 (type-walk lens, fold mask). The bridge folds every
//! absent/foreign panic source of a body into ONE aggregate row named after a
//! single representative callee. Here the representative is the tolerated std
//! print backend, and `dep::boom` — a verify-off dependency function that panics
//! on 3, with NO verdict anywhere — was co-folded under it: this program built
//! exit 0 with the note "it can dispatch into no user code" and panicked in the
//! dependency, while `dep::boom(3); println!()` (same calls, other order) was
//! refused. `function_has_masked_fail_closed_dispatch` re-derives the masked
//! source from MIR and withholds BOTH tolerances (print backend and vanilla
//! sysroot callee) on it.
extern crate policy_b_unverified_dep as dep;
fn main() {
    println!("hi");
    dep::boom(3);
}
