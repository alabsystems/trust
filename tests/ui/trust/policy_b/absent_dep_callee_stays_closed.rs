//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The read_any soundness pin. Policy B tolerates the std stdout/stderr print
//! backend absent-callee row; it must NOT tolerate a NON-std absent callee.
//! `deref_raw` (a verify-off dependency doing `*p`) produces an absent-callee
//! panic-freedom row of the SAME class as `_print`, but its callee is
//! `policy_b_unverified_dep::deref_raw`, not std/core/alloc — so
//! `transport_row_is_std_print_dispatch` does not match it and the fail-closed
//! override stands. The served pack `acb08e761` once built this green (a
//! default-lane soundness hole, fixed on main); it MUST stay red.
extern crate policy_b_unverified_dep;
pub fn read_any(addr: usize) -> u32 {
    policy_b_unverified_dep::deref_raw(addr as *const u32)
}
