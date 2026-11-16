//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: const_param_slice_len_name_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `const_param_slice_len_name.rs` (SLICE-LEN-NAME-1, the
//! const-parameter half).
//!
//! The dependency is built with verification ON under the advisory policy, with
//! overflow checks on. Its `dec::<N>` subtracts 1 from a const parameter named
//! `n__slice_len`. This file, built `-Ztrust-verify=off`, instantiates
//! `dec::<-128>` from the dependency's MIR; `-128 - 1` overflows `i8`.
//!
//! BEFORE (stage 1 of `dc15b882f6` at `scratchpad/stage1-w16`, measured
//! 2026-10-05): the dependency build printed `TRUST_ELIDE: elided 1
//! kernel-certified overflow checks` for `dec` and for `dec_joined`, and this
//! program printed the wrapped `127` and exited 0.
//!
//! AFTER: the parameter's symbol is not a length, the subtraction is refuted (a
//! warning under advisory), nothing is elided, and the program panics with
//! `attempt to subtract with overflow` (exit 101).

extern crate const_param_slice_len_name_dep as dep;

fn main() {
    println!("{}", dep::dec::<{ -128 }>());
}
