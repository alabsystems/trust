//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: contract_attr_foreign_tool_namespace_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `contract_attr_foreign_tool_namespace.rs` (CONTRACT-NS-1). It
//! failed before the fix on the stage 1 it was written against; on the main it landed
//! on, it pins the runtime result instead (passes before and after).
//!
//! The dependency is built with verification ON under the advisory policy, with
//! overflow checks on. Its `f` carries `#[clippy::requires = ".."]` whose text holds
//! the compiler-internal lowering prefix. This file, built `-Ztrust-verify=off`, calls
//! `f(300)`; `300 + 4_294_967_000` overflows `u32`.
//!
//! BEFORE, wave-14 stage 1 (main + wave 7, `scratchpad/stage1-w14`, measured
//! 2026-10-05): the dependency build printed `elided 1 kernel-certified overflow
//! checks` for `f`, and this program printed `4` (the wrapped sum) and exited 0.
//!
//! BEFORE, stage 1 of main `d7555335ab` (`scratchpad/stage1-w15main`, measured at
//! wave-16 integration): the dependency still reads the forged precondition and
//! proves the add under it, but ADVISORY-REQUIRES-CROSS-CRATE keeps the checks of a
//! `requires` body another crate can call, so nothing is elided and this program
//! panics with `attempt to add with overflow` (exit 101).
//!
//! AFTER (stage 1 of `dc15b882f6`, measured): the `clippy::` attribute is not a
//! contract, `f`'s add is refuted (a warning under advisory), nothing is elided, and
//! the program panics with `attempt to add with overflow` (exit 101).

extern crate contract_attr_foreign_tool_namespace_dep as dep;

fn main() {
    println!("{}", dep::f(std::hint::black_box(300)));
}
