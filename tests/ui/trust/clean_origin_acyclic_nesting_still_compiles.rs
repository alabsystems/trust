//@ needs-trust-verify
//@ revisions: verifyoff verifyon
//@[verifyoff] compile-flags: -Ztrust-verify=off
//@[verifyon] compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr

//! **THE CAPABILITY THE CYCLE GUARD MUST NOT COST.**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`,
//! `callee_reaches_a_gate_on_this_stack`; 2026-09-25.)
//!
//! Legal acyclic nesting: `def a` calls `fn f`; `fn g` calls `a`; a SECOND
//! declaration `def b` also calls `f`. Rust calls into Clean, Clean calls into
//! Rust, two declarations share a callee — and nothing leads back into a
//! declaration whose gate is running. Every one of these must keep compiling.
//!
//! THIS FIXTURE EXISTS BECAUSE A GUARD ALREADY BROKE IT ONCE. An earlier
//! reachability guard asked `trust_clean_origin_references` of every callee
//! unconditionally, which forces `mir_built` — and a Clean-origin def is a
//! synthetic HIR owner, so that dead-ends in `typeck`'s
//! `can't type-check body of DefId(..)` `span_bug!`. This program ICEd; the
//! measurement reverted the guard. The shipped guard never expands a
//! Clean-origin node (nor a const-context body, whose elaborated MIR
//! `inner_mir_for_ctfe` steals).
//!
//! Both revisions, for the same reason as the refusal fixtures: the lanes differ
//! in demand order, so a capability check in one lane is not a capability check.

fn f(x: u64) -> u64 {
    x.wrapping_add(1)
}

clean {
    def a (x : UInt64) : UInt64 := f x
}

fn g(x: u64) -> u64 {
    a(x)
}

clean {
    def b (x : UInt64) : UInt64 := f (f x)
}

fn main() {
    let _v = g(1).wrapping_add(b(2));
}
