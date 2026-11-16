//@ revisions: dbg2 dbg0
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[dbg2] compile-flags: -Cdebuginfo=2
//@[dbg0] compile-flags: -Cdebuginfo=0
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! VS-1 follow-up (2026-10-04), the loop clauses that must stay ACCEPTED by the
//! check that a loop clause binds the binding in scope at its loop
//! (`loop_clause_binding_shadow_not_in_scope.rs` holds the refusals).
//!
//! `closed_shadow`: the constant shadow `let x = 50u32;` is in a block that has
//! CLOSED before the loop, so the `x` in scope is the parameter, and its local
//! carries the parameter's own HIR identity. `copy_alias` (-Cdebuginfo=2 only;
//! at -Cdebuginfo=0 the clause was unknown before this check, too): CopyProp
//! removes `n`'s local and moves its row onto the parameter's, so the clause's
//! `n` is accepted on `n`'s own debug row. `mut_param`: a mutated parameter is
//! its own local. Each proved as pinned here on a stage 1 with VS-1 before this
//! check.
#![allow(unused_variables)]

pub fn closed_shadow(x: u32) -> u32
    //~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 4
    requires x < 10
{
    {
        let x = 50u32;
    }
    let mut i = 0u32;
    while i < 3
        invariant x < 10
    {
        i += 1;
    }
    i
}

#[cfg(dbg2)]
pub fn copy_alias(x: u32) -> u32 {
    //[dbg2]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3
    let n = x;
    let mut i = 0u32;
    while i < n
        invariant i <= n
    {
        i += 1;
    }
    i
}

pub fn mut_param(mut n: u32) -> u32
    requires n <= 100
{
    while n > 0
        invariant n <= 100
    {
        n -= 1;
    }
    n
}
