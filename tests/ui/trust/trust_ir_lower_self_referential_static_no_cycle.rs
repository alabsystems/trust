//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Regression for the trust-ir producer's SELF-REFERENTIAL STATIC query cycle
//! (E0391). Sibling of `trust_ir_lower_rpit_no_cycle.rs`: same failure class
//! (a pre-borrowck demand from inside `mir_built` re-entering `mir_built`),
//! different demand chain.
//!
//! `lower_static_ref` (wave-SR2) reads a static's value with
//! `tcx.eval_static_initializer`, which demands `mir_built` for that static's
//! initializer. When the body being lowered IS that initializer — as in
//! `static FOO: Foo = Foo { foo: Some(&FOO) }` — the demand closes a cycle on
//! rustc's own query stack: a FATAL error, not the recoverable eval error the
//! call site assumed. The original code asserted the opposite in a comment
//! ("a `static` is a module-level ITEM whose initializer body cannot reference
//! the function being lowered"), which is false for exactly this shape.
//!
//! The hole shipped latent: `Option<&'static Foo>` failed enum registration,
//! so the whole expression collapsed to the opaque lane and the `&FOO` was
//! never reached. Wave-EP admitted thin-pointer enum payloads and the corpus
//! surfaced it as a `flag_induced_fail` on
//! `tests/ui/consts/static-cycle-error.rs`.
//!
//! The fix is the `LOWERING_BODIES` thread-local reentrancy stack in
//! `trust-thir-lower`: every producer frame pushes the `DefId` it is lowering,
//! and `lower_static_ref` declines (recorded coverage gap, no value invented)
//! rather than issue a query for anything already on it. A stack rather than a
//! single "current body" field because the cycle can be MUTUAL, closing across
//! two nested producer frames — see `mutual` below.

pub struct Foo {
    pub foo: Option<&'static Foo>,
}

// Direct self-reference: lowering FOO's initializer reaches `&FOO`.
pub static FOO: Foo = Foo { foo: Some(&FOO) };

// Mutual reference: lowering A reaches `&B`, whose own `mir_built` re-enters
// the producer and reaches `&A` — the cycle closes across two frames, so a
// single current-body check would miss it and only the stack catches it.
pub struct Node {
    pub next: Option<&'static Node>,
}
pub static A: Node = Node { next: Some(&B) };
pub static B: Node = Node { next: Some(&A) };

// A non-cyclic static read through the same path must keep working — the guard
// must decline only on genuine reentrancy, not on every static.
pub static PLAIN: u64 = 7;
pub fn read_plain() -> u64 {
    PLAIN
}

fn main() {}
