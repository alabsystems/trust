//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **W5 increment 7 — A LET-TEMP BODY WHOSE RESULT IS NOT A CALL IS REFUSED, WITH THE FIX.**
//! (`crates/trust-clean-origin/src/emit.rs`, `walk_let_spine`; the
//! `EmitRefusal::LetSpine` refusal, returned UNMASKED by the planner.)
//!
//! `let y := dbl x; x` binds a Rust call the body never uses and returns a bare
//! parameter. The let-temp lane evaluates the binding once — that is its
//! contract — but it emits only through the Rust-call chain, whose root must
//! be a callee application; a projection root with a dangling evaluated
//! binding is outside the fragment today. So the `def` is not minted (E0425 at
//! the call site, exactly as every other non-emittable Clean-origin `def`),
//! and the note carries the options: return the bound value, use it in a
//! Rust call, reorder the `let`s, or drop the unused binding. The fragment
//! boundary is a measurement (v7/D2), the refusal a fix with options (v7/D3).
//!
//! check-fail: the refusal is a resolver-time mint decision, so `--emit
//! metadata` already sees it.

#![allow(dead_code)]

fn dbl(x: u64) -> u64 {
    x.wrapping_add(x)
}

clean {
    def drop_it (x : UInt64) : UInt64 := let y := dbl x; x
}

fn main() {
    let _ = drop_it(3);
    //~^ ERROR cannot find function `drop_it`
    //~| NOTE never used by the result
}
