//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust) — the AMBIGUOUS-CALLEE refusal, with options.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, Diagnostics.)
//!
//! Clean sees ONE crate-wide namespace. Two modules each hold an island and
//! a sibling `fn inc`, so two admissible callees bear one bare name — and
//! rather than pick one (which module's `inc` would `a`'s island mean?) the
//! mint refuses ALL bearers. Neither island can then name `inc`: each gets
//! the elaborator's `Unknown identifier: inc` with the ambiguity note and the
//! options (rename one; give the callee a distinct bare name; cite from
//! proof position).
//!
//! What is NOT claimed: no callee was declared, nothing was minted, nothing
//! was emitted — a refusal, never a guess.

mod a {
    pub fn inc(x: u64) -> u64 {
        x.wrapping_add(1)
    }
    clean {
        def twice_inc (x : UInt64) : UInt64 := inc (inc x)
    }
//~^^ ERROR Unknown identifier: inc
//~| NOTE Clean sees one namespace: `inc` is declared as `fn` in `a` and `b`
//~| NOTE rename one of them
}

mod b {
    pub fn inc(x: u64) -> u64 {
        x.wrapping_add(2)
    }
    clean {
        def thrice_inc (x : UInt64) : UInt64 := inc (inc (inc x))
    }
//~^^ ERROR Unknown identifier: inc
//~| NOTE Clean sees one namespace: `inc` is declared as `fn` in `a` and `b`
}

fn main() {
    let _ = a::inc(1) + b::inc(1);
    let _ = crate::a::twice_inc(5);
    //~^ ERROR cannot find function `twice_inc` in module `crate::a`
}
