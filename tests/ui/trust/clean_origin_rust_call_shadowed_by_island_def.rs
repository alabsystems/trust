//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust) — the SILENT-PRECEDENCE hazard now speaks.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, VISIBILITY/IDENTITY.)
//!
//! Clean sees ONE crate-wide namespace. `mod a`'s island declares `def inc`
//! (`x + 2`); the crate root holds a Rust `fn inc` (`x + 1`) and an island whose
//! `twice_inc` writes `inc (inc x)`. The design rule refuses the `fn` as a
//! callee ("a bare name equal to any island `def` in another module … refuse
//! ALL bearers"), and records the "Clean sees one namespace" note — but that
//! note only ever surfaced through the elaborator's `Unknown identifier`, and
//! here the identifier is KNOWN: it resolves to `a`'s `def`. Measured
//! 2026-09-16 (probe-call 16c/16g): the crate built clean in either source
//! order and computed 9, with `function inc is never used` as the only output.
//!
//! Coherent with the kernel term, so not unsound — and different arithmetic
//! from the function written right beside the island, silently. It is now a
//! WARNING at the declaration that used the name, carrying the recorded
//! refusal and its options. A warning and not an error because the design
//! refuses the `fn` BEARERS, not the program: a cross-module Clean call is a
//! sanctioned shape (`clean_symbol_graph_forward_reference.rs`), and an author
//! who meant `a`'s `def` wrote a correct crate. Nothing is weakened: the `fn`
//! stays refused and the emitted body is still the kernel-gated Clean one —
//! which `main` asserts.
//!
//! Twin: `clean_origin_rust_call_shadowed_name_unused.rs` (same names, no use —
//! no warning).

mod a {
    clean {
        def inc (x : UInt64) : UInt64 := x + 2
    }
}

fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
//~^^ WARN `inc` in this Clean island names the island `def inc` declared in `a`, NOT the sibling Rust `fn inc`
//~| NOTE Clean sees one namespace: `inc` is declared as `fn` in `the crate root` and as island `def` in `a`

fn main() {
    // The Rust `fn` is ordinary Rust and still means what it says.
    assert_eq!(inc(5), 6);
    // The island's `inc` is `a`'s `def` (`x + 2`), exactly as the warning says:
    // 9, not the 7 a reader of the root module would expect.
    assert_eq!(twice_inc(5), 9);
    assert_eq!(a::inc(5), 7);
}
