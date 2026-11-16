//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust): a sibling `fn` named like a Clean PRELUDE constant
//! (Trust, 2026-09-28).**
//!
//! This is the silent-precedence hazard of
//! `clean_origin_rust_call_shadowed_by_island_def.rs`, but here the name's holder
//! is the prelude rather than an island `def` in another module. The design of
//! record (`docs/design/2026-09-13-lean-calls-rust-lane.md`, VISIBILITY/IDENTITY)
//! refuses a callee whose bare name the prelude holds. The refusal note only ever
//! surfaced through `Unknown identifier`, and `id` does resolve: to the prelude's
//! `id`. Measured on stage 1 before this fix: the crate built and ran with NO
//! diagnostic, and printed `call_id(5) = 5` against the Rust `id(5) = 6`.
//!
//! It is now a WARNING at the declaration that used the name, for the same
//! reason the island-`def` case is a warning. `id` meaning the prelude's `id` is
//! ordinary Lean, and the author may have meant exactly that. Nothing is
//! weakened: the `fn` stays refused, and `main` asserts the prelude meaning.
//!
//! The negative twin is `keep`: a sibling `fn not` that no island mentions draws
//! no warning (the warning keys on USE, read from the kernel terms).

fn id(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[allow(dead_code)]
fn not(b: bool) -> bool {
    b
}

clean {
    def call_id (x : UInt64) : UInt64 := id x
    def keep (b : Bool) : Bool := b
}
//~^^^ WARN `id` in this Clean island names the Clean prelude's `id`, NOT the sibling Rust `fn id`
//~| NOTE Clean sees one namespace: `id` is declared as `fn` here and already held by the Clean environment

fn main() {
    // The Rust `fn` is ordinary Rust and still means what it says.
    assert_eq!(id(5), 6);
    // The island's `id` is the prelude's identity, exactly as the warning says.
    assert_eq!(call_id(5), 5);
    assert!(keep(true));
}
