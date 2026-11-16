//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **CLOSE NEGATIVE TWIN of `clean_origin_rust_call_shadowed_by_island_def.rs`:
//! the shadowing warning fires on USE, never on a name coincidence.**
//!
//! Same two bearers of `inc` — `mod a`'s island `def` and the root's Rust `fn`
//! — and the root island sits right beside the refused `fn`. But no declaration
//! of the root island names `inc`, so nothing the author wrote changed meaning:
//! `inc` and `a::inc` are two unrelated Rust paths. The question "did a
//! declaration of THIS island use the contested name" is answered from the
//! kernel's own terms (`trust_certify::clean_island::island_declarations_naming`),
//! not from source text, so the comment below mentioning inc does not count.
//!
//! No `WARN` annotation and no `dont-require-annotations`: a warning here is an
//! unannotated diagnostic and fails the test.

mod a {
    clean {
        def inc (x : UInt64) : UInt64 := x + 2
    }
}

fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

clean {
    -- deliberately does not call inc
    def add_three (x : UInt64) : UInt64 := x + 3
}

fn main() {
    assert_eq!(inc(5), 6);
    assert_eq!(a::inc(5), 7);
    assert_eq!(add_three(5), 8);
}
