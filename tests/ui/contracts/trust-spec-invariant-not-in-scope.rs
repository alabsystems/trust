//! Trust: with no `trust` crate linked and no `register_tool(trust)`, the
//! `trust::invariant` path must remain E0433.
//!
//! This pins the OTHER end of the refusal. `trust` is not a builtin registered
//! tool (the builtin list in `rustc_resolve::macros` is `clippy, rustfmt,
//! diagnostic, miri, rust_analyzer`), so absent the shim crate the path simply
//! does not resolve. That is the correct fail-closed behaviour and the new
//! refusal builtin must not accidentally make the bare path resolvable — a
//! builtin that answers for `trust::invariant` in crates that never linked
//! `trust` would be a new, quieter way to accept the annotation.
//@ edition: 2021

#![allow(dead_code)]

#[trust::invariant(x > 0)]
//~^ ERROR cannot find module or crate `trust` in this scope
fn annotated(x: i32) -> i32 {
    x
}

fn main() {}
