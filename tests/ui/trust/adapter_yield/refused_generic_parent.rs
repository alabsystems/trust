//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: Trust modeled fact
//! D2 tier 1 (2026-09-24): the PARENT gate. The occurrence discipline is read
//! over the parent's own pre-inlining MIR, which is one body only for a
//! non-generic parent; a generic parent is refused (conservative: this program
//! is safe). Same result in both revisions.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): the closure is
//! refused with `[slice] FAILED` on its own root.

pub fn generic_parent<T>(v: &[u32], _t: T) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}
