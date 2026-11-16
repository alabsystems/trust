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
//! D2 tier 1 (2026-09-24): an `async fn` / coroutine parent is EXCLUDED. A
//! closure inside an `async fn` body is a child of the coroutine, never of a
//! plain `fn`, and a coroutine's MIR is stolen by its layout computation before
//! the analysis seam runs. Same result in both revisions (conservative: this
//! program is safe).
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): the closure is
//! refused with `[slice] FAILED` on its own root, and the coroutine body with
//! the unproved executor-protocol premise.

pub async fn async_parent(v: &[u32]) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}
