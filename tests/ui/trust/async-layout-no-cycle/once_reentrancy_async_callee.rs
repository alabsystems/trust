//@ revisions: off adv
//@ edition: 2021
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: E0391
//@ forbid-output: stolen value
//! The once-initializer re-entrancy check on the `first-party/ty` `tla-cli`
//! shape (seal trust-45f6241e): a plain fn (`modified_ns`) reached from a
//! `OnceLock` initializer AND from an `async fn`. The check borrows elaborated
//! MIR; a stolen body is read through `optimized_mir`. With verification on,
//! `from_async`'s coroutine used to be optimized during
//! `run_required_analyses` — its layout was read from `optimized_mir` — and its
//! TrustVerify pass bundled `modified_ns`, stealing that body before the check
//! ran (the `tla-cli` "attempted to read from stolen value" ICE, since routed
//! through the fallback). The layout is now read pre-steal, so under `adv`
//! nothing is stolen when the check runs. Both lanes report the same
//! re-entrant wait.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn modified_ns() -> u32 {
    *C.get_or_init(|| 7)
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

pub fn tool_fingerprint() -> u32 {
    *C.get_or_init(|| modified_ns() + 1)
}

pub async fn from_async() -> u32 {
    modified_ns()
}

fn main() {
    let _ = from_async();
}
