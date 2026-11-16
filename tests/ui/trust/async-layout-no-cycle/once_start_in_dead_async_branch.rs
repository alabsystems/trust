//@ revisions: off adv off_opt adv_opt
//@ edition: 2021
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off_opt] compile-flags: -Ztrust-verify=off -O
//@[adv_opt] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -O
//@ needs-trust-verify
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: can wait on
//@ forbid-output: internal compiler error
//! The once-initializer re-entrancy check must give the same verdict in both lanes.
//! Each `async` body below starts a re-entrant initializer only on a constant-false
//! branch, so none can deadlock. The vanilla lane reads a coroutine through
//! `optimized_mir`, where `SimplifyConstCondition` has removed the branch, and accepts
//! the crate (as the base compiler did in both lanes).
//!
//! With verification on, the coroutine used to be read through its ELABORATED body,
//! which keeps the branch, and every function here was a HARD error — under advisory
//! too, since the check is not policy-gated — "the initializer of `C` can wait on `C`
//! itself". The verified lane now reads `trust_once_coroutine_mir`: the same body the
//! vanilla lane optimizes, from a clone, without TrustVerify.

#![allow(dead_code, unreachable_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();
static D: OnceLock<u32> = OnceLock::new();
static E: OnceLock<u32> = OnceLock::new();

const ENABLED: bool = false;

fn h() -> u32 {
    *C.get_or_init(|| 7)
}

fn k() -> u32 {
    *D.get_or_init(|| 9)
}

fn m() -> u32 {
    *E.get_or_init(|| 11)
}

// `cfg!` of a feature that is never enabled: a literal `false` condition.
pub async fn via_cfg() -> u32 {
    if cfg!(feature = "never_enabled") {
        return *C.get_or_init(|| h() + 1);
    }
    0
}

// A `const` condition, across an await.
pub async fn via_const() -> u32 {
    if ENABLED {
        return *D.get_or_init(|| k() + 1);
    }
    std::future::ready(()).await;
    0
}

// `if false` inside an `async` block.
pub fn via_block() -> impl std::future::Future<Output = u32> {
    async {
        if false {
            return *E.get_or_init(|| m() + 1);
        }
        0
    }
}

fn main() {}
