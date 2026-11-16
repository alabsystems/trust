//@ revisions: off adv adv_opt
//@ edition: 2021
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[adv_opt] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -O
//@ needs-trust-verify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: internal compiler error
//! Control for `once_start_in_dead_async_branch.rs`: the same start site on a LIVE
//! branch (a runtime flag) is a real re-entrant initializer, and it is reported in
//! both lanes. Reading a coroutine through its vanilla-optimized body must not hide it.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn h() -> u32 {
    *C.get_or_init(|| 7)
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

pub async fn live(flag: bool) -> u32 {
    if flag {
        return *C.get_or_init(|| h() + 1);
    }
    std::future::ready(()).await;
    0
}

fn main() {}
