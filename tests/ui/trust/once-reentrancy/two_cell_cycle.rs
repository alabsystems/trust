//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//
// Trust: no single initializer waits on its own cell directly — A's initializer
// calls `b`, which starts B's initializer, which calls `a`, which waits on A
// while A is still RUNNING. The walk follows closure ARGUMENTS as edges, so the
// cycle is found from both sides: one error per cell.

#![allow(dead_code)]

use std::sync::OnceLock;

static A: OnceLock<u32> = OnceLock::new();
static B: OnceLock<u32> = OnceLock::new();

fn a() -> u32 {
    *A.get_or_init(|| b() + 1)
    //~^ ERROR the initializer of `A` can wait on `A` itself
}

fn b() -> u32 {
    *B.get_or_init(|| a() + 1)
    //~^ ERROR the initializer of `B` can wait on `B` itself
}

fn main() {
    let _ = a();
}
