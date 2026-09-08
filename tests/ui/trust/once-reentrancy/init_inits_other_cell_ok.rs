//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: nested DISTINCT cells with no cycle — A's initializer calls a function
// that initializes B, whose initializer touches neither. aterm has several of
// these (STARTUP_PRESENT -> PROCESS_START, INDEX -> SCHEMA); they must stay green.

#![allow(dead_code)]

use std::sync::OnceLock;

static A: OnceLock<u32> = OnceLock::new();
static B: OnceLock<u32> = OnceLock::new();

fn a() -> u32 {
    *A.get_or_init(|| b() + 1)
}

fn b() -> u32 {
    *B.get_or_init(|| 2)
}

fn main() {
    let _ = a();
}
