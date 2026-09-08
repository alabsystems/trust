//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//
// Trust: the re-entrant wait is two calls away from the initializer — the
// closure calls `helper`, which calls `f`, which waits on `C` again. The walk is
// interprocedural over local bodies, so this is the same error as the direct
// shape, with the call path in the diagnostic.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn f() -> u32 {
    *C.get_or_init(|| helper())
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

fn helper() -> u32 {
    f() + 1
}

fn main() {
    let _ = f();
}
