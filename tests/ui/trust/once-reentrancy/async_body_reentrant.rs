//@ check-fail
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//
// Trust: a start site INSIDE a coroutine body. The `async fn`'s waiting call is
// read off its `optimized_mir` (see async_body_ok.rs for why), so the
// initializer it starts is walked like any other: the closure calls `h`, which
// waits on `C` while `C` is RUNNING. The primary span is the re-entrant wait in
// `h`; the starting call in the coroutine carries its own label.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

async fn f() -> u32 {
    *C.get_or_init(|| h() + 1)
}

fn h() -> u32 {
    *C.get_or_init(|| 7)
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

fn main() {
    let _ = f();
}
