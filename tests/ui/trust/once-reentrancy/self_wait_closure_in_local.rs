//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//
// Trust: the initializer is identified by the TYPE of the argument, so a
// closure moved through a local (`let g = ..; C.get_or_init(g)`) and a fn item
// (`D.get_or_init(init_d)`) are both found. For the fn-item form the re-entrant
// wait is inside `d`, reached from `init_d`.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn f() -> u32 {
    let g = || f() + 1;
    *C.get_or_init(g)
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

static D: OnceLock<u32> = OnceLock::new();

fn init_d() -> u32 {
    d() + 1
}

fn d() -> u32 {
    *D.get_or_init(init_d)
    //~^ ERROR the initializer of `D` can wait on `D` itself
}

fn main() {
    let _ = f();
    let _ = d();
}
