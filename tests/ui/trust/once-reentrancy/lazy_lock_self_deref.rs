//@ check-fail
//@ compile-flags: -Ztrust-verify=off
// ignore-tidy-linelength
//
// Trust: a `LazyLock` static carries its initializer in the static itself
// (`LazyLock::new(f)`, `F = fn() -> T` by default, so the closure is coerced to a
// fn pointer before the call). `*L` is `<LazyLock as Deref>::deref(&L)`, which
// waits; so does `LazyLock::force(&M)`.

#![allow(dead_code)]

use std::sync::LazyLock;

static L: LazyLock<u32> = LazyLock::new(|| *L + 1);
//~^ ERROR the initializer of `L` can wait on `L` itself: a `std::sync::LazyLock` initializer that re-enters its own cell deadlocks

static M: LazyLock<u32> = LazyLock::new(init_m);

fn init_m() -> u32 {
    *LazyLock::force(&M) + 1
    //~^ ERROR the initializer of `M` can wait on `M` itself
}

fn main() {
    let _ = *L;
    let _ = *M;
}
