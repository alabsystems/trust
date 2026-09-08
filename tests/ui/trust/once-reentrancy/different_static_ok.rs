//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: an initializer may wait on a DIFFERENT cell; cell identity is the
// static's definition, not the method name.

#![allow(dead_code)]

use std::sync::{LazyLock, OnceLock};

static C: OnceLock<u32> = OnceLock::new();
static D: OnceLock<u32> = OnceLock::new();
static L: LazyLock<u32> = LazyLock::new(|| *D.get_or_init(|| 3) + *M);
static M: LazyLock<u32> = LazyLock::new(|| 4);

fn c() -> u32 {
    *C.get_or_init(|| *D.get_or_init(|| 1) + *D.wait())
}

fn main() {
    let _ = c();
    let _ = *L;
}
