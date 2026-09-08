//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: reading the cell WITHOUT waiting inside its own initializer is fine:
// `OnceLock::get`, `Once::is_completed` and `LazyLock::get` never park. This is
// repair 3 in the diagnostic's help.

#![allow(dead_code)]

use std::sync::{LazyLock, Once, OnceLock};

static C: OnceLock<u32> = OnceLock::new();

fn c() -> u32 {
    *C.get_or_init(|| C.get().copied().unwrap_or(1))
}

static O: Once = Once::new();

fn o() {
    O.call_once(|| {
        let _ = O.is_completed();
    })
}

static L: LazyLock<u32> = LazyLock::new(|| LazyLock::get(&L).copied().unwrap_or(2));

fn main() {
    let _ = c();
    o();
    let _ = *L;
}
