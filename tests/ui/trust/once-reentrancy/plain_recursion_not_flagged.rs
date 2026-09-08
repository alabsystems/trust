//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: recursion OUTSIDE any initializer is none of this check's business —
// that is `unconditional_recursion`'s lint, which this crate allows. The cell
// is here so the crate passes the census pre-filter and the walk really runs.

#![allow(dead_code, unconditional_recursion)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn cell() -> u32 {
    *C.get_or_init(|| 1)
}

fn countdown(n: u32) -> u32 {
    if n == 0 { cell() } else { countdown(n - 1) }
}

#[allow(unconditional_recursion)]
fn forever() -> u32 {
    forever()
}

fn main() {
    let _ = countdown(3);
    let _ = forever;
}
