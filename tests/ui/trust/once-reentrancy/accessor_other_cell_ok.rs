//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: following an accessor's return must not overreach. `other()` returns a
// DIFFERENT cell than the one whose initializer is running — no error. And
// `either()` resolves to TWO different statics, so the receiver is ambiguous and
// stays unresolved: `ambiguous()` is a REAL deadlock the ambiguity rule leaves
// uncaught (a guess has no place in a hard error), pinned here as the documented
// false negative it is.

#![allow(dead_code)]

use std::sync::OnceLock;

static A: OnceLock<u32> = OnceLock::new();
static B: OnceLock<u32> = OnceLock::new();

fn other() -> &'static OnceLock<u32> {
    &B
}

// A's initializer waits on B through the accessor: a different cell, no error.
fn a() -> u32 {
    *A.get_or_init(|| *other().get_or_init(|| 7) + 1)
}

fn either(flag: bool) -> &'static OnceLock<u32> {
    if flag { &A } else { &B }
}

fn ambiguous() -> u32 {
    *either(true).get_or_init(|| ambiguous())
}

fn main() {
    let _ = a();
    let _ = ambiguous();
}
