//@ revisions: rpass1 rpass2 rpass3
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Copt-level=2 -Cdebug-assertions=no
//@ ignore-backends: gcc

// Trust: the optimized twin of `trust-once-facts-async-verify-off.rs` (see it for
// the mechanism): with debug assertions off, `if cfg!(debug_assertions)` is a
// constant-false branch that `optimized_mir` folds away and the elaborated body
// keeps, so reading the coroutine elaborated on a replay changed
// `trust_mir_once_body_facts` between sessions and rpass2 ICEd in the ICH check.
// rpass2 and rpass3 edit only the body of `unrelated`.

#![allow(dead_code)]

use std::sync::OnceLock;

static CONFIG: OnceLock<u32> = OnceLock::new();

pub async fn handle(x: u32) -> u32 {
    if cfg!(debug_assertions) {
        let _ = CONFIG.get_or_init(|| 3);
    }
    std::future::ready(()).await;
    x + 1
}

// The edit is BODY-ONLY on purpose (the literal changes; no item, span or signature
// does): swapping `#[cfg(..)]`-gated items shifts crate-level spans, the facts
// query is then red and recomputed without the ICH check, and the bug hides.
pub fn unrelated() -> u32 {
    if cfg!(rpass1) {
        1
    } else if cfg!(rpass2) {
        2
    } else {
        3
    }
}

fn main() {
    let _ = handle(1);
    assert!(unrelated() > 0);
}
