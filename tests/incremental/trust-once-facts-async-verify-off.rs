//@ revisions: rpass1 rpass2 rpass3
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ ignore-backends: gcc

// Trust: the VANILLA lane (`-Ztrust-verify=off`), incremental — cargo's default dev
// profile. The once-initializer re-entrancy check runs in this lane too, and its
// per-body facts query (`trust_mir_once_body_facts`) is memoized but NOT disk-cached:
// an incremental session recomputes it and the ICH check compares the result with the
// fingerprint the previous session recorded. A coroutine must therefore be read from
// the same MIR in every session. It is read through `optimized_mir`, which is
// disk-cached.
//
// Before the fix it was read through its ELABORATED body whenever that body was
// intact. In a clean session upstream's eager coroutine layout check steals it (the
// facts came from `optimized_mir`, where a constant-false branch is folded away); on a
// replay that check is green, nothing steals it, and the facts came from the
// elaborated body, which still holds the dead `LazyLock` deref. rpass2 ICEd —
// "Found unstable fingerprints for trust_mir_once_body_facts(...handle::{closure#0})"
// — and every later session did too until the cache was deleted.
//
// rpass2 and rpass3 edit only the body of `unrelated`. The shapes are the three
// measured ones: a `const` flag (a log prefix), a `&&` condition (the log/tracing
// `STATIC_MAX_LEVEL` pattern), and a re-entrant `get_or_init` under `if false`.

#![allow(dead_code, unreachable_code)]

use std::sync::{LazyLock, OnceLock};

const VERBOSE: bool = false;
static LOG_PREFIX: LazyLock<String> = LazyLock::new(|| String::from("[app] "));

pub async fn handle(x: u32) -> u32 {
    if VERBOSE {
        println!("{}handling {}", *LOG_PREFIX, x);
    }
    std::future::ready(()).await;
    x + 1
}

const TRACE: bool = false;
static CONFIG: LazyLock<String> = LazyLock::new(|| String::from("cfg"));

pub fn sync_trace(x: u32) -> u32 {
    if TRACE {
        eprintln!("{}", *CONFIG);
    }
    x + 1
}

pub async fn trace(x: u32) -> u32 {
    if TRACE && x > 3 {
        eprintln!("{}", *CONFIG);
    }
    x + 1
}

static C: OnceLock<u32> = OnceLock::new();

async fn reentrant_when_dead() -> u32 {
    if false {
        return *C.get_or_init(|| h() + 1);
    }
    0
}

fn h() -> u32 {
    *C.get_or_init(|| 7)
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
    let _ = trace(1);
    let _ = reentrant_when_dead();
    assert_eq!(sync_trace(1), 2);
    assert!(unrelated() > 0);
}
