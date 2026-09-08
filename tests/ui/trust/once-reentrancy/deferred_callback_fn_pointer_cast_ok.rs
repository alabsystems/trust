//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: the fn-item registration from
// `deferred_callback_registration_flagged.rs`, with the item CAST to a fn
// pointer. A fn POINTER value is opaque to the walk (a documented false
// negative), so the cast erases the callback edge and this compiles — the one
// spelling that quiets the deliberate deferred-callback flag. Pinned so that
// closing the fn-pointer gap, or anything else that changes this outcome, is a
// conscious decision; the docs name the cast next to the flag it silences.

#![allow(dead_code)]

use std::sync::{Mutex, OnceLock};

static CBS: Mutex<Vec<fn()>> = Mutex::new(Vec::new());
static CFG: OnceLock<u32> = OnceLock::new();

fn register(f: fn()) {
    CBS.lock().unwrap().push(f);
}

fn on_exit() {
    let _ = cfg();
}

pub fn cfg() -> u32 {
    *CFG.get_or_init(|| {
        register(on_exit as fn());
        7
    })
}

fn main() {
    let _ = cfg();
}
