//@ check-fail
//@ compile-flags: -Ztrust-verify=off
// ignore-tidy-linelength
//
// Trust: deferred-callback REGISTRATION inside an initializer is flagged ON
// PURPOSE, not by accident of the walk: handing the cell-reading callback to
// `std::panic::set_hook` (closure form) or to a local registry (fn-item form)
// makes the re-entrant wait reachable DURING the init window — a panic inside
// the initializer runs the hook re-entrantly, an exit runs atexit callbacks —
// which is exactly the deadlock. Repair 3 in the diagnostic (`C.get()`, which
// never waits) preserves the pattern. This test pins both shapes so that a
// change that stops flagging them is a conscious decision, not a side effect.
// The one-token spelling that erases the edge is pinned by
// `deferred_callback_fn_pointer_cast_ok.rs`.

#![allow(dead_code)]

use std::sync::{Mutex, OnceLock};

static LOGGER: OnceLock<u32> = OnceLock::new();

pub fn logger() -> u32 {
    *LOGGER.get_or_init(|| {
    //~^ ERROR the initializer of `LOGGER` can wait on `LOGGER` itself
        std::panic::set_hook(Box::new(|_| {
            let _ = logger();
        }));
        1
    })
}

static CBS: Mutex<Vec<Box<dyn Fn() + Send>>> = Mutex::new(Vec::new());
static CFG: OnceLock<u32> = OnceLock::new();

fn register<F: Fn() + Send + 'static>(f: F) {
    CBS.lock().unwrap().push(Box::new(f));
}

fn on_exit() {
    let _ = cfg();
}

pub fn cfg() -> u32 {
    *CFG.get_or_init(|| {
    //~^ ERROR the initializer of `CFG` can wait on `CFG` itself
        register(on_exit);
        7
    })
}

fn main() {
    let _ = logger();
    let _ = cfg();
}
