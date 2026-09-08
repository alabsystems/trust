//@ check-fail
//@ compile-flags: -Ztrust-verify=off
// ignore-tidy-linelength
//
// Trust: the exact aterm v0.65.0 shape (commit c493e44c in aterm): a fn-local
// `static ARMED: OnceLock<bool>` whose initializer calls the very function that
// is running `ARMED.get_or_init`. std's `Once` parks the initializing thread on
// its own `RUNNING` state — every caller hung forever. This must be a HARD error
// on an ordinary build, i.e. with `-Ztrust-verify=off`.

#![allow(dead_code)]

pub fn debug_seamless_reexec_armed() -> bool {
    static ARMED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ARMED.get_or_init(|| {
    //~^ ERROR the initializer of `ARMED` can wait on `ARMED` itself: a `std::sync::OnceLock` initializer that re-enters its own cell deadlocks — the initializing thread parks forever
        let on = debug_seamless_reexec_armed();
        if on {
            eprintln!("$ATERM_DEBUG_SEAMLESS_REEXEC is set");
        }
        on
    })
}

fn main() {
    let _ = debug_seamless_reexec_armed();
}
