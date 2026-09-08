//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: the FIXED aterm shape (commit 9811b83c in aterm, shipped in v0.67.0):
// the initializer reads the environment — the input — directly, and never asks
// the function that owns the cell. Byte-for-byte the origin/main body, with the
// logger call replaced.

#![allow(dead_code)]

pub fn debug_seamless_reexec_armed() -> bool {
    static ARMED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ARMED.get_or_init(|| {
        // THE ENVIRONMENT ANSWERS THIS, and nothing else can.
        let on = std::env::var_os("ATERM_DEBUG_SEAMLESS_REEXEC").is_some();
        if on {
            eprintln!("$ATERM_DEBUG_SEAMLESS_REEXEC is set");
        }
        on
    })
}

fn main() {
    let _ = debug_seamless_reexec_armed();
}
