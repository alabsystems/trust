//@ needs-trust-verify
//@ only-macos
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 -Ztrust-verify-profile=unix_hardened
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Refuted 2026-09-16 (SIGPIPE lens, resumed): a `#[used] #[link_section =
//! "__DATA,__mod_init_func"]` static (the `ctor` crate's shape) runs its function
//! at image load, BEFORE `lang_start -> rt::init -> reset_sigpipe` installs the
//! disposition `unix_hardened` declares. Its stdout writes ran under the parent's
//! inherited `SIG_IGN` (measured: exit 134, "failed printing to stdout: Broken
//! pipe") while the `process_semantics` mandate had been discharged for the whole
//! compilation on the strength of `EntryFnType::Main`. One such static now
//! withdraws the discharge crate-wide: the mandate stays minted and reported for
//! `early` and for `main` alike (measured: two `hardened_process_semantics` rows,
//! against zero for the same source without the constructor).
//!
//! The crate does not BUILD, and that is not this file's subject: `early` is an
//! `extern "C"` body whose `println!` gap is not tolerated there, so it refuses on
//! its own. What is pinned is the mandate's presence; the control for its absence
//! is any `unix_hardened` main without a constructor.
#[used]
#[link_section = "__DATA,__mod_init_func"]
static INIT: unsafe extern "C" fn() = early;

unsafe extern "C" fn early() {
    //~^ ERROR Trust strict verification failed
    println!("early");
}

fn main() {
    println!("main");
}
