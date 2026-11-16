//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Refuted 2026-09-16 (SIGPIPE lens): `unix_hardened` DECLARES the process-signal
//! policy, but the only installer is std's `lang_start`, which rustc emits solely
//! for an `EntryFnType::Main` entry. A library (or a `#![no_main]` crate) emits no
//! installer, so a mandate discharged on the declaration there was discharged on
//! nothing — measured: a `#![no_main]` binary under `unix_hardened` built with
//! the mandate gone and INHERITED its parent's SIGPIPE disposition. The
//! `process_semantics` mandate therefore stays MINTED here (an opaque design
//! mandate: reported under the default policy, refused under certify), and the
//! `installed_process_signal_policy` helper is what the discharge keys on.
pub fn shout() {
    //~^ WARN Trust Level 0 safety verification incomplete
    //~| NOTE [hardened_process_semantics]
    println!("hello");
}
