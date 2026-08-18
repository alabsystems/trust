//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The POISON direction: a `Display::fmt` verified on its own carries a
//! caller-chosen sink, so its `dyn` site must stay fail-closed.
//!
//! `f: &mut Formatter<'_>` is a ROOT parameter whose `buf` field is a
//! `&mut dyn Write` this compilation never sees created. That is an entry point
//! for a vtable of unknown origin, so `core::fmt::Write` is POISONED for this
//! bundle and neither certificate applies:
//!
//! * C-FLOW declines — the coercion set is not complete;
//! * C-UNIVERSAL declines — Φ is not (and cannot soundly be) declared on
//!   `fmt::Write::write_str`, because std's private `Adapter` impl forwards to an
//!   arbitrary user `io::Write`.
//!
//! This verdict is CORRECT, not a limitation to be optimized away: a
//! `Display::fmt` really does panic when handed a panicking sink, and any rule
//! that reported it clean would be a false promise. The composite in
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs` — where the caller pins the
//! sink — is the shape that legitimately discharges.
#![no_std]
#![allow(dead_code)]

use core::fmt;

pub struct Tag;

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("tag")
        //~^^ ERROR Trust strict verification failed
    }
}
