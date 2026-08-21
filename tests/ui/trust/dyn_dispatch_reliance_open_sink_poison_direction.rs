//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The POISON direction for `core::fmt::Write`, which
//! `dyn_dispatch_reliance_open_sink_stays_closed.rs` CLAIMED in its title and
//! never tested. Read that file's header first — it now says what it actually
//! establishes, which is the VACUITY decline, and points here.
//!
//! `Formatter<'a>` holds `buf: &'a mut (dyn Write + 'a)` in a FIELD. Until
//! 2026-08-19 `dyn_principals_in_ty` answered for an ADT from its GENERIC
//! ARGUMENTS alone, and `Formatter<'a>`'s arguments are one lifetime — so no
//! principal was named, `fmt::Write` was never poisoned, and the open-sink
//! fixture declined for a reason its own header disclaimed.
//!
//! ## What makes this file the test and that one not
//!
//! Vacuity ("no coercion for this trait anywhere in the bundle") and poison ("a
//! vtable of unknown origin can reach it") are DIFFERENT declines with different
//! repairs, and vacuity is the one that evaporates. This body performs a REAL,
//! WITNESSED `&mut Sink -> &mut dyn Write` coercion — inside `write!(local, …)`,
//! where `spec_write_fmt` unsizes it — at the SAME instantiation the
//! `f.write_str` site dispatches through. So `coerced[dyn Write]` is `{Sink}`:
//! present, non-empty, and every member provably panic-free. Only the poison can
//! refuse the second site.
//!
//! MEASURED on the pre-fix binary: EXIT=0, zero diagnostics, probe reporting the
//! `write_str` group `=> DISCHARGED`. A `Display::fmt` handed a panicking sink by
//! its caller was reported panic-free.
//!
//! `--crate-type lib` is the assertion, as in
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs`: this is the rlib case.
#![no_std]
#![allow(dead_code)]

use core::fmt;

/// Provably panic-free, and the target of the WITNESSED coercion. Its presence
/// is what makes `coerced[dyn Write]` non-empty — i.e. what disarms the vacuity
/// decline that the sibling fixture actually relies on.
pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub struct Tag;

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //~^ ERROR Trust strict verification failed
        use fmt::Write as _;
        let mut local = Sink { written: 0 };
        // WITNESSED: `&mut Sink` -> `&mut dyn Write`, inside the bundle.
        let _ = write!(local, "x");
        // NEVER WITNESSED: `f.buf` is whatever sink the CALLER built, and it can
        // panic. This site must keep its obligation.
        f.write_str("tag")
    }
}
