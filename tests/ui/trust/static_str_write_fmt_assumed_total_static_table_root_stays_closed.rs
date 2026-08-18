//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `write!` reduction must refuse a `write_str` whose only path to a
//! `#[trust::assume_total]` axiom runs through a FUNCTION POINTER IN A STATIC.
//!
//! Two siblings spell the same dependency differently and both are already closed:
//! `static_str_write_fmt_assumed_total_root_stays_closed.rs` calls the axiom
//! directly, and `..._fn_pointer_root_stays_closed.rs` reifies it into a local. In
//! THIS file the calling body never names `boom` at all. `write_str` loads
//! `const {alloc1: &[fn(); 1]}` — a pointer to `GlobalAlloc::Static(TABLE)` — and
//! `boom as fn()` appears only inside TABLE's own initializer, which is not a
//! member of the DefId walk. Both halves of the round-3 census were therefore blind
//! to it.
//!
//! MEASURED, both states, on three compilers built from this tree. On pristine
//! main AND on the round-3 compiler (the one that added the value-mention scan)
//! this file compiles rc=0 with `write_fmt site=… => DISCHARGED`; on round 3 the
//! census prints `axiom census root=<Sink as core::fmt::Write>::write_str
//! axiom_free=true (user_axiom_keys=0, assumed_total=0)`. (Pristine main emits no
//! `axiom census` line at all — it has no census — so that half is a round-3
//! measurement, not a base one.) With the constant-memory walk the same probe
//! prints `axiom_free=false (const_memory_reads_complete=true, user_axiom_keys=1,
//! assumed_total=0)` — the axiom is CENSUSED without ever being SPENT — and the
//! reduction is `kept`.
//!
//! The control that grades this file is `Y6`: the byte-identical program with the
//! `#[trust::assume_total]` attribute removed is rc=1 on every one of those three
//! compilers, so the clean build this fixture forbids was bought entirely by the
//! unproved user declaration. The other control is
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs`, which holds a fn pointer in a
//! static with NO axiom under it and must stay green: this census refuses an
//! AXIOM reachable from constant memory, not constant memory itself.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt;

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

/// The calling body never mentions `boom`. It mentions THIS.
static TABLE: [fn(); 1] = [boom];

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        (TABLE[0])();
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}
