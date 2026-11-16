//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: wr_dep_writer.rs
//@ revisions: wr_direct_call_formatter_new_dep_writer
//@ revisions: masked_dep_call
//@ revisions: masked_dep_call_write_char
//@ revisions: wr_direct_call_derive_dep_writer
//@ compile-flags: -Ztrust-verify=on
//@[wr_direct_call_formatter_new_dep_writer] compile-flags: -Copt-level=0
//@[masked_dep_call] compile-flags: --crate-type lib -Copt-level=0
//@[masked_dep_call_write_char] compile-flags: --crate-type lib -Copt-level=0
//@[wr_direct_call_derive_dep_writer] compile-flags: -Copt-level=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 increment 1 (2026-09-25): RAILS for the writer-relative (WR) class that need
//! a verify-off dependency (`auxiliary/wr_dep_writer.rs`). Both MUST STAY REFUSED.
//!
//! * `wr_direct_call_formatter_new_dep_writer{,_o2}` — the adversarial critique's
//!   required change (a): a DIRECT call into a WR impl from a body that is not
//!   itself a WR root, with a `Formatter` built over a dependency writer whose
//!   `write_str` panics (`#![feature(formatting_options)]`,
//!   `Formatter::new(&mut dep::F, ..)`). `S::fmt` itself compiles as a
//!   conditional pass after increment 1 — that is the point: the direct call is
//!   NOT a std sink, so `main` must be refused. It is, because `S::fmt` is
//!   bundled into `main` and its writer edge is charged to `main` as an unproved
//!   absent callee that no writer-relative excuse covers (`main` is not a
//!   formatting-impl root). BEFORE (stage-1 snapshot `4e9fe36bf`): rc=1, `main`
//!   refused with "an unproved assumption-panic row — a generic absent callee"
//!   (callee `core::fmt::Formatter::<'_>::write_str`), and `S::fmt` refused on its
//!   own writer row. The pin is `main`'s refusal and its cause.
//! * `masked_dep_call{,_o2}` — critique required change (c): `f.write_str(..)?`
//!   followed by a call into the verify-off dependency. The co-folded masked
//!   source withholds the writer-relative excuse, and the writer gap joins the
//!   tolerated gaps a masked source may not hide behind — both refusal-only.
//!   BEFORE: rc=1 at the impl.
//! * `masked_dep_call_write_char{,_o2}` (D1 increment 2, 2026-09-25): the same
//!   rail through `f.write_char(..)?`. Increment 2 stops counting core's
//!   `<Formatter as fmt::Write>::write_char` as a masked source in a
//!   writer-relative root (its one foreign edge is the writer edge itself); the
//!   `dep::boom` call beside it must STILL be one, so this stays refused. BEFORE
//!   (stage-1 snapshot `43b8fe6ab`): rc=1 at the impl (both calls were masked).
//! * `wr_direct_call_derive_dep_writer` (D1 increment 2): critique change (a)
//!   for a DERIVED impl — `#[derive(Debug)]` is writer-relative after increment
//!   2, and a direct `Debug::fmt` call with a `Formatter` over the dependency's
//!   panicking writer is not a sink. `main` must stay refused. BEFORE: rc=1.
#![cfg_attr(
    any(
        wr_direct_call_formatter_new_dep_writer,
        wr_direct_call_derive_dep_writer
    ),
    feature(formatting_options)
)]
extern crate wr_dep_writer as dep;
use std::fmt;

#[cfg(wr_direct_call_formatter_new_dep_writer)]
pub struct S;
#[cfg(wr_direct_call_formatter_new_dep_writer)]
impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("x")
    }
}
#[cfg(wr_direct_call_formatter_new_dep_writer)]
fn main() {
    //[wr_direct_call_formatter_new_dep_writer]~^ ERROR verification failed for
    //[wr_direct_call_formatter_new_dep_writer]~| NOTE assumption-panic row — a generic absent callee
    let mut w = dep::F;
    let mut f = fmt::Formatter::new(&mut w, fmt::FormattingOptions::new());
    let _ = fmt::Display::fmt(&S, &mut f);
}

#[cfg(masked_dep_call)]
pub struct D(pub u8);
#[cfg(masked_dep_call)]
impl fmt::Display for D {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[masked_dep_call]~^ ERROR Trust strict verification failed
        f.write_str("d")?;
        let _ = dep::boom(self.0);
        Ok(())
    }
}

#[cfg(masked_dep_call_write_char)]
use std::fmt::Write as _;
#[cfg(masked_dep_call_write_char)]
pub struct DC(pub u8);
#[cfg(masked_dep_call_write_char)]
impl fmt::Display for DC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[masked_dep_call_write_char]~^ ERROR verification failed for
        f.write_char('d')?;
        let _ = dep::boom(self.0);
        Ok(())
    }
}

#[cfg(wr_direct_call_derive_dep_writer)]
#[derive(Debug)]
pub struct P(pub u32);
#[cfg(wr_direct_call_derive_dep_writer)]
fn main() {
    //[wr_direct_call_derive_dep_writer]~^ ERROR verification failed for
    let mut w = dep::F;
    let mut f = fmt::Formatter::new(&mut w, fmt::FormattingOptions::new());
    let _ = fmt::Debug::fmt(&P(1), &mut f);
}
