//@ needs-trust-verify
//@ edition: 2021
//@ revisions: lib_i10 debug_write_str write_char_q certify
//@ revisions: println_bin eprintln_bin format_bin to_string_bin debug_println_bin
//@ revisions: write_char_q_println write_char_alone
//@ compile-flags: -Ztrust-verify=on
//@[lib_i10] compile-flags: --crate-type lib -Copt-level=0
//@[debug_write_str] compile-flags: --crate-type lib -Copt-level=0
//@[write_char_q] compile-flags: --crate-type lib -Copt-level=0
//@[certify] compile-flags: --crate-type lib -Copt-level=0 -Ztrust-policy=certify
//@[println_bin] compile-flags: -Copt-level=0
//@[eprintln_bin] compile-flags: -Copt-level=0
//@[format_bin] compile-flags: -Copt-level=0
//@[to_string_bin] compile-flags: -Copt-level=0
//@[debug_println_bin] compile-flags: -Copt-level=0
//@[write_char_q_println] compile-flags: -Copt-level=0
//@[write_char_alone] compile-flags: --crate-type lib -Copt-level=0
//@[lib_i10] check-pass
//@[debug_write_str] check-pass
//@[write_char_q] check-pass
//@[certify] check-fail
//@[println_bin] build-pass
//@[eprintln_bin] build-pass
//@[format_bin] build-pass
//@[to_string_bin] build-pass
//@[debug_println_bin] build-pass
//@[write_char_q_println] build-pass
//@[write_char_alone] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 increment 1 (2026-09-25): the WRITER-RELATIVE (WR) verdict class.
//!
//! A local, non-generic `Display`/`Debug` impl whose only unproved edges are its
//! own `Formatter`'s writer (`<dyn core::fmt::Write>::write_str`/`write_char`)
//! compiles as a CONDITIONAL pass — an advisory carrying the note "panic-free
//! relative to its `Formatter`'s writer" — never proved, and `certify` refuses
//! it. std's formatting sinks (`println!`, `eprintln!`, `format!`, `to_string`)
//! supply a std writer and discharge the condition, so a WR impl formatted there
//! builds (see `trust_verify/fmt_writer_relative.rs` and docs/TCB.md
//! "Formatting premises").
//!
//! BEFORE, measured on the stage-1 snapshot `4e9fe36bf` (current main without
//! this change), every revision below was REFUSED (rc=1). The impl itself failed
//! with "an unproved assumption-panic row — a generic absent callee — keeps the
//! function fail-closed", the row naming
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str` (for `write_char_q`
//! also `...::write_char`); every `*_bin` revision additionally refused `main`
//! with "a value is formatted through a user `Display`/`Debug` implementation
//! whose panic-freedom was not established" (the `to_string` one with the
//! `formats ... not verified panic-free` tolerance note). `lib_i10` is
//! `tests/idiomatic-rust-sample/i10_newtype_display.rs` verbatim.
//!
//! AFTER (predicted; the lead's run records it): every pass revision builds with
//! the impl's advisory pinned by its NOTE below — the pin is the WR disclosure,
//! so a pass for any other reason fails the pin. `certify` stays refused, and
//! its pin shows the refusal is the same writer-relative row, now fatal because
//! `certify` demands static discharge.
//!
//! The rails (`fmt_writer_relative_rails.rs`, `fmt_writer_relative_dep_rails.rs`)
//! hold what must stay refused.
//!
//! D1 increment 2 (2026-09-25): `write_char_q`, `write_char_q_println` (flipped,
//! see the note on `Q`) and the new `write_char_alone`/`write_char_alone_o2`
//! (`f.write_char('w')` as the whole body). BEFORE, measured on the stage-1
//! snapshot `43b8fe6ab`: all four refused (rc=1, "Trust strict verification
//! failed" on the impl; `TRUST_MASK_TRACE` names `<Formatter<'_> as
//! Write>::write_char` as the masked source). AFTER: predicted to pass with the
//! writer-relative pin.
use core::fmt;
#[cfg(any(write_char_q, write_char_q_println, write_char_alone))]
use core::fmt::Write as _;

#[cfg(any(lib_i10, certify, println_bin, eprintln_bin, format_bin, to_string_bin))]
pub struct Port(pub u16);
#[cfg(any(lib_i10, certify, println_bin, eprintln_bin, format_bin, to_string_bin))]
impl fmt::Display for Port { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("port") } }
//[lib_i10]~^ WARN Trust verification advisory
//[lib_i10]~| NOTE panic-free relative to its `Formatter`'s writer
//[certify]~^^^ ERROR Trust strict verification failed
//[certify]~| NOTE panic-free relative to its `Formatter`'s writer
//[println_bin]~^^^^^ WARN Trust verification advisory
//[println_bin]~| NOTE panic-free relative to its `Formatter`'s writer
//[eprintln_bin]~^^^^^^^ WARN Trust verification advisory
//[eprintln_bin]~| NOTE panic-free relative to its `Formatter`'s writer
//[format_bin]~^^^^^^^^^ WARN Trust verification advisory
//[format_bin]~| NOTE panic-free relative to its `Formatter`'s writer
//[to_string_bin]~^^^^^^^^^^^ WARN Trust verification advisory
//[to_string_bin]~| NOTE panic-free relative to its `Formatter`'s writer

#[cfg(any(debug_write_str, debug_println_bin))]
pub struct S(pub u32);
#[cfg(any(debug_write_str, debug_println_bin))]
impl fmt::Debug for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[debug_write_str]~^ WARN Trust verification advisory
        //[debug_write_str]~| NOTE panic-free relative to its `Formatter`'s writer
        //[debug_println_bin]~^^^ WARN Trust verification advisory
        //[debug_println_bin]~| NOTE panic-free relative to its `Formatter`'s writer
        f.write_str("S")
    }
}

#[cfg(any(write_char_q, write_char_q_println))]
pub struct Q;
#[cfg(any(write_char_q, write_char_q_println))]
impl fmt::Display for Q {
    // FLIPPED by D1 increment 2 (2026-09-25) from a documented over-refusal of
    // increment 1 (check-fail at both revisions, "Trust strict verification
    // failed"). The increment-1 note blamed the `?`: that was WRONG. Measured on
    // the stage-1 snapshot `43b8fe6ab` (current main without increment 2): the
    // `write_str` twin of this exact body (`f.write_str("a")?; f.write_str("b")`)
    // builds as a writer-relative pass, and `println!` of it builds and prints
    // `ab` — the `?` sites are totalized and never reach the fold. What refused
    // THIS body, and `f.write_char('b')` alone, was the masked-source scan:
    // `TRUST_MASK_TRACE: <Q as Display>::fmt: masked fail-closed source at _0 =
    // <Formatter<'_> as Write>::write_char(copy _2, const 'b')` — the trait
    // method's `Self = Formatter` holds `buf: &mut dyn Write`, so the scan read it
    // as reaching foreign code. In a writer-relative root that code IS the
    // writer, whose edge row is judged on its own; increment 2 stops counting
    // exactly that call (`fmt_writer_relative::writer_relative_body_has_masked_
    // source`). AFTER (predicted; the lead's run records it): both revisions pass
    // with the writer-relative pin below.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[write_char_q]~^ WARN Trust verification advisory
        //[write_char_q]~| NOTE panic-free relative to its `Formatter`'s writer
        //[write_char_q_println]~^^^ WARN Trust verification advisory
        //[write_char_q_println]~| NOTE panic-free relative to its `Formatter`'s writer
        f.write_str("a")?;
        f.write_char('b')
    }
}

#[cfg(write_char_alone)]
pub struct W;
#[cfg(write_char_alone)]
impl fmt::Display for W {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[write_char_alone]~^ WARN Trust verification advisory
        //[write_char_alone]~| NOTE panic-free relative to its `Formatter`'s writer
        f.write_char('w')
    }
}

#[cfg(println_bin)]
fn main() {
    println!("{}", Port(80));
}

#[cfg(eprintln_bin)]
fn main() {
    eprintln!("{}", Port(80));
}

#[cfg(format_bin)]
fn main() {
    let s = format!("{}", Port(80));
    let _ = s.len();
}

#[cfg(to_string_bin)]
fn main() {
    let s = Port(80).to_string();
    let _ = s.len();
}

#[cfg(debug_println_bin)]
fn main() {
    println!("{:?}", S(1));
}

#[cfg(write_char_q_println)]
fn main() {
    println!("{}", Q);
}
