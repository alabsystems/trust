//@ needs-trust-verify
//@ edition: 2021
//@ revisions: tuple_u32 enum_d3 enum_i01 nested_local certify_tuple
//@ revisions: println_tuple println_pretty format_enum nested_local_println
//@ revisions: termination_derived
//@ revisions: enum_struct_arities
//@ compile-flags: -Ztrust-verify=on
//@[tuple_u32] compile-flags: --crate-type lib -Copt-level=0
//@[enum_d3] compile-flags: --crate-type lib -Copt-level=0
//@[enum_i01] compile-flags: --crate-type lib -Copt-level=0
//@[nested_local] compile-flags: --crate-type lib -Copt-level=0
//@[certify_tuple] compile-flags: --crate-type lib -Copt-level=0 -Ztrust-policy=certify
//@[println_tuple] compile-flags: -Copt-level=0
//@[println_pretty] compile-flags: -Copt-level=0
//@[format_enum] compile-flags: -Copt-level=0
//@[nested_local_println] compile-flags: -Copt-level=0
//@[termination_derived] compile-flags: -Copt-level=0
//@[enum_struct_arities] compile-flags: --crate-type lib -Copt-level=0
//@[tuple_u32] check-pass
//@[enum_d3] check-pass
//@[enum_i01] check-pass
//@[nested_local] check-pass
//@[certify_tuple] check-fail
//@[println_tuple] build-pass
//@[println_pretty] build-pass
//@[format_enum] build-pass
//@[nested_local_println] build-pass
//@[termination_derived] build-pass
//@[enum_struct_arities] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 increment 2 (2026-09-25): `#[derive(Debug)]` in the WRITER-RELATIVE (WR)
//! class — its nested formatters (`<dyn core::fmt::Debug>::fmt` inside core's
//! `DebugTuple`/`DebugStruct`) are excused when every target they can reach
//! panics only through the `Formatter`'s writer (core's `&T` forwarding impl,
//! a sysroot impl at a foundational type, or a local impl with a verdict of its
//! own), and `{:#?}`'s `PadAdapter` is core's own wrapper of that writer. See
//! `trust_verify/fmt_writer_relative.rs` ("Increment 2") and docs/TCB.md
//! "Formatting premises".
//!
//! BEFORE, measured on the stage-1 snapshot `43b8fe6ab` (current main without
//! increment 2): EVERY revision refused (rc=1). Each derived impl failed with
//! "Trust strict verification failed", its rows naming
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str` and
//! `<dyn core::fmt::Debug as core::fmt::Debug>::fmt`, and the dyn-reliance probe
//! naming four refusals of the writer-relative facts: poison from a CONSTANT
//! operand and from the outputs of the UNBUNDLED callee `std::fmt::Debug::fmt`
//! on `std::fmt::Write`, C-FLOW declining the `<&T as Debug>::fmt` target, and
//! (read off the bundle) `PadAdapter::wrap`'s `Formatter` and `&mut dyn Write`
//! coercion plus the `unreachable_unchecked::precondition_check` member. Every
//! bin revision also refused `main` with "a value is formatted through a user
//! `Display`/`Debug` implementation whose panic-freedom was not established".
//! `enum_i01` is `tests/idiomatic-rust-sample/i01_*.rs`'s type; `tuple_u32` and
//! `enum_d3` are the open-dispatch ladder's `d2`/`d3`.
//!
//! AS FIRST COMMITTED (`94837a9e88`, measured on its stage-1 build): STILL every
//! revision refused, the same "Trust strict verification failed" on each derived
//! impl. `TRUST_DYN_RELIANCE_PROBE` named the three refusing writer-relative
//! conjuncts: `write_poisoned_beyond_formatter_param` and `write_forge_poisoned`
//! (the bundle's one `dyn`-bearing constant is `Option<&mut PadAdapter<'_, '_>>`,
//! the `None` arm of `Option::insert`'s inlined `as_mut().unwrap_unchecked()` in
//! `PadAdapter::wrap` — not the predicted `Option<PadAdapter>` — so it kept the
//! forged `Constant` poison) and `unrowed_panic_site` (G-MEMBER counted the no-op
//! `drop(value_fmt)` of `DebugTuple::field`'s reference-capturing closure in
//! `DebugTuple::field_with` and its closure).
//!
//! AFTER (MEASURED on stage-1 `d1i2-live`, 2026-09-25): every pass revision
//! builds with the derived impl's advisory pinned by the writer-relative NOTE (on
//! the line after `#[derive(Debug)]`, where rustc spans a derived impl) — a pass
//! for any other reason fails the pin; the bins run to exit 0 (`termination_derived`
//! to exit 1, its `Err` report). `certify_tuple` stays refused, pinned to the same
//! writer-relative note. The rails are `fmt_writer_relative_derive_rails.rs`.
//!
//! 1.101 REGRESSION (measured on stage-1 `39d11b38d7`, 2026-11-08): `nested_local`,
//! `nested_local_println`, `println_tuple`, `println_pretty`, `format_enum` and
//! `termination_derived` refused (rc=1) — every revision whose verdict rests on the
//! SHARED writer-relative bar (a nested-formatter target, or a sink's formatter)
//! rather than on the impl's own decision. The upstream finishers (`ff7c30e864ac`,
//! ported in `eaa3250ddc`) walk `<Split<'_, u8, _> as Iterator>::next`, whose inlined
//! `slice::Iter::new` calls `<*mut T>::add::precondition_check`; the bundler declines
//! `core::ptr::` bodies, so the check was ABSENT and its marker (`TRUST_PF_BAR_TRACE`:
//! "non-writer fold site ... `core::ptr::mut_ptr::<impl *mut T>::add::precondition_check`")
//! kept the bar refused. Fixed by P-UB for absent UB-check members
//! (`WriterRelativeFacts::ub_check_callee_keys`, docs/TCB.md P-UB).
use std::fmt;

#[cfg(any(tuple_u32, certify_tuple, println_tuple, println_pretty))]
#[derive(Debug)]
//[tuple_u32]~^ WARN Trust verification advisory
//[tuple_u32]~| NOTE panic-free relative to its `Formatter`'s writer
//[certify_tuple]~^^^ ERROR Trust strict verification failed
//[certify_tuple]~| NOTE panic-free relative to its `Formatter`'s writer
//[println_tuple]~^^^^^ WARN Trust verification advisory
//[println_tuple]~| NOTE panic-free relative to its `Formatter`'s writer
//[println_pretty]~^^^^^^^ WARN Trust verification advisory
//[println_pretty]~| NOTE panic-free relative to its `Formatter`'s writer
pub struct P(pub u32);

#[cfg(enum_d3)]
#[derive(Debug)]
//[enum_d3]~^ WARN Trust verification advisory
//[enum_d3]~| NOTE panic-free relative to its `Formatter`'s writer
pub enum E {
    A,
    B(u32),
}

#[cfg(any(enum_i01, format_enum))]
#[derive(Debug)]
//[enum_i01]~^ WARN Trust verification advisory
//[enum_i01]~| NOTE panic-free relative to its `Formatter`'s writer
//[format_enum]~^^^ WARN Trust verification advisory
//[format_enum]~| NOTE panic-free relative to its `Formatter`'s writer
pub enum ConfigError {
    Missing(&'static str),
    Invalid { key: &'static str, got: u32 },
}

// Trust (96a18b, P-SPLIT; 1.101 shape): struct variants of arity 1, 3 and 5
// in one derive — `debug_struct_field{1,3,5}_finish` each take ONE
// concatenated names string (`"One a"`, `"Three a b c"`, `"Five a b c d e"`)
// and forward it to `debug_struct_fields_finish`, so each arm's evidence
// (a constant names string with the finisher's arity of separators, chained
// through the forwarding call) is exercised beside `enum_i01`'s arity 2.
#[cfg(enum_struct_arities)]
#[derive(Debug)]
//[enum_struct_arities]~^ WARN Trust verification advisory
//[enum_struct_arities]~| NOTE panic-free relative to its `Formatter`'s writer
pub enum Arities {
    One { a: u32 },
    Three { a: u32, b: &'static str, c: bool },
    Five { a: u32, b: &'static str, c: bool, d: char, e: u8 },
}

#[cfg(any(nested_local, nested_local_println))]
#[derive(Debug)]
pub struct Inner(pub u32);

// `Outer`'s nested formatter reaches core's `<&Inner as Debug>::fmt`, peeled to
// the LOCAL `<Inner as Debug>::fmt`, which is itself writer-relative.
#[cfg(any(nested_local, nested_local_println))]
#[derive(Debug)]
//[nested_local]~^ WARN Trust verification advisory
//[nested_local]~| NOTE panic-free relative to its `Formatter`'s writer
//[nested_local_println]~^^^ WARN Trust verification advisory
//[nested_local_println]~| NOTE panic-free relative to its `Formatter`'s writer
pub struct Outer(pub Inner, pub u8);

#[cfg(println_tuple)]
fn main() {
    println!("{:?}", P(std::hint::black_box(7)));
}

// `{:#?}` runs core's `PadAdapter` over stdout's writer.
#[cfg(println_pretty)]
fn main() {
    println!("{:#?}", P(std::hint::black_box(7)));
}

#[cfg(format_enum)]
fn main() {
    let a = format!("{:?}", ConfigError::Missing("port"));
    let b = format!("{:?}", ConfigError::Invalid { key: "port", got: std::hint::black_box(0) });
    let _ = a.len();
    let _ = b.len();
}

#[cfg(nested_local_println)]
fn main() {
    println!("{:?}", Outer(Inner(std::hint::black_box(1)), 2));
}

// `main`'s `Termination::report` formats the error with `Debug` into stderr —
// the fourth sink, with both its checks (the writer-relative bar AND error
// transparency, recognizer version 2).
#[cfg(termination_derived)]
#[derive(Debug)]
//[termination_derived]~^ WARN Trust verification advisory
//[termination_derived]~| NOTE panic-free relative to its `Formatter`'s writer
pub struct Failure(pub u32);

#[cfg(termination_derived)]
fn main() -> Result<(), Failure> {
    let code = std::hint::black_box(3u32);
    if code == 3 { Err(Failure(code)) } else { Ok(()) }
}
