//@ revisions: default strict memory_safe
//@ needs-trust-verify
//@ aux-build: print_grace_writer_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type=lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! The second half of `print_grace_drop_glue_reaches_foreign_code.rs`, split off
//! when the spawn census's rows (design 2026-09-29-spawn-census-by-construction
//! P2) made the file's output exceed what compiletest captures: the same rule,
//! the same revisions. See that file for the rule and its measurement.
//!
//! The census refuses every function here as well (the second error of each):
//! `dep::Sink::write` has no MIR (R2) and returns an `io::Result`, which can carry
//! a callable it minted out of sight (`io::Error`'s boxed `dyn Error`), so it is
//! an UNKNOWN sink, and a sink leaves every pool unclosed: each function's panic
//! path reaches an indirect call. Under `memory_safe`, `no_print_vanilla_gap` is
//! refused without it.
extern crate print_grace_writer_dep as dep;

use std::any::Any;
use std::io::{BufWriter, LineWriter, Write};

/// No trait object is DROPPED here: `BufWriter`'s std destructor flushes its buffer
/// through `<&mut dyn Write as Write>::write`.
pub fn bufwriter_of_dyn_ref(w: BufWriter<&mut dyn Write>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_dyn_ref`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_dyn_ref`
    println!("{}", x);
    let _w = w;
}

pub fn linewriter_of_dyn_ref(w: LineWriter<&mut dyn Write>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::linewriter_of_dyn_ref`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::linewriter_of_dyn_ref`
    println!("{}", x);
    let _w = w;
}

/// The r13 refix's left-open, asked directly: a dependency writer as the std
/// destructor's type argument, nested one level deeper, and as a type parameter.
pub fn bufwriter_of_dep_writer(w: BufWriter<dep::Sink>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_dep_writer`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_dep_writer`
    println!("{}", x);
    let _w = w;
}

pub fn option_of_bufwriter_of_dep_writer(w: Option<BufWriter<dep::Sink>>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::option_of_bufwriter_of_dep_writer`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::option_of_bufwriter_of_dep_writer`
    println!("{}", x);
    let _w = w;
}

pub fn bufwriter_of_generic_writer<W: Write>(w: BufWriter<W>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_generic_writer`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::bufwriter_of_generic_writer`
    println!("{}", x);
    let _w = w;
}

/// `BufWriter<dep::Sink>` itself is refused by `body_drops_foreign_adt_argument`
/// (a dependency type as a type ARGUMENT of the dropped type); behind a local
/// struct's FIELD it was not, and its destructor runs `dep::Sink::write`.
pub struct Holder {
    pub w: BufWriter<dep::Sink>,
}

pub fn local_holder_of_dep_bufwriter(h: Holder, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::local_holder_of_dep_bufwriter`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::local_holder_of_dep_bufwriter`
    println!("{}", x);
    let _h = h;
}

/// `io::Error`'s `Repr` drops a boxed `dyn Error` through a function pointer it
/// stores; the explicit `drop(e)` spelling was already masked (the call-side walk).
pub fn io_error(e: std::io::Error, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::io_error`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::io_error`
    println!("{}", x);
    let _e = e;
}

pub fn io_result(r: std::io::Result<u32>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::io_result`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::io_result`
    println!("{}", x);
    let _r = r;
}

pub fn waker(w: std::task::Waker, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::waker`
    //~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::waker`
    println!("{}", x);
    let _w = w;
}

/// The same mask behind the OTHER tolerated gap, a vanilla sysroot callee: no print.
pub fn no_print_vanilla_gap(b: Box<dyn Any>) -> usize {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code_writers::no_print_vanilla_gap`
    //[default,strict]~| ERROR Trust Level 0 safety verification incomplete for `print_grace_drop_glue_reaches_foreign_code_writers::no_print_vanilla_gap`
    let _b = b;
    std::env::args().count()
}
