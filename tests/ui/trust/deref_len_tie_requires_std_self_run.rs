//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The run twin of `deref_len_tie_requires_std_self.rs` (DEREF-ANCHOR-1): the program
//! the false `Deref` length tie miscompiled. `Wrap`'s `deref` returns `&self.a`
//! (`[7]`) on the first call and `&self.b` (empty) on the second, so vanilla Rust
//! passes the `w.len() == 0` guard and panics at `w.len() - 1`.
//!
//! BEFORE: the base-collection trace hopped the user `deref`, tied both `w.len()`
//! results to one `coll_len(w)`, proved the `- 1` row and removed its overflow
//! check. Measured 2026-10-04 on the stage 1 of `38e6c69b1c`
//! (`scratchpad/stage1-w11fix`): this source built with these flags exits 0 with only
//! `main`'s warning (`TRUST_ELIDE_DEBUG=1`: `elided 1 kernel-certified overflow
//! checks` in `h`), and the binary prints `18446744073709551615` and exits 0. Built
//! without a policy flag (default) it also exits 0 and prints the same. Built
//! `-Ztrust-verify=off`, it panics `attempt to subtract with overflow` (exit 101).
//!
//! AFTER (predicted, then measured): the row is refuted and the check stays, so the run
//! panics. The default policy refuses to BUILD a crate with a refuted row, so this
//! twin uses the advisory policy, which records the row and keeps the check. The
//! annotated warnings and the panic are what the BEFORE compiler gives for this file
//! with the second `len()` read through a second parameter bound to the same `Wrap`
//! (`h(w: &Wrap, w2: &Wrap)`, called `h(&w, &w)`), which no tie connects: build exit
//! 0 with `h`'s and `main`'s warnings, run exit 101 with that message. Measured on the
//! stage 1 of `ee3f51541d` (2026-10-04): the same two warnings, nothing elided, and the
//! run panics `attempt to subtract with overflow` (exit 101).

use std::cell::Cell;
use std::ops::Deref;

struct Wrap {
    a: Vec<u32>,
    b: Vec<u32>,
    flip: Cell<bool>,
}

impl Deref for Wrap {
    type Target = Vec<u32>;
    fn deref(&self) -> &Vec<u32> {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

#[inline(never)]
fn h(w: &Wrap) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self_run::h`: 2 obligation(s) were not proved
    if w.len() == 0 {
        return 0;
    }
    w.len() - 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self_run::main`
    let w = Wrap { a: vec![7], b: Vec::new(), flip: Cell::new(false) };
    println!("{}", h(std::hint::black_box(&w)));
}
