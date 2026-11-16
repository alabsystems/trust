//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The run twin of `ord_min_max_requires_primitive_self.rs` (NAME-ANCHOR-2): the
//! program the false `Ord::min` fact miscompiled. `E`'s `Ord` impl overrides `min`
//! to return `E::B` (200), so vanilla Rust panics at `+ 100`.
//!
//! BEFORE: the call-dest lane read `<…::E as core::cmp::Ord>::min` as std's `min`,
//! proved the `+ 100` row and removed its overflow check. Measured 2026-10-04 on the
//! stage 1 of integ/wave11 `936573497e` (`scratchpad/stage1-w11`) and on
//! `stage1-w10`: this source built with `-Ztrust-verify=on -Coverflow-checks=on`
//! exits 0 under the default, strict, advisory and memory-safe policies
//! (`TRUST_ELIDE_DEBUG=1`: `elided 1 kernel-certified overflow checks` in `f`), and
//! the binary prints 44 and exits 0. Built `-Ztrust-verify=off`, it panics.
//!
//! AFTER: the row is refuted and the check stays, so the run panics. The default
//! policy refuses to BUILD a crate with a refuted row, so this twin uses the
//! advisory policy, which records the row and keeps the check. BEFORE, `f` had no
//! warning (every row proved) and `main` had the one annotated here.

use core::cmp::Ordering;

#[repr(u8)]
#[derive(PartialEq, Eq, PartialOrd, Clone, Copy)]
enum E {
    A = 0,
    B = 200,
}

impl Ord for E {
    fn cmp(&self, o: &Self) -> Ordering {
        (*self as u8).cmp(&(*o as u8))
    }
    // A user override: returns `B` whatever the arguments.
    fn min(self, _o: Self) -> Self {
        E::B
    }
}

#[inline(never)]
fn f(x: E) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self_run::f`: 2 obligation(s) were not proved
    (x.min(E::A) as u8) + 100
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self_run::main`
    println!("{}", f(std::hint::black_box(E::A)));
}
