//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The run twin of `index_value_tie_requires_std_index.rs` (IDX-TIE-1): the program
//! the false tie miscompiled. `Lo::index` returns `&0` and `Hi::index` returns
//! `&u32::MAX`, so vanilla Rust panics at `b + 1`.
//!
//! Before the fix the tie proved `b + 1`, removed its overflow check, and the
//! program returned 0. Measured 2026-10-03 on stage1-w10: this source built with
//! `-Ztrust-verify=on -Coverflow-checks=on`, under the advisory policy and under
//! the default policy, exits 0 at run time (`TRUST_ELIDE_DEBUG=1`: `elided 1
//! kernel-certified overflow checks` in `f`).
//!
//! After the fix the row is refuted and the check stays, so the run panics. The
//! default policy refuses to BUILD a crate with a refuted row, so this twin uses
//! the advisory policy, which records the row and keeps the check. The expected
//! warnings and the panic are what the same compiler gives for this file with the
//! tie removed by hand (the methods renamed `idx`): build exit 0, run exit 101,
//! "attempt to add with overflow". That held on the stage 1 of `936573497e`
//! (2026-10-04): build exit 0, run exit 101 with that message.

static ZERO: u32 = 0;
static MAX: u32 = u32::MAX;

trait Lo {
    fn index(&self, i: usize) -> &u32;
}
trait Hi {
    fn index(&self, i: usize) -> &u32;
}
impl Lo for [u32] {
    fn index(&self, _i: usize) -> &u32 {
        &ZERO
    }
}
impl Hi for [u32] {
    fn index(&self, _i: usize) -> &u32 {
        &MAX
    }
}

fn f(v: &[u32], i: usize) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index_run::f`
    let a = *Lo::index(v, i);
    let b = *Hi::index(v, i);
    if a == 0 { b + 1 } else { 0 }
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index_run::main`
    let v = [7u32, 8];
    let _ = f(std::hint::black_box(&v[..]), 0);
}
