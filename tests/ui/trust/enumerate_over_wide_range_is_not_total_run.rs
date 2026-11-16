//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `enumerate_over_wide_range_is_not_total.rs` (ITER-RECV-1): the
//! `always_panics` that file's BEFORE compiler certified panic-free. `skip(usize::MAX)`
//! makes the first `next` call `Enumerate::nth(usize::MAX)`; the `Range<u128>` has an
//! item at that index, so `count + n` is `usize::MAX` and the `+ 1` after it
//! overflows (core's enumerate.rs, `#[rustc_inherit_overflow_checks]`).
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the panic is real, not the verdict. Measured 2026-10-04 on the stage 1
//! of `38e6c69b1c` (`scratchpad/stage1-w11fix`): this file built
//! `-Ztrust-verify=off -Coverflow-checks=on` exits 101 with the message above. Built
//! `-Ztrust-verify=on -Ztrust-policy=certify` it builds exit 0 (`always_panics` reads
//! `unreach proved` only, `main` `no_obligations proved`) and exits 101 the same way:
//! the check is kept, the certificate is what was false.

#[inline(never)]
fn always_panics() -> usize {
    let mut e = (0u128..u128::MAX).enumerate().skip(usize::MAX);
    match e.next() {
        Some((i, _)) => i,
        None => 0,
    }
}

fn main() {
    let r = always_panics();
    if r == 7 {
        return;
    }
}
