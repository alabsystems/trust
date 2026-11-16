//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The run twin of `slice_windows_requires_std_slice.rs` (SLICE-INHERENT-1): the
//! program the false trip count miscompiled. `W::<[T], &[T; 4]>::iter` is a user
//! associated fn whose path carries `[T]`; it returns an iterator of 300 items, so
//! vanilla Rust panics at `acc += 1` once `acc` passes 255.
//!
//! BEFORE (`scratchpad/stage1-w11fix`, this file built with the flags below,
//! 2026-10-04): `loop_bounds` read the call as std's `<[T]>::iter` over `&[T; 4]`,
//! bounded the loop at 4 trips, proved the `+= 1` row and elided its check
//! (`TRUST_ELIDE_DEBUG=1`: `elided 1 kernel-certified overflow checks` in `trip`);
//! the binary prints 44 and exits 0. Built `-Ztrust-verify=off`, it panics with
//! `attempt to add with overflow`.
//!
//! AFTER (predicted, then measured): the user call is keyed to this crate, so
//! no trip count is minted, the row is refuted and the check stays. The advisory
//! policy records the refuted row and keeps building, so the run panics. A twin of
//! this file with `iter` renamed `itr` (nothing else changed), built the same way on
//! the BEFORE compiler, elides nothing and panics with `attempt to add with
//! overflow`; its warnings are the ones annotated (`main`'s BEFORE-only warning is
//! gone in the twin).
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): the build prints the annotated
//! warnings, `trip`'s check is not elided (`TRUST_ELIDE_DEBUG=1` lists only
//! `Many::next`'s, which BEFORE elided too), and the run panics `attempt to add with
//! overflow` (exit 101).

use core::marker::PhantomData;

/// A user type whose associated fn is named like std's `<[T]>::iter`.
struct W<S: ?Sized, A>(PhantomData<A>, PhantomData<S>);

/// Yields 300 items, whatever it was built from.
struct Many {
    n: u32,
}

impl Iterator for Many {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.n < 300 {
            self.n += 1;
            Some(0)
        } else {
            None
        }
    }
}

impl<S: ?Sized, A> W<S, A> {
    fn iter(_a: A) -> Many {
        //~^ WARN Trust Level 0 safety verification incomplete for `slice_iter_trip_requires_std_slice_run::W::<S, A>::iter`: 1 obligation(s) were not proved
        Many { n: 0 }
    }
}

#[inline(never)]
fn trip<T>(s: &[T; 4]) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete for `slice_iter_trip_requires_std_slice_run::trip`: 2 obligation(s) were not proved
    let mut acc = 0u8;
    for _ in W::<[T], &[T; 4]>::iter(s) {
        acc += 1;
    }
    acc
}

fn main() {
    println!("{}", trip(std::hint::black_box(&[0u8; 4])));
}
