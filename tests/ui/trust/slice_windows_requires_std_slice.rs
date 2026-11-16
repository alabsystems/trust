//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! A `<[T]>` slice method is std's only when its callee is DEFINED in a real sysroot
//! crate (its compiler-minted key) and its path strips to `core::slice::{method}`
//! (SLICE-INHERENT-1).
//!
//! `iterator_yield::vc_callee_is_slice_inherent` also accepted `[T]` ANYWHERE in the
//! rendering plus a `::{method}` leaf. `W`'s methods below render
//! `…::W::<[T]>::windows` and `…::W::<[T], &[T; 4]>::iter`, so every consumer minted
//! std's yield fact for a user iterator: `len(win) == 3` (`win`), `len(c) == 4`
//! (`chx`), `i < len(s)` (`en`, through `enumerate`), and a trip count of 4 (`trip`).
//!
//! BEFORE (`scratchpad/stage1-w11fix`, each revision's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`, 2026-10-04): `win`, `chx`
//! and `en` read `slice proved`; `trip` read `overflow:add proved` with the check
//! ELIDED (`TRUST_ELIDE_DEBUG=1`: `elided 1`; the run twin
//! `slice_iter_trip_requires_std_slice_run.rs` returns 44 where vanilla Rust
//! panics). Every revision exits 1 (the user `W::iter`'s own row, `en`'s and `trip`'s
//! absent-callee rows), but none of the annotations on `win`, `chx`, `en` or `trip`
//! matches: under default `win` and `chx` get only warnings, and each count is one
//! lower.
//!
//! AFTER (predicted, then measured): the key gate refuses `W`'s methods and
//! the `[T]` arm is gone. The annotations were derived on the BEFORE compiler from a
//! twin of this file whose `W` methods are renamed `wndws`/`chnks_exact`/`itr`
//! (nothing else changed; the names of `W::<S, A>::iter`'s own diagnostics are
//! mapped back), which the BEFORE recognizer already refuses: checked the way
//! compiletest checks, it matches all three revisions. The std controls `win_std`,
//! `en_std` and `trip_std` keep their facts before and after (`slice proved`,
//! `overflow:add proved`): their callees are keyed `krate_is_real_sysroot: true`.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `trip`'s overflow check is no longer
//! elided; `trip_std`'s still is.
//!
//! Runs with `TRUST_NO_SYSROOT_CENSUS=1` (2026-10-08, std-absent-callee): this file
//! pins obligation COUNTS of the slice-key lane, and the sysroot panic census derives
//! `It::next`'s `&ONE[..]` (`Index<RangeFull>`, which cannot panic) panic-free, which
//! proves `next` outright. Withholding the census (it only removes proof) keeps the
//! counts measured.

use core::marker::PhantomData;

/// A user type whose methods are named like std's slice methods. Called at
/// `W<[T]>`, its paths render `…::W::<[T]>::windows` — `[T]` included.
pub struct W<S: ?Sized, A = ()>(pub u8, pub PhantomData<A>, pub PhantomData<S>);

/// Yields a ONE-element slice, twice.
pub struct It {
    n: usize,
}

static ONE: [u8; 1] = [9];

impl Iterator for It {
    type Item = &'static [u8];
    fn next(&mut self) -> Option<&'static [u8]> {
        //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `<slice_windows_requires_std_slice::It as core::iter::traits::iterator::Iterator>::next`: 1 obligation(s) were not proved
        //[default]~^^ WARN Trust verification advisory for `<slice_windows_requires_std_slice::It as core::iter::traits::iterator::Iterator>::next`: 1 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<slice_windows_requires_std_slice::It as core::iter::traits::iterator::Iterator>::next`: 1 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<slice_windows_requires_std_slice::It as core::iter::traits::iterator::Iterator>::next`: 1 obligation(s) were not fully verified
        //[memsafe]~^^^^^ ERROR Trust memory-safe verification failed for `<slice_windows_requires_std_slice::It as core::iter::traits::iterator::Iterator>::next`: at least one result is not an authenticated memory-safe assumption
        if self.n < 2 {
            self.n += 1;
            Some(&ONE[..])
        } else {
            None
        }
    }
}

/// Yields 300 items, whatever it was built from.
pub struct Many {
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
    pub fn windows(&self, _n: usize) -> It {
        It { n: 0 }
    }
    pub fn chunks_exact(&self, _n: usize) -> It {
        It { n: 0 }
    }
    pub fn iter(_a: A) -> Many {
        //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::W::<S, A>::iter`: 1 obligation(s) were not proved
        //[default,certify]~^^ ERROR Trust strict verification failed for `slice_windows_requires_std_slice::W::<S, A>::iter`: 1 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::W::<S, A>::iter`: 1 obligation(s) were not proved
        //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::W::<S, A>::iter`: at least one result is not an authenticated memory-safe assumption
        Many { n: 0 }
    }
}

/// `len(win) == 3` was minted for the user's one-element slices.
pub fn win<T>(w: &W<[T]>) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::win`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `slice_windows_requires_std_slice::win`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::win`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::win`: at least one result is not an authenticated memory-safe assumption
    let mut s = 0u8;
    for win in w.windows(3) {
        s = win[2];
    }
    s
}

/// `len(c) == 4`, the same way.
pub fn chx<T>(w: &W<[T]>) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::chx`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `slice_windows_requires_std_slice::chx`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::chx`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::chx`: at least one result is not an authenticated memory-safe assumption
    let mut s = 0u8;
    for c in w.chunks_exact(4) {
        s = c[3];
    }
    s
}

/// `i < len(s)` was minted for an enumerate over the user's 300-item iterator.
pub fn en<T: Copy>(s: &[T]) -> Option<T> {
    //[default]~^ WARN Trust verification advisory for `slice_windows_requires_std_slice::en`: a bundled std/core/alloc member's internal obligation was not statically discharged
    //[default,certify]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::en`: 2 obligation(s) were not proved
    //[default,certify]~^^^ ERROR Trust strict verification failed for `slice_windows_requires_std_slice::en`: 2 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust certify verification failed for `slice_windows_requires_std_slice::en`: a bundled std/core/alloc member's internal Assert is left to a runtime check, not statically discharged
    //[memsafe]~^^^^^ WARN Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::en`: 2 obligation(s) were not proved
    //[memsafe]~^^^^^^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::en`: at least one result is not an authenticated memory-safe assumption
    let mut r = None;
    for (i, _) in W::<[T], &[T]>::iter(s).enumerate() {
        r = Some(s[i]);
    }
    r
}

/// A trip count of 4 (the array's length) was minted for the 300-item loop, and
/// the `acc += 1` overflow check was elided.
pub fn trip<T>(s: &[T; 4]) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::trip`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `slice_windows_requires_std_slice::trip`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `slice_windows_requires_std_slice::trip`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::trip`: at least one result is not an authenticated memory-safe assumption
    let mut acc = 0u8;
    for _ in W::<[T], &[T; 4]>::iter(s) {
        acc += 1;
    }
    acc
}

// std's own slice methods keep their facts.
pub fn win_std(s: &[u8]) -> u8 {
    // RE-PINNED 2026-10-15 (the merge of 2026-10-14): both rows are now proved and
    // kernel-certified under all three policies (the soundness line's `windows(N)`
    // yield fact bounds `w[2]`; the bundled `windows` call's own row is discharged), so
    // the std control carries no diagnostic. Measured on the merged stage 1, with the
    // negative twin `for w in s.windows(2) { r = w[2] }` still refused there.
    let mut r = 0u8;
    for w in s.windows(3) {
        r = w[2];
    }
    r
}

pub fn en_std<T: Copy>(s: &[T]) -> Option<T> {
    //[memsafe]~^ ERROR Trust memory-safe verification failed for `slice_windows_requires_std_slice::en_std`: at least one result is not an authenticated memory-safe assumption
    let mut r = None;
    for (i, _) in s.iter().enumerate() {
        r = Some(s[i]);
    }
    r
}

pub fn trip_std(s: &[u8]) -> u64 {
    let mut acc = 0u64;
    for _ in s.iter() {
        acc += 1;
    }
    acc
}
