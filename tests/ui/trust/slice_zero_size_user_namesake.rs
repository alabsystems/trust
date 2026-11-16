//@ revisions: usernames usernames_cert usernames_ms controls
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[usernames_cert] compile-flags: -Ztrust-policy=certify
//@[usernames_ms] compile-flags: -Ztrust-policy=memory-safe
//@[usernames] check-pass
//@[usernames_cert] check-pass
//@[usernames_ms] check-pass
//@[controls] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A USER method merely NAMED like one of core's panicking slice methods owes none of
//! that method's rows (SLICE-ZERO-SIZE-NAME-1; 2026-10-11).
//!
//! `trust_vcgen`'s `panic_calls::slice_method_panic` MINTS core's slice rows over the
//! call's own arguments: `n == 0` for `chunks*` / `rchunks*` / `windows` (a zero size
//! panics), `mid > len` for `split_at*`, `i >= len || j >= len` for `swap`. It decided
//! the callee by its last path segment alone, so a call to a user `Grid::windows(&self,
//! n) { self.w ^ n }`, a user trait's `Tiles::chunks_exact`, or a user trait implemented
//! for `[u8]` with total `swap` / `split_at` / `windows` was charged core's row over the
//! user method's own arguments and REFUTED (`[divzero] FAILED; counterexample: k = 0`,
//! `[slice] FAILED`) — for methods that cannot panic. The DIVZERO-NAME-1 sibling.
//!
//! It now mints those three arms' rows only when the callee's ROOT is a sysroot crate
//! (`core::` / `alloc::` / `std::`, read past one well-formed leading `__trust_crate@`
//! stamp, keyless). The fn-item deny-list keeps the old name-only answer.
//!
//! BEFORE (the stage 1 of `1213387e6d`, `scratchpad/stage1-w24probe`, measured
//! 2026-10-11 with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json -A unused`; the
//! commands and outputs are in `scratchpad/scout24/D/ui/`):
//! * `usernames` exits 1 with 17 errors: `p1`..`p7` each read "Trust Level 0 safety
//!   verification incomplete" and "Trust strict verification failed" on a `[divzero]`
//!   or `[slice] FAILED` row, and `p1`, `p4` and `p7` also read "Trust verification
//!   found 1 guaranteed Level 0 safety violation(s)" (FORCED-OWN-EQ-1's false label).
//!   `g1` passes.
//! * `usernames_cert` (`certify`) exits 1 with the same 17 errors.
//! * `usernames_ms` (`memory-safe`) exits 0 (the FAILED rows are reported as
//!   warnings); it pins that the fix moves nothing there.
//! * The renamed twin of the `usernames` module (every user method renamed off core's
//!   names, bodies identical; `crates/trust-vcgen/tests/fixtures/user_namesake_slice/
//!   renamed_slice.rs` minus the generic owner; `scratchpad/scout24/D/ui/
//!   slice_zero_size_user_namesake_twin.rs`) builds rc=0 with each `usernames*`
//!   revision's flags on the same compiler.
//! * `controls` exits 1 with exactly the errors annotated below; `g2` and `g3` pass.
//!   FORCED-OWN-EQ-1 is not fixed this wave, so `c1` (`s.windows(k)`, which panics only
//!   at `k == 0`) still prints the false "guaranteed Level 0 safety violation".
//!
//! NOT HERE: the generic owner `W::<[T]>::windows` (`impl<S: ?Sized> W<S> { fn
//! windows(&self, n: usize) -> usize }` called from `fn p5<T>(w: &W<[T]>, k: usize)`).
//! Its renamed twin is refused too, for a reason this fix does not touch ("a call it
//! makes is discharged by no authenticated panic-freedom registry"), so no check-pass
//! revision can hold it. vcgen's half is pinned on real MIR in
//! `crates/trust-vcgen/tests/user_namesake_slice_realmir.rs` (`p5`).
//!
//! AFTER (predicted; not built — the fix is in `crates/` only and needs a rebuilt
//! stage 1): the three `usernames*` revisions exit 0 — vcgen gives each caller exactly
//! its renamed twin's obligations (`user_namesake_slice_realmir.rs`). `controls` is
//! unchanged.

// ---- usernames: user methods that share a name with core's slice methods ----

#[cfg(any(usernames, usernames_cert, usernames_ms))]
pub mod user {
    pub struct Grid {
        pub w: usize,
    }

    impl Grid {
        #[inline(never)]
        pub fn windows(&self, n: usize) -> usize {
            self.w ^ n
        }

        #[inline(never)]
        pub fn chunks(&self, n: usize) -> usize {
            self.w.wrapping_add(n)
        }

        #[inline(never)]
        pub fn rchunks_exact(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Tiles {
        fn chunks_exact(&self, n: usize) -> usize;
    }

    pub struct G2;

    impl Tiles for G2 {
        #[inline(never)]
        fn chunks_exact(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Tr {
        fn swap(&self, i: usize, j: usize) -> usize;
        fn split_at(&self, m: usize) -> usize;
        fn windows(&self, n: usize) -> usize;
    }

    impl Tr for [u8] {
        #[inline(never)]
        fn swap(&self, i: usize, j: usize) -> usize {
            i ^ j
        }

        #[inline(never)]
        fn split_at(&self, m: usize) -> usize {
            m
        }

        #[inline(never)]
        fn windows(&self, n: usize) -> usize {
            n
        }
    }

    pub fn p1(g: &Grid, k: usize) -> usize {
        g.windows(k)
    }

    pub fn p2(g: &Grid) -> usize {
        g.chunks(0)
    }

    pub fn p3(g: &Grid) -> usize {
        g.rchunks_exact(0)
    }

    pub fn p4(g: &G2, k: usize) -> usize {
        g.chunks_exact(k)
    }

    pub fn p5(s: &[u8], i: usize, j: usize) -> usize {
        s.swap(i, j)
    }

    pub fn p6(s: &[u8], m: usize) -> usize {
        Tr::split_at(s, m)
    }

    pub fn p7(s: &[u8], n: usize) -> usize {
        Tr::windows(s, n)
    }

    // Passes before and after: the guard discharged the (spurious) row.
    pub fn g1(g: &Grid, k: usize) -> usize {
        if k != 0 { g.windows(k) } else { 0 }
    }
}

// ---- controls: core's own slice methods keep their rows ----

#[cfg(controls)]
pub fn c1(s: &[u8], k: usize) -> usize {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `slice_zero_size_user_namesake::c1`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `slice_zero_size_user_namesake::c1`: 2 obligation(s)
    // Re-pinned 2026-10-15: no longer a "guaranteed" violation, and it never was one. `k` is a
    // free parameter, so `windows(k)` panics only when the caller passes 0 (the FAILED
    // `[divzero]` row's counterexample `k = 0`); a violation that depends on an input is
    // possible, not forced. The merged compiler does not emit it (measured 2026-10-15 on the
    // merge's stage 1, before and after trust-router's `violation_is_forced` stopped binding
    // a violation's own equalities). Still refused.
    s.windows(k).count()
}

#[cfg(controls)]
pub fn c2(s: &[u8]) -> usize {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `slice_zero_size_user_namesake::c2`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `slice_zero_size_user_namesake::c2`: 2 obligation(s)
    s.chunks(0).count()
}

#[cfg(controls)]
pub fn c3(s: &[u8], m: usize) -> usize {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `slice_zero_size_user_namesake::c3`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `slice_zero_size_user_namesake::c3`: 2 obligation(s)
    s.split_at(m).0.len()
}

#[cfg(controls)]
pub fn c4(s: &mut [u8], i: usize, j: usize) {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `slice_zero_size_user_namesake::c4`: 2 obligation(s) were not proved
    //[controls]~| ERROR Trust strict verification failed for `slice_zero_size_user_namesake::c4`: 2 obligation(s)
    s.swap(i, j)
}

#[cfg(controls)]
pub fn g2(s: &[u8], k: usize) -> usize {
    if k != 0 { s.chunks(k).count() } else { 0 }
}

#[cfg(controls)]
pub fn g3(s: &mut [u8], i: usize, j: usize) {
    if i < s.len() && j < s.len() {
        s.swap(i, j)
    }
}
