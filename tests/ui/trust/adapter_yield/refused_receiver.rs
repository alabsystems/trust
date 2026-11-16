//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: Trust modeled fact
//! D2 tier 1 (2026-09-24): ADAPTER AND RECEIVER identity. The premise is
//! installed only for a core `Iterator` method resolved into a foundational
//! crate, over a receiver written once by an admitted constructor and used
//! once by that adapter. (A runtime `windows(k)` is admitted with `len >= 1`
//! since 2026-10-08; `slice_receiver_stack_refused.rs` pins it.) Each closure
//! below fails one of those, and must
//! stay refused with the premise never installed, in BOTH revisions:
//!
//! * `user_iterator` — a user `Iterator` yielding `&[]` forever (PANICS).
//! * `user_override` — a user `Iterator` whose `all` calls `f(&[])` (PANICS);
//!   the receiver is the user type, and its `all` resolves into this crate.
//! * `range_end_written` — `r.end = 9` after `0..8` (`i = 8` PANICS).
//! * `by_ref_receiver` — `windows(2).by_ref().all(..)` (conservative: safe).
//! * `inclusive_range` — `0..=7` is not an admitted receiver (conservative).
//! * `zero_window` — `windows(0)`: the size must be `>= 1` (the parent panics
//!   before the closure could run; refused anyway).
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): every closure is
//! refused with `[slice] FAILED` / `[bounds] FAILED`, exactly as pinned here.

pub struct Empty;
impl Iterator for Empty {
    type Item = &'static [u32];
    fn next(&mut self) -> Option<&'static [u32]> {
        Some(&[])
    }
}

pub fn user_iterator() -> bool {
    Empty.all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}

pub struct W<'a>(core::slice::Windows<'a, u32>);
impl<'a> Iterator for W<'a> {
    type Item = &'a [u32];
    fn next(&mut self) -> Option<&'a [u32]> {
        self.0.next()
    }
    fn all<F: FnMut(Self::Item) -> bool>(&mut self, mut f: F) -> bool {
        f(&[])
    }
}

pub fn user_override(v: &[u32]) -> bool {
    W(v.windows(2)).all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}

pub fn range_end_written(a: &[u8; 8]) -> bool {
    let mut r = 0..8;
    r.end = 9;
    r.all(|i| a[i] == 0)
    //~^ NOTE [bounds] FAILED
}

pub fn by_ref_receiver(v: &[u32]) -> bool {
    v.windows(2).by_ref().all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}

pub fn inclusive_range(a: &[u8; 8]) -> bool {
    (0..=7).all(|i| a[i] == 0)
    //~^ NOTE [bounds] FAILED
}

pub fn zero_window(v: &[u32]) -> bool {
    v.windows(0).all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}
