//@ needs-trust-verify
//@ edition: 2021
//@ revisions: chars_nth dedup_u32 dedup_user_eq
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[chars_nth] check-pass
//@[dedup_u32] check-pass
//@[dedup_user_eq] check-fail
//! **`Iterator::nth` on a total `str` iterator, and `Vec::dedup` over a core-comparable
//! element, are total (Trust, 2026-09-28).**
//!
//! * `chars_nth`: the ordinary sweep's t15. `nth(n)` advances the same iterator up to
//!   `n + 1` times (`Chars` uses `advance_by`), so it is total exactly when `next` is. It
//!   now rides the same receiver gate as `next`/`next_back`
//!   (`total_str_iterator_call`).
//! * `dedup_u32`: `dedup` is `dedup_by(|a, b| a == b)`. It runs `T::eq` and drops the
//!   removed duplicates, and frees nothing. It is total when `T`'s equality is core's own
//!   (`ty_has_builtin_total_ord`) and `T`'s drop is total (`vec_truncating_drop_total_call`,
//!   beside `clear`/`truncate`).
//! * `dedup_user_eq`: the NEGATIVE. A hand-written `PartialEq` can panic, so `f` stays
//!   refused. The annotation on `f` discriminates; `Key::eq` fails on its own as well, so
//!   unannotated errors are allowed.

#[cfg(chars_nth)]
pub fn f(s: &str, n: usize) -> Option<char> {
    s.chars().nth(n)
}

#[cfg(dedup_u32)]
pub fn f(v: &mut Vec<u32>) {
    v.dedup();
}

#[cfg(dedup_user_eq)]
pub struct Key(pub u32);

#[cfg(dedup_user_eq)]
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.0 != 7);
        self.0 == other.0
    }
}

#[cfg(dedup_user_eq)]
pub fn f(v: &mut Vec<Key>) {
    //[dedup_user_eq]~^ ERROR Trust Level 0 safety verification incomplete for `str_nth_and_vec_dedup_are_total::f`
    v.dedup();
}
