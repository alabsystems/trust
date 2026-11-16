//@ needs-trust-verify
//@ edition: 2021
//@ revisions: plus_one plus_one_o1 not_ascii_boundary none_arm join_max reseated_iter other_root user_position
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[plus_one] check-pass
//@[plus_one_o1] check-pass
//@[plus_one_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[not_ascii_boundary] check-fail
//@[none_arm] check-fail
//@[join_max] check-fail
//@[reseated_iter] check-fail
//@[other_root] check-fail
//@[user_position] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (STR_BYTES_POSITION_BOUND, 2026-10-04): the `Some(i)` of an authenticated
//! `s.bytes().position(..)` satisfies `i + 1 <= s.len()`, guarded by the
//! discriminant. `crates/trust-vcgen/src/generate/str_offset.rs`
//! (`str_bytes_position_dest_facts`) has the gates; `docs/TCB.md` has the std
//! contract. It grants NO char-boundary credit.
//!
//! # Before (measured on the stage 1 of `3122ad070f`, 2026-10-04)
//!
//! `plus_one` was `[overflow:add] FAILED` with `i = 18446744073709551615`.
//!
//! Not covered (measured on the same stage 1 with the fact): a `while let Some(i) =
//! it.position(..)` loop over one iterator still fails `i + 1` — the fact does not
//! reach the loop body's discriminant read. The bound would hold there (each call's
//! index is relative to the remaining suffix), so this is a precision gap only.
//!
//! # The rails, each a program that really panics
//!
//! * `not_ascii_boundary` — `position(|b| b == 0xA9)` on `"é"` gives `i = 1`, and
//!   `&s[i..]` panics: a byte position is not a char boundary.
//! * `none_arm` — the `None` arm of `""` indexes byte 0.
//! * `join_max` — `None => usize::MAX`, then `i + 1` overflows.
//! * `reseated_iter` — the iterator is reseated to a longer string through `&mut`
//!   before `position`, and the index is used on the shorter one.
//! * `other_root` — `a`'s position indexes `b`, which can be shorter.
//! * `user_position` — a user iterator overriding `position` with `Some(usize::MAX)`.

#[cfg(any(plus_one, plus_one_o1))]
pub fn plus_one(rest: &str) -> usize {
    match rest.bytes().position(|b| b == b'/') {
        Some(i) => i + 1,
        None => 0,
    }
}

#[cfg(not_ascii_boundary)]
pub fn not_ascii_boundary(s: &str) -> &str {
    match s.bytes().position(|b| b == 0xA9) {
        Some(i) => &s[i..],
        None => s,
    }
}

#[cfg(none_arm)]
pub fn none_arm(r: &str) -> u8 {
    match r.bytes().position(|b| b == b'/') {
        Some(_) => 0,
        None => r.as_bytes()[0],
    }
}

#[cfg(join_max)]
pub fn join_max(s: &str) -> usize {
    let i = match s.bytes().position(|b| b == b'/') {
        Some(i) => i,
        None => usize::MAX,
    };
    i + 1
}

#[cfg(reseated_iter)]
pub fn reseated_iter(a: &str, b: &'static str) -> u8 {
    let mut it = a.bytes();
    let p = &mut it;
    *p = b.bytes();
    match it.position(|c| c == b'/') {
        Some(i) => a.as_bytes()[i],
        None => 0,
    }
}

#[cfg(other_root)]
pub fn other_root(a: &str, b: &str) -> u8 {
    match a.bytes().position(|c| c == b'/') {
        Some(i) => b.as_bytes()[i],
        None => 0,
    }
}

#[cfg(user_position)]
pub struct Liar;

#[cfg(user_position)]
impl Iterator for Liar {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        None
    }
    fn position<P: FnMut(u8) -> bool>(&mut self, _: P) -> Option<usize> {
        Some(usize::MAX)
    }
}

#[cfg(user_position)]
pub fn user_position() -> usize {
    match Liar.position(|b| b == b'/') {
        Some(i) => i + 1,
        None => 0,
    }
}
