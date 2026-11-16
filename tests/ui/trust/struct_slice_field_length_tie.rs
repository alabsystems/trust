//@ needs-trust-verify
//@ edition: 2021
//@ revisions: ref_struct by_value cursor unguarded reseat other_field
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[ref_struct] check-pass
//@[by_value] check-pass
//@[cursor] check-pass
//@[unguarded] check-fail
//@[reseat] check-fail
//@[other_field] check-fail
//! **A guarded index through a struct's slice field keeps its length (Trust, 2026-09-28;
//! DQ W-D2a/W-D2b).**
//!
//! `if i < p.s.len() { p.s[i] }` reads `p.s` three times. Each read is a fresh copy
//! (`_8`, `_9`, `_10 = copy (*_1).0`). The index row reads `_10`'s length, and `_10`'s one
//! definition, `_10__slice_len == p*.0__slice_len`, sits in the index's OWN block,
//! just before it. vcgen's rvalue lane conjoined the dominating blocks' definitions
//! (through the path guards) but never the row's own block's, so the row was refuted
//! with `_10__slice_len = 0`. That is a false refutation under every policy, the default
//! included, so a `Cursor { buf, pos }` with a guarded `peek` failed to build. A plain
//! slice parameter proved, because its read needs no copy. The rvalue lane now conjoins
//! the same-block copy ties at the row's statement, and renames the row at its own use
//! point, as `generate_v2_safety_vcs` does.
//!
//! * `ref_struct`, `by_value`, `cursor`: POSITIVE.
//! * `unguarded`, `reseat`, `other_field`: the NEGATIVES, each annotated on `f`. A tie
//!   joins only a true, versioned equality, so an unguarded index, a field reseated to
//!   another slice after the guard, and a guard on a different field stay refuted.

#[cfg(any(ref_struct, by_value, unguarded))]
pub struct P<'a> {
    pub s: &'a [u32],
}

#[cfg(ref_struct)]
pub fn f(p: &P, i: usize) -> u32 {
    if i < p.s.len() { p.s[i] } else { 0 }
}

#[cfg(by_value)]
pub fn f(p: P, i: usize) -> u32 {
    if i < p.s.len() { p.s[i] } else { 0 }
}

#[cfg(cursor)]
pub struct Cursor<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
}

#[cfg(cursor)]
impl<'a> Cursor<'a> {
    pub fn peek(&self) -> Option<u8> {
        if self.pos < self.buf.len() { Some(self.buf[self.pos]) } else { None }
    }
}

#[cfg(unguarded)]
pub fn f(p: &P, i: usize) -> u32 {
    //[unguarded]~^ ERROR Trust Level 0 safety verification incomplete for `struct_slice_field_length_tie::f`
    p.s[i]
}

#[cfg(reseat)]
pub struct P<'a> {
    pub s: &'a [u32],
}

#[cfg(reseat)]
pub fn f<'a>(p: &mut P<'a>, q: &'a [u32], i: usize) -> u32 {
    //[reseat]~^ ERROR Trust Level 0 safety verification incomplete for `struct_slice_field_length_tie::f`
    if i < p.s.len() {
        p.s = q;
        p.s[i]
    } else {
        0
    }
}

#[cfg(other_field)]
pub struct P<'a> {
    pub s: &'a [u32],
    pub t: &'a [u32],
}

#[cfg(other_field)]
pub fn f(p: &P, i: usize) -> u32 {
    //[other_field]~^ ERROR Trust Level 0 safety verification incomplete for `struct_slice_field_length_tie::f`
    if i < p.s.len() { p.t[i] } else { 0 }
}
