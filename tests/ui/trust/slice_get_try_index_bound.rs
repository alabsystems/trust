//@ needs-trust-verify
//@ edition: 2021
//@ revisions: local field other_slice join_match join_try dup_target
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[local] check-pass
//@[field] check-pass
//@[other_slice] check-fail
//@[join_match] check-fail
//@[join_try] check-fail
//@[dup_target] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-04): `slice.get(i)?` — the `?` spelling of the `<[T]>::get`
//! Some-index bound. Core's `Try::branch` turns `Some(x)` into `Continue(x)`, so the
//! `Continue` arm knows `i < slice.len()` and `i + 1` cannot overflow
//! (`guards::slice_get_some_index_bound_definitions`).
//!
//! # Before (measured on the stage 1 of `020f50ec4c`, 2026-10-04)
//!
//! `local` and `field` were `[overflow:add] FAILED` with `i = 18446744073709551615`.
//! `field` is a3d_wire's `Parser::bump` shape.
//!
//! # The refused rail
//!
//! * `other_slice` — the bound is on `a`'s length; `b[i]` panics when `b` is shorter.
//! * `join_match`, `join_try` — `if c { a.get(i) } else { b.get(j) }`: both calls
//!   target ONE switch block, so its `Some` arm knows neither bound; `a[i]` panics
//!   for `c = false, a = [], b = [1]`. Both PROVED (a false proof) on that stage 1,
//!   the `match` one through the pre-existing lane; every hop block must now be
//!   entered only from the previous hop.
//! * `dup_target` (VARIANT-ARM-DUP-EDGE-1, 2026-10-06) — `match a.get(i) { Some(_) =>
//!   {}, None => {} }; a[i]`: rustc -O0 switches `[0: bb3, 1: bb3, otherwise: bb2]`, so
//!   the join `bb3` that `None` also enters was taken for the `Some` arm (the
//!   predecessor relation deduplicated the two edges) and `a[i]` PROVED — `2 proved,
//!   0 failed` on a stage 1 reporting `0c4b132ee` — although `a = [], i = 0` panics.
//!   The arm must now be the only one of the switch's edges into it.

#[cfg(local)]
pub fn local(b: &[u8], i: usize) -> Option<usize> {
    let _c = b.get(i)?;
    Some(i + 1)
}

#[cfg(field)]
pub struct P<'a> {
    pub b: &'a [u8],
    pub i: usize,
}

#[cfg(field)]
impl P<'_> {
    pub fn bump(&mut self) -> Option<u8> {
        let c = *self.b.get(self.i)?;
        self.i += 1;
        Some(c)
    }
}

#[cfg(other_slice)]
pub fn other_slice(a: &[u8], b: &[u8], i: usize) -> Option<u8> {
    let _c = a.get(i)?;
    Some(b[i])
}

#[cfg(join_match)]
pub fn join_match(c: bool, a: &[u8], b: &[u8], i: usize, j: usize) -> u8 {
    let o = if c { a.get(i) } else { b.get(j) };
    match o {
        Some(_) => a[i],
        None => 0,
    }
}

#[cfg(join_try)]
pub fn join_try(c: bool, a: &[u8], b: &[u8], i: usize, j: usize) -> Option<u8> {
    let _x = if c { a.get(i) } else { b.get(j) }?;
    Some(a[i])
}

#[cfg(dup_target)]
pub fn dup_target(a: &[u8], i: usize) -> u8 {
    match a.get(i) {
        Some(_) => {}
        None => {}
    }
    a[i]
}
