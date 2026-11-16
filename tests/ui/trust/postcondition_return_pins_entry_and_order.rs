//@ revisions: enum_alias_after_copy param_field_write param_field_vacuous
//@ revisions: local_rewritten_debuginfo local_rewritten_vacuous_debuginfo local_tuple_compound
//@ revisions: ancestor_write_debuginfo
//@[ancestor_write_debuginfo] compile-flags: -Cdebuginfo=2
//@[local_rewritten_debuginfo] compile-flags: -Cdebuginfo=2
//@[local_rewritten_vacuous_debuginfo] compile-flags: -Cdebuginfo=2
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Review round 44 (2026-10-02), each PROVED and kernel-certified before, each
//! refuted by a run. `enum_alias_after_copy`: the Option/Result return resolver hopped
//! `_0 <- t <- r` and took `r`'s LAST assignment, made after `let t = r`, so
//! `r.is_some()` held of a `None` return. `param_field_write`: a write to a FIELD of a
//! by-value parameter was not a mutation, so `ensures result == s.a` read the final
//! field. `param_field_vacuous`: after `s.a += 1` the bare return pin read `s.a`
//! under its ENTRY name and contradicted the versioned pin, so a false clause was
//! proved vacuously. Review round 45: the same bare-name defect for LOCALS. A return
//! pin, or the hop's `_L == value` pin, named a local rewritten inside the
//! predecessor/return window by its bare name while the block defs named its other
//! value, so `let mut r = x; r = r + 1; r` gave `_2 == _2 + 1` and every clause
//! proved (`-Cdebuginfo=2`, cargo's dev profile), and `t.0 += k; t.0` pinned both
//! versions at every level. `ancestor_write_debuginfo`: with the first write in a
//! block BEFORE the window (`c = x; side(); c = c + 1; c`), a one-write-in-window
//! rule still pinned the stale `c` (measured while fixing round 45).
#![cfg_attr(enum_alias_after_copy, feature(contracts))]
#![allow(incomplete_features, unused_assignments, unused_variables)]

#[cfg(enum_alias_after_copy)]
#[core::contracts::ensures(|r: &Option<u8>| r.is_some())]
pub fn f(a: u8) -> Option<u8> {
    let mut r: Option<u8> = None;
    let t = r;
    r = Some(a);
    t
}

#[cfg(any(param_field_write, param_field_vacuous))]
pub struct S {
    pub a: u32,
    pub b: u32,
}

#[cfg(param_field_write)]
pub fn f(mut s: S) -> u32 //[param_field_write]~ ERROR verification
    ensures result == s.a
{
    s.a = 0;
    s.a
}

#[cfg(param_field_vacuous)]
pub fn f(mut s: S) -> u32 //[param_field_vacuous]~ ERROR verification
    requires s.a < 100
    ensures result == 12345
{
    s.a += 1;
    s.a
}

#[cfg(local_rewritten_debuginfo)]
pub fn f(x: u32) -> u32 //[local_rewritten_debuginfo]~ ERROR verification
    requires x < 100
    ensures result == x
{
    let mut r = x;
    r = r + 1;
    r
}

#[cfg(local_rewritten_vacuous_debuginfo)]
pub fn f(x: u32) -> u32 //[local_rewritten_vacuous_debuginfo]~ ERROR verification
    requires x < 100
    ensures result == 12345
{
    let mut r = x;
    r = r + 1;
    r
}

#[cfg(local_tuple_compound)]
pub fn f(x: u32, k: u32) -> u32 //[local_tuple_compound]~ ERROR verification
    requires x < 100 && k < 100
    ensures result == x
{
    let mut t = (x, 0u32);
    t.0 += k;
    t.0
}

#[cfg(ancestor_write_debuginfo)]
#[inline(never)]
pub fn side() {}

#[cfg(ancestor_write_debuginfo)]
pub fn f(x: u32) -> u32 //[ancestor_write_debuginfo]~ ERROR verification
    requires x < 100
    ensures result == x
{
    let mut c = x;
    side();
    c = c + 1;
    c
}
