// UNION-SIBLING-WRITE-2 (review of INTERVAL-WRITE-LOCKSTEP-2, 2026-10-12): a write to a
// union field THROUGH A POINTER rewrites its siblings too. UNION-SIBLING-WRITE-1 gave a
// direct field write (`u.b = n`) the union cover, but took it on the syntactic place: a
// store `*r = n` through `r = &mut u.b` is NAMED `u.1` (the referent fold) while its
// place `(*r)` has no field projection, so no cover; and a pointer into a union field
// handed to a callee, or stored through after it reached a pointer the fold cannot
// resolve, put only `u.1` on the havoc list. Every `r_*` function below panics for some
// input (verify-off, and stock rustc): `r_ref(MAX, 7)`, `r_nested(MAX, 7)`,
// `r_narrow(MAX, 0)`, `r_call(MAX, 7)`, `r_two(MAX, 7)`, `r_param(&mut U { a: 0 }, 7)`.
// The `c_*` functions are correct on every input: the same shapes over a STRUCT, whose
// fields are disjoint, and a store through `&mut u.a` read back through `u.a`.
#![allow(dead_code, unused_unsafe)]

pub union U { pub a: usize, pub b: usize }
pub union V { pub a: u8, pub b: i8 }
pub struct S { pub k: usize, pub u: U }
pub struct P { pub a: usize, pub b: usize }

#[inline(never)]
fn set(r: &mut usize, v: usize) {
    *r = v;
}

#[inline(never)]
fn set_b(r: &mut U, v: usize) {
    r.b = v;
}

#[inline(never)]
fn set_pb(r: &mut P, v: usize) {
    r.b = v;
}

// `&mut u.b` held in a local and stored through.
pub fn r_ref(m: usize, n: usize) -> usize {
    let mut u = U { a: 0 };
    u.a = 5;
    let r: &mut usize = unsafe { &mut u.b };
    *r = n;
    let y = unsafe { u.a };
    y + (usize::MAX - 5)
}
// The union nested in a struct: `&mut s.u.b`.
pub fn r_nested(m: usize, n: usize) -> usize {
    let mut s = S { k: 1, u: U { a: 0 } };
    s.u.a = 5;
    let r: &mut usize = unsafe { &mut s.u.b };
    *r = n;
    let y = unsafe { s.u.a };
    y + (usize::MAX - 5)
}
// The narrowing fixture's `narrow_dst` with the sibling store through a reference.
pub fn r_narrow(m: usize, n: usize) -> usize {
    let x = n as u32;
    let mut v = V { a: 0 };
    v.a = x as u8;
    let r: &mut i8 = unsafe { &mut v.b };
    *r = -56;
    if x < 0x80 { ((unsafe { v.a }) + 0x7f) as usize } else { 0 }
}
// A callee writes through `&mut u.b`.
pub fn r_call(m: usize, n: usize) -> usize {
    let mut u = U { a: 0 };
    u.a = 5;
    set(unsafe { &mut u.b }, n);
    let y = unsafe { u.a };
    y + (usize::MAX - 5)
}
// A two-referent `&mut` (into `u.b` or a separate local): the store is opaque.
pub fn r_two(m: usize, n: usize) -> usize {
    let mut u = U { a: 0 };
    let mut other = 0usize;
    u.a = 5;
    let r: &mut usize = if m > 3 { unsafe { &mut u.b } } else { &mut other };
    *r = n;
    let y = unsafe { u.a };
    y + (usize::MAX - 5)
}
// A callee writes a union field through a `&mut U` PARAMETER the caller passes on.
pub fn r_param(p: &mut U, n: usize) -> usize {
    p.a = 5;
    set_b(p, n);
    let y = unsafe { p.a };
    y + (usize::MAX - 5)
}

// Controls: the same shapes over a struct, and a write read back through itself.
pub fn c_ref(m: usize, n: usize) -> usize {
    let mut s = P { a: 0, b: 0 };
    s.a = 5;
    let r: &mut usize = &mut s.b;
    *r = n;
    s.a + (usize::MAX - 5)
}
pub fn c_call(m: usize, n: usize) -> usize {
    let mut s = P { a: 0, b: 0 };
    s.a = 5;
    set(&mut s.b, n);
    s.a + (usize::MAX - 5)
}
pub fn c_param(p: &mut P, n: usize) -> usize {
    p.a = 5;
    set_pb(p, n);
    p.a + (usize::MAX - 5)
}
pub fn c_self(m: usize, n: usize) -> usize {
    let mut u = U { a: 0 };
    let r: &mut usize = unsafe { &mut u.a };
    *r = 5;
    let y = unsafe { u.a };
    y + (usize::MAX - 5)
}
