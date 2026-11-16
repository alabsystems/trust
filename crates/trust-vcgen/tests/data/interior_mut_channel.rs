// Interior-mutable write channels (G2 of the verifier-gaps design,
// trust-ir reports/2026-10-08-session-4b77663c/designs/trust-verifier-gaps-final.md,
// Appendix A.6): real-MIR regression guards. `Cell::get`/`set` stay calls in the
// verify MIR, so every `must_refute_*` row here refutes before and after the rule;
// these pin that the rule costs nothing on real code. Every `must_refute_*` panics
// natively with `s = [7; 4]`; every `control_*` returns 7.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]
use std::cell::{Cell, UnsafeCell};

#[inline(never)]
pub fn poke_cell(c: &Cell<usize>) {
    c.set(usize::MAX);
}
#[inline(never)]
pub fn poke_ucell(c: &UnsafeCell<usize>) {
    unsafe {
        *c.get() = usize::MAX;
    }
}
pub struct S {
    pub n: usize,
    pub c: Cell<usize>,
}
#[inline(never)]
pub fn poke_s(s: &S) {
    s.c.set(usize::MAX);
}
pub fn must_refute_local_cell_callee(s: &[u8]) -> u8 {
    let c = Cell::new(0usize);
    if c.get() < s.len() {
        poke_cell(&c);
        s[c.get()]
    } else {
        0
    }
}
pub fn must_refute_local_ucell_callee(s: &[u8]) -> u8 {
    let c = UnsafeCell::new(0usize);
    if unsafe { *c.get() } < s.len() {
        poke_ucell(&c);
        s[unsafe { *c.get() }]
    } else {
        0
    }
}
pub fn must_refute_local_cell_inline(s: &[u8]) -> u8 {
    let c = Cell::new(0usize);
    if c.get() < s.len() {
        let r = &c;
        r.set(usize::MAX);
        s[c.get()]
    } else {
        0
    }
}
pub fn must_refute_struct_cell_field(s: &[u8]) -> u8 {
    let st = S { n: 1, c: Cell::new(0) };
    if st.c.get() < s.len() {
        poke_s(&st);
        s[st.c.get()]
    } else {
        0
    }
}
pub fn control_struct_frozen_sibling(s: &[u8]) -> u8 {
    let st = S { n: 0, c: Cell::new(0) };
    if st.n < s.len() {
        poke_s(&st);
        s[st.n]
    } else {
        0
    }
}
pub fn must_refute_cell_param(c: &Cell<usize>, s: &[u8]) -> u8 {
    if c.get() < s.len() {
        poke_cell(c);
        s[c.get()]
    } else {
        0
    }
}
pub fn must_refute_ucell_param_inline(c: &UnsafeCell<usize>, s: &[u8]) -> u8 {
    if unsafe { *c.get() } < s.len() {
        unsafe {
            *c.get() = usize::MAX;
        }
        s[unsafe { *c.get() }]
    } else {
        0
    }
}
pub fn must_refute_cell_array(s: &[u8]) -> u8 {
    let arr = [Cell::new(0usize), Cell::new(0usize)];
    if arr[0].get() < s.len() {
        poke_cell(&arr[0]);
        s[arr[0].get()]
    } else {
        0
    }
}
pub struct Holder<'a> {
    pub r: &'a Cell<usize>,
}
#[inline(never)]
pub fn poke_holder(h: &Holder) {
    h.r.set(usize::MAX);
}
pub fn must_refute_cell_through_holder(s: &[u8]) -> u8 {
    let c = Cell::new(0usize);
    let h = Holder { r: &c };
    if c.get() < s.len() {
        poke_holder(&h);
        s[c.get()]
    } else {
        0
    }
}
const ZC: Cell<usize> = Cell::new(0);
pub fn must_refute_const_cell_transmute(s: &[u8]) -> u8 {
    if s.is_empty() {
        return 0;
    }
    let c = ZC;
    poke_cell(&c);
    let x: usize = unsafe { std::mem::transmute::<Cell<usize>, usize>(c) };
    s[x]
}
pub fn must_refute_transmute_in_out_poke(s: &[u8]) -> u8 {
    if s.is_empty() {
        return 0;
    }
    let c: Cell<usize> = unsafe { std::mem::transmute::<usize, Cell<usize>>(0) };
    poke_cell(&c);
    let x: usize = unsafe { std::mem::transmute::<Cell<usize>, usize>(c) };
    s[x]
}
pub struct W {
    pub n: usize,
    pub c: Cell<usize>,
}
#[inline(never)]
pub fn poke_w(w: &W) {
    w.c.set(usize::MAX);
}
pub fn control_struct_plain_sibling(s: &[u8]) -> u8 {
    if s.is_empty() {
        return 0;
    }
    let w = W { n: 0, c: unsafe { std::mem::transmute::<usize, Cell<usize>>(0) } };
    poke_w(&w);
    s[w.n]
}
pub fn control_tuple_plain_sibling(s: &[u8]) -> u8 {
    if s.is_empty() {
        return 0;
    }
    let t = (ZC, 0usize);
    poke_cell(&t.0);
    s[t.1]
}
