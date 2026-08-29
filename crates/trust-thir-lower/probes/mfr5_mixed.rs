// LANE MF-R5 — THE OTHER TWO SITES, AND THE SEAMS BETWEEN PLANS.
//
// Three of the gate's five sites are authorised by `mf_plan`; the other two have their own
// plans and their own body-end arithmetic. `MfSite::InteriorBorrow` is authorised by a single
// BOOLEAN (`cx.mf_borrow`), and its ledger admits "at most `usize::from(cx.mf_borrow)`" pairs —
// which is a bound on how many markers a plan permits, expressed in terms of a field any arm in
// the module can write. This file populates the interior-borrow neighbourhood and the seams
// where two plans meet, so a driver that reaches one site's lease from another site's arm shows
// up as a bucket change rather than as a compile error.
//
// No body name here appears in any of the 22 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr5_mixed \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr5_mixed.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::needless_borrow)]
#![allow(clippy::no_effect, clippy::never_loop, clippy::unnecessary_cast)]

#[derive(Clone, Copy)]
pub struct M5 {
    pub u: u32,
    pub v: u32,
    pub w: u64,
    pub f: bool,
}

#[derive(Clone, Copy)]
pub struct Holder {
    pub one: M5,
    pub two: M5,
}

// --- A: the interior-borrow tail — `&place` as the body's whole expression. -----------------

#[inline(never)]
pub fn n01_borrow_field(m: &M5) -> &u32 {
    &m.u
}

#[inline(never)]
pub fn n02_borrow_nested_field(h: &Holder) -> &u32 {
    &h.one.v
}

#[inline(never)]
pub fn n03_borrow_wide_field(m: &M5) -> &u64 {
    &m.w
}

#[inline(never)]
pub fn n04_borrow_whole(m: &M5) -> &M5 {
    m
}

#[inline(never)]
pub fn n05_borrow_mut_field(m: &mut M5) -> &mut u32 {
    &mut m.u
}

// --- B: a borrow next to something else — the plan admits ONE pair, so a second reborrow is a
//        body the plan did not describe and must fail CLOSED. --------------------------------

#[inline(never)]
pub fn n06_borrow_after_let(m: &M5) -> &u32 {
    let t = 0u32;
    &m.u
}

#[inline(never)]
pub fn n07_borrow_under_if<'a>(m: &'a M5, c: bool) -> &'a u32 {
    if c { &m.u } else { &m.v }
}

#[inline(never)]
pub fn n08_borrow_of_field_of_field(h: &Holder) -> &u64 {
    &h.two.w
}

// --- C: aggregates — a struct literal materialises a temp per field in source order. --------

#[inline(never)]
pub fn n09_agg_two_places(a: u32, b: u32) -> M5 {
    M5 { u: a, v: b, w: 0, f: false }
}

#[inline(never)]
pub fn n10_agg_out_of_source_order(a: u32, b: u32) -> M5 {
    M5 { v: b, u: a, w: 1, f: true }
}

#[inline(never)]
pub fn n11_agg_all_const() -> M5 {
    M5 { u: 1, v: 2, w: 3, f: true }
}

#[inline(never)]
pub fn n12_agg_from_fields(m: M5) -> M5 {
    M5 { u: m.v, v: m.u, w: m.w, f: m.f }
}

#[inline(never)]
pub fn n13_agg_nested(a: u32, b: u32) -> Holder {
    Holder { one: M5 { u: a, v: b, w: 0, f: false }, two: M5 { u: b, v: a, w: 1, f: true } }
}

// --- D: the seam — a body that holds a field write AND a borrow, or a write AND an operand
//        tree, so more than one plan has an opinion and they are mutually exclusive. ---------

#[inline(never)]
pub fn n14_write_then_borrow<'a>(m: &'a mut M5, x: u32) -> &'a u32 {
    m.u = x;
    &m.v
}

#[inline(never)]
pub fn n15_borrow_arg_then_compare(m: &M5, a: u32) -> bool {
    m.u == a
}

#[inline(never)]
pub fn n16_write_then_agg(m: &mut M5, a: u32, b: u32) -> M5 {
    m.u = a;
    M5 { u: a, v: b, w: 0, f: false }
}

#[inline(never)]
pub fn n17_agg_then_field_read(a: u32) -> u32 {
    let t = M5 { u: a, v: a, w: 0, f: false };
    t.v
}

// --- E: bodies that must stay OUT of every plan — the population where a marker of any kind
//        is a marker no plan sanctioned. ------------------------------------------------------

#[inline(never)]
pub fn n18_while_loop_sum(n: u32) -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    while i < n {
        s = s ^ i;
        i = i + 1;
    }
    s
}

#[inline(never)]
pub fn n19_early_return_chain(a: u32, b: u32) -> u32 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    a & b
}

#[inline(never)]
pub fn n20_shadowed_lets(a: u32) -> u32 {
    let x = a;
    let x = x & 1;
    let x = x | 2;
    x
}

#[inline(never)]
pub fn n21_tuple_bind(a: u32, b: u32) -> u32 {
    let (x, y) = (a, b);
    x & y
}

#[inline(never)]
pub fn n22_destructured_param(p: (u32, u32)) -> u32 {
    let (x, y) = p;
    x | y
}

#[inline(never)]
pub fn n23_nested_fn_item(a: u32) -> u32 {
    fn inner(z: u32) -> u32 {
        z & 3
    }
    inner(a)
}

#[inline(never)]
pub fn n24_closure_call(a: u32, b: u32) -> u32 {
    let f = |x: u32, y: u32| x ^ y;
    f(a, b)
}
