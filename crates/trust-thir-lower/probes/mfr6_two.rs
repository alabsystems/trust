// LANE MF-R6 (sixth review) — TWO PLANS, ONE BODY.
//
// `MfPlans::seal` resolves exclusivity: the field-write and interior-borrow plans are computed
// first, and `source_form_marker_plan_available` then gates the general source-form lane on BOTH
// being absent. `predict` nevertheless ADDS all four terms — the write pairs, the borrow pair, and
// the operand class — into one `MfMarkers`. If any body could ever hold two plans at once, the
// prediction would be a sum where the emitter's discipline is an alternation, and the law would be
// satisfied by the wrong body.
//
// This file is the attempt to build that body from source: a field write next to a comparison, a
// field write next to an interior borrow, an aggregate return next to a write, a borrow next to a
// branch, and each of them in both statement orders. Every row that comes back REFUSED is one more
// measured reason the exclusivity holds; a row that comes back admitted with two plans' worth of
// markers is the finding.
//
// No body name in this file appears in any of the 27 probe files rounds 1-5 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::if_same_then_else, clippy::needless_bool, clippy::useless_conversion)]

#[derive(Clone, Copy)]
pub struct Rec {
    pub a: u32,
    pub b: u32,
    pub h: u64,
}

#[derive(Clone, Copy)]
pub struct Out {
    pub p: u32,
    pub q: u32,
}

// --- A: WRITE + COMPARISON. The write plan counts source writes; the comparison mints temps the
//        write plan has no term for, so the tail clause must refuse. --------------------------

#[inline(never)]
pub fn t01_write_then_cmp_return(r: &mut Rec, a: u32, b: u32) -> bool {
    r.a = a;
    return a == b;
}

#[inline(never)]
pub fn t02_write_then_place_return(r: &mut Rec, a: u32) -> u32 {
    r.a = a;
    return r.b;
}

#[inline(never)]
pub fn t03_cmp_written_into_field(r: &mut Rec, a: u32, b: u32) {
    r.a = a;
    r.b = b;
}

#[inline(never)]
pub fn t04_two_writes_one_const(r: &mut Rec, a: u32) {
    r.a = a;
    r.b = 0;
}

#[inline(never)]
pub fn t05_write_field_from_field(r: &mut Rec) {
    r.a = r.b;
}

// --- B: WRITE + BORROW in one body, both orders. -----------------------------------------------

#[inline(never)]
pub fn t06_write_then_borrow_tail(r: &mut Rec, a: u32) -> &u64 {
    r.a = a;
    &r.h
}

#[inline(never)]
pub fn t07_borrow_only(r: &Rec) -> &u64 {
    &r.h
}

#[inline(never)]
pub fn t08_borrow_first_field(r: &Rec) -> &u32 {
    &r.a
}

#[inline(never)]
pub fn t09_borrow_of_deref<'a>(r: &&'a Rec) -> &'a u64 {
    &r.h
}

// --- C: AGGREGATE RETURN — the `agg_chains` term of `predict`, alone and beside a branch. ------

#[inline(never)]
pub fn t10_aggregate_of_params(x: u32, y: u32) -> Out {
    Out { p: x, q: y }
}

#[inline(never)]
pub fn t11_aggregate_of_fields(r: Rec) -> Out {
    Out { p: r.a, q: r.b }
}

#[inline(never)]
pub fn t12_aggregate_of_cmp_result(a: u32, b: u32) -> Out {
    Out { p: a & b, q: b }
}

#[inline(never)]
pub fn t13_aggregate_in_if_arms(c: bool, x: u32, y: u32) -> Out {
    if c { Out { p: x, q: y } } else { Out { p: y, q: x } }
}

#[inline(never)]
pub fn t14_aggregate_in_match_arms(c: bool, x: u32, y: u32) -> Out {
    match c {
        true => Out { p: x, q: y },
        false => Out { p: y, q: x },
    }
}

#[inline(never)]
pub fn t15_aggregate_of_cmp_scrutinee(a: u32, b: u32) -> Out {
    match a == b {
        true => Out { p: a, q: b },
        false => Out { p: b, q: a },
    }
}

// --- D: WRITE INSIDE A BRANCH — the write plan's straight-line grammar meets a CFG. ------------

#[inline(never)]
pub fn t16_write_in_if_arm(r: &mut Rec, c: bool, v: u32) {
    if c {
        r.a = v;
    } else {
        r.b = v;
    }
}

#[inline(never)]
pub fn t17_write_in_match_arm(r: &mut Rec, c: bool, v: u32) {
    match c {
        true => r.a = v,
        false => r.b = v,
    }
}

#[inline(never)]
pub fn t18_write_guarded_by_cmp(r: &mut Rec, a: u32, b: u32) {
    if a == b {
        r.a = a;
    }
}

// --- E: BORROW INSIDE A BRANCH, and a branch whose arms borrow different fields. ---------------

#[inline(never)]
pub fn t19_borrow_in_if_arms(r: &Rec, c: bool) -> &u32 {
    if c { &r.a } else { &r.b }
}

#[inline(never)]
pub fn t20_borrow_in_match_arms(r: &Rec, c: bool) -> &u32 {
    match c {
        true => &r.a,
        false => &r.b,
    }
}

// --- F: LOAD through a pointer beside each of the other plans. ---------------------------------

#[inline(never)]
pub fn t21_load_then_cmp(p: &u32, b: u32) -> bool {
    *p == b
}

#[inline(never)]
pub fn t22_write_then_load_cmp(r: &mut Rec, p: &u32, a: u32) -> bool {
    r.a = a;
    return *p == a;
}

#[inline(never)]
pub fn t23_match_on_load(p: &u32, a: u32, b: u32) -> u32 {
    match *p == a {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn t24_aggregate_of_loads(p: &u32, q: &u32) -> Out {
    Out { p: *p, q: *q }
}
