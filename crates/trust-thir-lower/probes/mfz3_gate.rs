// LANE MF-ZERO-3 (round 3, 2026-08-13) — THE CORPUS THIS LANE WROTE AGAINST ITS OWN FIX.
//
// Rounds 1 and 2 each claimed the admitted-and-wrong marker residual was zero and each died to a
// corpus its author had not written. The lesson taken here is not "write a better predicate", it
// is "write the corpus that would kill you, before somebody else does". Every body below probes a
// decision lane MF-ZERO-3 introduced:
//
//   GROUP T — the TAIL, around a field write. The plan admits a tail that mints no marker; these
//     enumerate the spellings that do and do not. `t01_tail_assign_place` is the body that this
//     file caught: `{ w.a = v }` and `{ w.a = v; }` are the same PROGRAM and NOT the same marker
//     sequence — built's `StorageDead` sits one statement later in the tail spelling — so the
//     plan's first draft, which treated a tail assignment as just another write, was wrong and
//     this body was ADMITTED-AND-WRONG until it was measured.
//   GROUP U — the STATEMENT list: items, empty bodies, several writes, mixed RHS classes.
//   GROUP V — the LEFT-HAND SIDE and the parameter list.
//   GROUP B — wave-29b's interior-borrow site, now gated by `plan_interior_borrow_markers`.
//   GROUP P — the `permutation_is_observable` deref narrowing, at every field index and count.
//   GROUP X — a write beside every construct that mints a built marker elsewhere in the body
//     (the shape class the third review measured at seventeen), in spellings `mfr3_wclass.rs`
//     did not use.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfz3_gate \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfz3_gate.rs --out-dir OUT

#![allow(dead_code, unused_variables, clippy::eq_op, clippy::identity_op)]
#![allow(clippy::let_and_return, clippy::needless_late_init, clippy::self_assignment)]
#![allow(clippy::unnecessary_cast, clippy::no_effect)]

#[derive(Clone, Copy)]
pub struct C3 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
}
#[derive(Clone, Copy)]
pub struct E3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct E4 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
}
#[derive(Clone, Copy)]
pub struct Mx {
    pub a: u8,
    pub b: u64,
}
#[derive(Clone, Copy)]
pub struct Slot {
    pub f: bool,
    pub g: u8,
    pub h: u64,
}
pub const K32: u32 = 3;

// =================================================================================================
// GROUP T — THE TAIL, around a field write.
// =================================================================================================

// The body this file was written to catch: a tail assignment with a PLACE right-hand side. Built
// puts the write's `StorageDead` one statement later here than in the `;` spelling.
#[inline(never)]
pub fn t01_tail_assign_place(w: &mut C3, v: u32) {
    w.a = v
}
#[inline(never)]
pub fn t02_tail_assign_const(w: &mut C3) {
    w.a = 7
}
#[inline(never)]
pub fn t03_stmt_assign_place(w: &mut C3, v: u32) {
    w.a = v;
}
#[inline(never)]
pub fn t04_write_then_unit_tail(w: &mut C3, v: u32) {
    w.a = v;
    ()
}
#[inline(never)]
pub fn t05_write_then_local_tail(w: &mut C3, v: u32, r: u32) -> u32 {
    w.a = v;
    r
}
#[inline(never)]
pub fn t06_write_then_field_tail(w: &mut C3, v: u32, s: C3) -> u32 {
    w.a = v;
    s.b
}
#[inline(never)]
pub fn t07_write_then_const_tail(w: &mut C3, v: u32) -> u32 {
    w.a = v;
    K32
}
#[inline(never)]
pub fn t08_write_then_deref_tail(w: &mut C3, v: u32, p: &u32) -> u32 {
    w.a = v;
    *p
}
#[inline(never)]
pub fn t09_write_then_deref_of_field_tail(w: &mut C3, v: u32, p: &C3) -> u32 {
    w.a = v;
    p.b
}
#[inline(never)]
pub fn t10_write_then_cast_tail(w: &mut C3, v: u32, x: u16) -> u32 {
    w.a = v;
    x as u32
}
#[inline(never)]
pub fn t11_write_then_binop_tail(w: &mut C3, v: u32, x: u32, y: u32) -> u32 {
    w.a = v;
    x & y
}
#[inline(never)]
pub fn t12_write_then_block_tail(w: &mut C3, v: u32, r: u32) -> u32 {
    w.a = v;
    { r }
}

// =================================================================================================
// GROUP U — THE STATEMENT LIST.
// =================================================================================================

#[inline(never)]
pub fn u01_item_stmt_then_write(w: &mut C3, v: u32) {
    struct Nested;
    w.a = v;
}
#[inline(never)]
pub fn u02_write_then_item_stmt(w: &mut C3, v: u32) {
    w.a = v;
    struct Nested;
}
#[inline(never)]
pub fn u03_two_writes_place_place(w: &mut C3, v: u32, u: u32) {
    w.a = v;
    w.b = u;
}
#[inline(never)]
pub fn u04_two_writes_place_const(w: &mut C3, v: u32) {
    w.a = v;
    w.b = 1;
}
#[inline(never)]
pub fn u05_two_writes_const_place(w: &mut C3, v: u32) {
    w.a = 1;
    w.b = v;
}
#[inline(never)]
pub fn u06_two_writes_place_cast(w: &mut C3, v: u32, x: u16) {
    w.a = v;
    w.b = x as u32;
}
#[inline(never)]
pub fn u07_write_self_field(w: &mut C3) {
    w.a = w.b;
}
#[inline(never)]
pub fn u08_empty_body(w: &mut C3) {}
#[inline(never)]
pub fn u09_unit_only(w: &mut C3) {
    ()
}

// =================================================================================================
// GROUP V — THE LEFT-HAND SIDE AND THE PARAMETERS.
// =================================================================================================

#[inline(never)]
pub fn v01_wild_param_and_write(_: u32, w: &mut C3, v: u32) {
    w.a = v;
}
#[inline(never)]
pub fn v02_write_wide_field(w: &mut C3, v: u64) {
    w.c = v;
}
#[inline(never)]
pub fn v03_write_from_wide_field(w: &mut C3, s: C3) {
    w.c = s.c;
}
#[inline(never)]
pub fn v04_write_const_path(w: &mut C3) {
    w.a = K32;
}
#[inline(never)]
pub fn v05_write_neg_const(w: &mut C3) {
    w.a = -0i32 as u32;
}

// =================================================================================================
// GROUP B — THE INTERIOR-BORROW SITE (wave-29b).
// =================================================================================================

#[inline(never)]
pub fn b01_borrow_scalar_field(s: &Slot) -> &u64 {
    &s.h
}
#[inline(never)]
pub fn b02_borrow_after_item(s: &Slot) -> &u64 {
    struct Nested;
    &s.h
}
#[inline(never)]
pub fn b03_borrow_bool_field(s: &Slot) -> &bool {
    &s.f
}
#[inline(never)]
pub fn b04_borrow_byte_field(s: &Slot) -> &u8 {
    &s.g
}

// =================================================================================================
// GROUP P — THE PERMUTATION NARROWING: a `*p` field at every index, and more than one.
// =================================================================================================

#[inline(never)]
pub fn p01_deref_first_field_permuted(p: &u32, y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: *p }
}
#[inline(never)]
pub fn p02_deref_first_field_in_order(p: &u32, y: u32, z: u32) -> E3 {
    E3 { a: *p, b: y, c: z }
}
#[inline(never)]
pub fn p03_deref_middle_field_permuted(p: &u32, x: u32, z: u32) -> E3 {
    E3 { c: z, b: *p, a: x }
}
#[inline(never)]
pub fn p04_deref_last_field_permuted(p: &u32, x: u32, y: u32) -> E3 {
    E3 { c: *p, b: y, a: x }
}
#[inline(never)]
pub fn p05_two_derefs_permuted(p: &u32, q: &u32, z: u32) -> E3 {
    E3 { c: z, b: *q, a: *p }
}
#[inline(never)]
pub fn p06_deref_first_with_const(p: &u32, y: u32) -> E3 {
    E3 { c: 9, b: y, a: *p }
}
#[inline(never)]
pub fn p07_deref_first_mixed_width(p: &u8, b: u64) -> Mx {
    Mx { b, a: *p }
}
#[inline(never)]
pub fn p08_deref_first_four_fields(p: &u32, x: u32, y: u32, z: u32) -> E4 {
    E4 { d: z, c: y, b: x, a: *p }
}
#[inline(never)]
pub fn p09_deref_of_field_first_permuted(p: &E3, y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: p.a }
}

// =================================================================================================
// GROUP X — A WRITE BESIDE A CONSTRUCT THAT MINTS A BUILT MARKER ELSEWHERE.
// =================================================================================================

#[inline(never)]
pub fn x01_write_in_if_tail(c: bool, w: &mut C3, v: u32) {
    if c {
        w.a = v
    }
}
#[inline(never)]
pub fn x02_write_after_if_stmt(c: bool, w: &mut C3, v: u32) {
    if c {}
    w.a = v;
}
#[inline(never)]
pub fn x03_write_then_write_in_if(c: bool, w: &mut C3, v: u32) {
    w.a = v;
    if c {
        w.b = v;
    }
}
#[inline(never)]
pub fn x04_write_with_andand_tail(w: &mut C3, v: u32, a: bool, b: bool) -> bool {
    w.a = v;
    a && b
}
#[inline(never)]
pub fn x05_write_in_match_tail(c: bool, w: &mut C3, v: u32) {
    match c {
        true => w.a = v,
        false => (),
    }
}
#[inline(never)]
pub fn x06_write_then_shift(w: &mut C3, v: u32, x: u32) -> u32 {
    w.a = v;
    x << 1
}
#[inline(never)]
pub fn x07_write_then_struct_literal(w: &mut C3, v: u32, x: u32, y: u32, z: u32) -> E3 {
    w.a = v;
    E3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn x08_write_then_cmp(w: &mut C3, v: u32, x: u32, y: u32) -> bool {
    w.a = v;
    x == y
}
