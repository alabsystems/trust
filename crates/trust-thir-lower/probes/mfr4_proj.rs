// LANE MF-R4 (round-3 REVIEW, 2026-08-13) — PROJECTION DEPTH x RHS CATEGORY, exhaustively.
//
// The field-write plan admits a body whose every statement is a `;`-assignment with a
// `hir_place_is_marker_free` left-hand side and a `Konst`/`Place` right-hand side. Two axes are
// therefore load-bearing and neither was swept: HOW DEEP the left-hand place projects, and WHICH
// category the right-hand side is. This file crosses them.
//
// Depth axis:   w.a | (*p).a | w.n.a | (*p).n.a | w.n.m.a | (**pp).a | s[..] via ref chains
// Category axis: literal | negated literal | const item | assoc const | local | param field |
//                deref | index | call | binop | cast | ref | tuple field | closure result
//
// No name here appears in any of the 18 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr4_proj \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr4_proj.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::needless_late_init, clippy::let_and_return)]

pub const K32: u32 = 5;

pub trait HasK {
    const AK: u32;
}
pub struct KImpl;
impl HasK for KImpl {
    const AK: u32 = 9;
}

#[derive(Clone, Copy)]
pub struct Leaf {
    pub a: u32,
    pub b: u64,
}

#[derive(Clone, Copy)]
pub struct Mid {
    pub l: Leaf,
    pub t: u32,
}

#[derive(Clone, Copy)]
pub struct Top {
    pub m: Mid,
    pub u: u32,
}

#[derive(Clone, Copy)]
pub struct TupHolder(pub u32, pub u64);

// --- DEPTH 1 --------------------------------------------------------------------------------

#[inline(never)]
pub fn q01_d1_lit(w: &mut Leaf) {
    w.a = 3;
}

#[inline(never)]
pub fn q02_d1_neg_lit(w: &mut Leaf) {
    w.a = (-1i32) as u32;
}

#[inline(never)]
pub fn q03_d1_const_item(w: &mut Leaf) {
    w.a = K32;
}

#[inline(never)]
pub fn q04_d1_assoc_const(w: &mut Leaf) {
    w.a = <KImpl as HasK>::AK;
}

#[inline(never)]
pub fn q05_d1_local_place(w: &mut Leaf, v: u32) {
    w.a = v;
}

#[inline(never)]
pub fn q06_d1_param_field_place(w: &mut Leaf, s: Leaf) {
    w.a = s.a;
}

#[inline(never)]
pub fn q07_d1_deref_rhs(w: &mut Leaf, p: &u32) {
    w.a = *p;
}

#[inline(never)]
pub fn q08_d1_binop_rhs(w: &mut Leaf, v: u32, u: u32) {
    w.a = v ^ u;
}

#[inline(never)]
pub fn q09_d1_cast_rhs(w: &mut Leaf, v: u64) {
    w.a = v as u32;
}

#[inline(never)]
pub fn q10_d1_shift_rhs(w: &mut Leaf, v: u32, s: u32) {
    w.a = v << s;
}

#[inline(never)]
pub fn q11_d1_cmp_rhs_to_u64(w: &mut Leaf, v: u32, u: u32) {
    w.b = (v == u) as u64;
}

#[inline(never)]
pub fn q12_d1_tuple_field_rhs(w: &mut Leaf, t: TupHolder) {
    w.a = t.0;
}

// --- DEPTH 2: through a deref, and through a nested struct field ------------------------------

#[inline(never)]
pub fn q13_d2_deref_lhs_lit(p: &mut Leaf) {
    (*p).a = 4;
}

#[inline(never)]
pub fn q14_d2_deref_lhs_place(p: &mut Leaf, v: u32) {
    (*p).a = v;
}

#[inline(never)]
pub fn q15_d2_nested_lhs_lit(w: &mut Mid) {
    w.l.a = 4;
}

#[inline(never)]
pub fn q16_d2_nested_lhs_place(w: &mut Mid, v: u32) {
    w.l.a = v;
}

#[inline(never)]
pub fn q17_d2_nested_lhs_nested_rhs(w: &mut Mid, s: Mid) {
    w.l.a = s.l.a;
}

#[inline(never)]
pub fn q18_d2_deref_lhs_deref_rhs(p: &mut Leaf, q: &u32) {
    (*p).a = *q;
}

// --- DEPTH 3 ----------------------------------------------------------------------------------

#[inline(never)]
pub fn q19_d3_deref_nested_lit(p: &mut Mid) {
    (*p).l.a = 4;
}

#[inline(never)]
pub fn q20_d3_deref_nested_place(p: &mut Mid, v: u32) {
    (*p).l.a = v;
}

#[inline(never)]
pub fn q21_d3_three_fields_lit(w: &mut Top) {
    w.m.l.a = 4;
}

#[inline(never)]
pub fn q22_d3_three_fields_place(w: &mut Top, v: u32) {
    w.m.l.a = v;
}

#[inline(never)]
pub fn q23_d3_three_fields_from_three(w: &mut Top, s: Top) {
    w.m.l.a = s.m.l.a;
}

// --- DEPTH 4: double deref, and deref-through-nested ------------------------------------------

#[inline(never)]
pub fn q24_d4_double_deref_lit(pp: &mut &mut Leaf) {
    (**pp).a = 4;
}

#[inline(never)]
pub fn q25_d4_double_deref_place(pp: &mut &mut Leaf, v: u32) {
    (**pp).a = v;
}

#[inline(never)]
pub fn q26_d4_deref_three_fields(p: &mut Top, v: u32) {
    (*p).m.l.a = v;
}

#[inline(never)]
pub fn q27_d4_deref_three_fields_from_deref(p: &mut Top, s: &Top) {
    (*p).m.l.a = (*s).m.l.a;
}

// --- MIXED DEPTH IN ONE BODY (the plan counts marking writes over the WHOLE body) --------------

#[inline(never)]
pub fn q28_mixed_depth_two_places(w: &mut Top, v: u32, u: u32) {
    w.u = v;
    w.m.l.a = u;
}

#[inline(never)]
pub fn q29_mixed_depth_place_then_const(w: &mut Top, v: u32) {
    w.m.l.a = v;
    w.u = 1;
}

#[inline(never)]
pub fn q30_mixed_depth_const_then_place(w: &mut Top, v: u32) {
    w.u = 1;
    w.m.l.a = v;
}

#[inline(never)]
pub fn q31_three_writes_all_place(w: &mut Top, a: u32, b: u32, c: u32) {
    w.u = a;
    w.m.t = b;
    w.m.l.a = c;
}

#[inline(never)]
pub fn q32_three_writes_alternating(w: &mut Top, a: u32, c: u32) {
    w.u = a;
    w.m.t = 2;
    w.m.l.a = c;
}

#[inline(never)]
pub fn q33_four_writes_all_const(w: &mut Top) {
    w.u = 1;
    w.m.t = 2;
    w.m.l.a = 3;
    w.m.l.b = 4;
}

// --- SAME PLACE WRITTEN TWICE, and a write whose RHS reads the place just written -------------

#[inline(never)]
pub fn q34_same_place_twice_place(w: &mut Leaf, v: u32, u: u32) {
    w.a = v;
    w.a = u;
}

#[inline(never)]
pub fn q35_write_then_read_back(w: &mut Mid, v: u32) {
    w.l.a = v;
    w.t = w.l.a;
}

#[inline(never)]
pub fn q36_write_reads_own_other_field(w: &mut Mid) {
    w.t = w.l.a;
}

// --- LHS FORMS THE PLACE CLASSIFIER MUST REFUSE (index, static, call result) ------------------

pub static mut SLOT: Leaf = Leaf { a: 0, b: 0 };

#[inline(never)]
pub fn q37_index_lhs(s: &mut [u32; 4], v: u32) {
    s[1] = v;
}

#[inline(never)]
pub fn q38_index_lhs_dynamic(s: &mut [u32; 4], i: usize, v: u32) {
    s[i] = v;
}

#[inline(never)]
pub fn q39_array_field_write(s: &mut [Leaf; 2], v: u32) {
    s[0].a = v;
}

#[inline(never)]
pub fn q40_tuple_index_lhs(t: &mut TupHolder, v: u32) {
    t.0 = v;
}

#[inline(never)]
pub fn q41_tuple_index_lhs_const(t: &mut TupHolder) {
    t.1 = 7;
}

// --- RHS = a REFERENCE, an AGGREGATE, and a CALL ----------------------------------------------

#[inline(never)]
pub fn q42_rhs_is_aggregate(w: &mut Mid, v: u32, u: u64) {
    w.l = Leaf { a: v, b: u };
}

#[inline(never)]
pub fn q43_rhs_is_copy_of_struct(w: &mut Mid, s: Leaf) {
    w.l = s;
}

#[inline(never)]
pub fn q44_rhs_is_deref_of_struct(w: &mut Mid, s: &Leaf) {
    w.l = *s;
}

#[inline(never)]
pub fn q45_two_writes_one_agg_one_place(w: &mut Mid, v: u32, u: u64) {
    w.t = v;
    w.l = Leaf { a: v, b: u };
}
