// LANE MF-R3 (round-3 independent review, 2026-08-13) — STRUCT LITERALS, PERMUTATIONS,
// NESTED AGGREGATES, ZSTs AND FRU.
//
// The seam: built evaluates a struct literal's WRITTEN fields in SOURCE order
// (`as_rvalue`/`ExprKind::Adt` -> `as_operand` "in order given by user") while the shim mints a
// place-valued field's temp at the aggregate site in FIELD order. Round 2 narrowed the refusal to
// `permutation_is_observable`: a permutation is admitted when every written field is a
// `Category::Constant` or a same-typed `Category::Place`. This file attacks that narrowing from
// every side it has: all six permutations of a same-typed 3-field struct, the same six with a
// MIXED-type struct, permutations mixing constants with places, permutations whose fields are
// computed / deref / adjusted, four-field rotations, nested and doubly-nested aggregates, ZST and
// 1-ZST fields, and FRU whose base is a CALL.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr3_perm \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr3_perm.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, clippy::unnecessary_cast)]
#![allow(clippy::needless_late_init, clippy::redundant_field_names)]

use core::marker::PhantomData;

#[derive(Clone, Copy)]
pub struct E3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct Mx3 {
    pub a: u8,
    pub b: u32,
    pub c: u64,
}
#[derive(Clone, Copy)]
pub struct E4 {
    pub a: u16,
    pub b: u16,
    pub c: u16,
    pub d: u16,
}
#[derive(Clone, Copy)]
pub struct In2 {
    pub x: u32,
    pub y: u32,
}
#[derive(Clone, Copy)]
pub struct Out2 {
    pub i: In2,
    pub k: u32,
}
#[derive(Clone, Copy)]
pub struct Out3 {
    pub o: Out2,
    pub m: u32,
}
#[derive(Clone, Copy)]
pub struct Unit1;
#[derive(Clone, Copy)]
pub struct ZArr {
    pub a: u32,
    pub z: [u64; 0],
}
#[derive(Clone, Copy)]
pub struct ZUnit {
    pub a: u32,
    pub u: Unit1,
}
#[derive(Clone, Copy)]
pub struct ZPhantom {
    pub a: u32,
    pub p: PhantomData<u64>,
}
#[derive(Clone, Copy)]
pub struct ZFirst {
    pub z: (),
    pub a: u32,
}
#[derive(Clone, Copy)]
pub struct Src {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

pub const PK: u32 = 21;

#[inline(never)]
pub fn mk_src() -> Src {
    Src { a: 1, b: 2, c: 3 }
}
#[inline(never)]
pub fn mk_e3() -> E3 {
    E3 { a: 4, b: 5, c: 6 }
}

// =================================================================================================
// GROUP P — ALL SIX PERMUTATIONS OF A SAME-TYPED 3-FIELD STRUCT, FIELDS ALL PLACES.
// Round 2 says every one of these is INVISIBLE to the marker channel and is therefore admitted.
// =================================================================================================

#[inline(never)]
pub fn p01_abc(x: u32, y: u32, z: u32) -> E3 {
    E3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn p02_acb(x: u32, y: u32, z: u32) -> E3 {
    E3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn p03_bac(x: u32, y: u32, z: u32) -> E3 {
    E3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn p04_bca(x: u32, y: u32, z: u32) -> E3 {
    E3 { b: y, c: z, a: x }
}
#[inline(never)]
pub fn p05_cab(x: u32, y: u32, z: u32) -> E3 {
    E3 { c: z, a: x, b: y }
}
#[inline(never)]
pub fn p06_cba(x: u32, y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: x }
}

// --- the same six with FIELD READS instead of bare params (still same-typed places) --------------
#[inline(never)]
pub fn p07_reads_abc(s: Src) -> E3 {
    E3 { a: s.a, b: s.b, c: s.c }
}
#[inline(never)]
pub fn p08_reads_cba(s: Src) -> E3 {
    E3 { c: s.c, b: s.b, a: s.a }
}
#[inline(never)]
pub fn p09_reads_crossed(s: Src) -> E3 {
    E3 { c: s.a, b: s.b, a: s.c }
}
#[inline(never)]
pub fn p10_reads_bca(s: Src) -> E3 {
    E3 { b: s.a, c: s.b, a: s.c }
}

// =================================================================================================
// GROUP Q — THE SAME SIX PERMUTATIONS, MIXED FIELD TYPES. Here the TYPE SEQUENCE itself permutes,
// so the channel CAN see the order and every out-of-order literal must be refused.
// =================================================================================================

#[inline(never)]
pub fn q01_mx_abc(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn q02_mx_acb(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn q03_mx_bac(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn q04_mx_bca(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { b: y, c: z, a: x }
}
#[inline(never)]
pub fn q05_mx_cab(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { c: z, a: x, b: y }
}
#[inline(never)]
pub fn q06_mx_cba(x: u8, y: u32, z: u64) -> Mx3 {
    Mx3 { c: z, b: y, a: x }
}

// =================================================================================================
// GROUP C — PERMUTATIONS MIXING CONSTANTS WITH PLACES. A constant folds on both sides and takes no
// position; the claim is that it therefore constrains nothing. One constant in each slot, and
// permutations where the constant is what moves.
// =================================================================================================

#[inline(never)]
pub fn c01_const_first_in_order(y: u32, z: u32) -> E3 {
    E3 { a: 1, b: y, c: z }
}
#[inline(never)]
pub fn c02_const_first_out_of_order(y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: 1 }
}
#[inline(never)]
pub fn c03_const_mid_out_of_order(x: u32, z: u32) -> E3 {
    E3 { c: z, a: x, b: 2 }
}
#[inline(never)]
pub fn c04_const_last_out_of_order(x: u32, y: u32) -> E3 {
    E3 { b: y, a: x, c: 3 }
}
#[inline(never)]
pub fn c05_two_consts_out_of_order(x: u32) -> E3 {
    E3 { c: 3, a: x, b: 2 }
}
#[inline(never)]
pub fn c06_all_consts_out_of_order() -> E3 {
    E3 { c: 3, b: 2, a: 1 }
}
#[inline(never)]
pub fn c07_const_path_out_of_order(x: u32) -> E3 {
    E3 { b: PK, a: x, c: PK }
}
#[inline(never)]
pub fn c08_mixed_type_const_out_of_order(x: u8, z: u64) -> Mx3 {
    Mx3 { c: z, b: 7, a: x }
}
#[inline(never)]
pub fn c09_max_const_out_of_order(x: u32) -> E3 {
    E3 { c: u32::MAX, a: x, b: 0 }
}

// =================================================================================================
// GROUP V — PERMUTATIONS WHOSE FIELDS COMPUTE, DEREF, OR CARRY AN ADJUSTMENT. Each is claimed
// OBSERVABLE and therefore refused; a wrong answer here is admitted-and-wrong.
// =================================================================================================

#[inline(never)]
pub fn v01_computed_field_out_of_order(x: u32, y: u32, z: u32) -> E3 {
    E3 { c: z, a: x & y, b: y }
}
#[inline(never)]
pub fn v02_computed_field_in_order(x: u32, y: u32, z: u32) -> E3 {
    E3 { a: x & y, b: y, c: z }
}
#[inline(never)]
pub fn v03_deref_field_out_of_order(p: &u32, y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: *p }
}
#[inline(never)]
pub fn v04_deref_field_in_order(p: &u32, y: u32, z: u32) -> E3 {
    E3 { a: *p, b: y, c: z }
}
#[inline(never)]
pub fn v05_cast_field_out_of_order(x: u16, y: u32, z: u32) -> E3 {
    E3 { c: z, b: y, a: x as u32 }
}
#[inline(never)]
pub fn v06_cast_field_in_order(x: u16, y: u32, z: u32) -> E3 {
    E3 { a: x as u32, b: y, c: z }
}
#[inline(never)]
pub fn v07_two_computed_out_of_order(x: u32, y: u32, z: u32) -> E3 {
    E3 { b: y ^ z, a: x & y, c: z }
}
#[inline(never)]
pub fn v08_two_computed_in_order(x: u32, y: u32, z: u32) -> E3 {
    E3 { a: x & y, b: y ^ z, c: z }
}
#[inline(never)]
pub fn v09_deref_and_place_mixed(p: &u32, y: u32) -> E3 {
    E3 { b: y, a: *p, c: y }
}
#[inline(never)]
pub fn v10_nested_field_read_out_of_order(o: Out2, z: u32) -> E3 {
    E3 { c: z, b: o.i.y, a: o.i.x }
}
#[inline(never)]
pub fn v11_nested_field_read_in_order(o: Out2, z: u32) -> E3 {
    E3 { a: o.i.x, b: o.i.y, c: z }
}

// =================================================================================================
// GROUP F — FOUR FIELDS: rotations and a full reversal, all same-typed places.
// =================================================================================================

#[inline(never)]
pub fn f01_e4_in_order(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { a, b, c, d }
}
#[inline(never)]
pub fn f02_e4_rotate1(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { d, a, b, c }
}
#[inline(never)]
pub fn f03_e4_rotate2(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { c, d, a, b }
}
#[inline(never)]
pub fn f04_e4_reverse(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { d, c, b, a }
}
#[inline(never)]
pub fn f05_e4_swap_middle(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { a, c, b, d }
}
#[inline(never)]
pub fn f06_e4_swap_ends(a: u16, b: u16, c: u16, d: u16) -> E4 {
    E4 { d, b, c, a }
}

// =================================================================================================
// GROUP N — NESTED AND DOUBLY-NESTED AGGREGATES.
// =================================================================================================

#[inline(never)]
pub fn n01_nested_in_order(x: u32, y: u32, k: u32) -> Out2 {
    Out2 { i: In2 { x, y }, k }
}
#[inline(never)]
pub fn n02_nested_outer_out_of_order(x: u32, y: u32, k: u32) -> Out2 {
    Out2 { k, i: In2 { x, y } }
}
#[inline(never)]
pub fn n03_nested_inner_out_of_order(x: u32, y: u32, k: u32) -> Out2 {
    Out2 { i: In2 { y, x }, k }
}
#[inline(never)]
pub fn n04_nested_both_out_of_order(x: u32, y: u32, k: u32) -> Out2 {
    Out2 { k, i: In2 { y, x } }
}
#[inline(never)]
pub fn n05_double_nested_in_order(x: u32, y: u32, k: u32, m: u32) -> Out3 {
    Out3 { o: Out2 { i: In2 { x, y }, k }, m }
}
#[inline(never)]
pub fn n06_double_nested_out_of_order(x: u32, y: u32, k: u32, m: u32) -> Out3 {
    Out3 { m, o: Out2 { k, i: In2 { y, x } } }
}
#[inline(never)]
pub fn n07_nested_with_computed(x: u32, y: u32, k: u32) -> Out2 {
    Out2 { i: In2 { x: x & y, y }, k }
}
#[inline(never)]
pub fn n08_nested_read_from_nested(o: Out2) -> Out2 {
    Out2 { i: In2 { x: o.i.y, y: o.i.x }, k: o.k }
}
#[inline(never)]
pub fn n09_nested_all_const() -> Out2 {
    Out2 { i: In2 { x: 1, y: 2 }, k: 3 }
}
#[inline(never)]
pub fn n10_double_nested_all_const() -> Out3 {
    Out3 { o: Out2 { i: In2 { x: 1, y: 2 }, k: 3 }, m: 4 }
}

// =================================================================================================
// GROUP Z — ZST AND 1-ZST FIELDS. `()` and a unit struct are 1-ZST; `[u64; 0]` is a ZST with
// align 8; `PhantomData` is the producer's own special lane. In every case the ZST field mints
// nothing, so it must take no position in either order — including when it is written FIRST.
// =================================================================================================

#[inline(never)]
pub fn z01_zst_array_in_order(a: u32) -> ZArr {
    ZArr { a, z: [] }
}
#[inline(never)]
pub fn z02_zst_array_out_of_order(a: u32) -> ZArr {
    ZArr { z: [], a }
}
#[inline(never)]
pub fn z03_unit_struct_in_order(a: u32) -> ZUnit {
    ZUnit { a, u: Unit1 }
}
#[inline(never)]
pub fn z04_unit_struct_out_of_order(a: u32) -> ZUnit {
    ZUnit { u: Unit1, a }
}
#[inline(never)]
pub fn z05_phantom_in_order(a: u32) -> ZPhantom {
    ZPhantom { a, p: PhantomData }
}
#[inline(never)]
pub fn z06_phantom_out_of_order(a: u32) -> ZPhantom {
    ZPhantom { p: PhantomData, a }
}
#[inline(never)]
pub fn z07_unit_first_in_order(a: u32) -> ZFirst {
    ZFirst { z: (), a }
}
#[inline(never)]
pub fn z08_unit_first_out_of_order(a: u32) -> ZFirst {
    ZFirst { a, z: () }
}

// =================================================================================================
// GROUP U — FUNCTIONAL RECORD UPDATE, INCLUDING A BASE THAT IS ITSELF A CALL. `StructTailExpr`
// is refused by name; a base that is a CALL is the shape where the base is not even a place.
// =================================================================================================

#[inline(never)]
pub fn u01_fru_base_is_call(x: u32) -> Src {
    Src { a: x, ..mk_src() }
}
#[inline(never)]
pub fn u02_fru_base_is_call_two_given(x: u32, y: u32) -> Src {
    Src { a: x, b: y, ..mk_src() }
}
#[inline(never)]
pub fn u03_fru_base_is_param(s: Src, x: u32) -> Src {
    Src { a: x, ..s }
}
#[inline(never)]
pub fn u04_fru_base_is_param_out_of_order(s: Src, x: u32) -> Src {
    Src { c: x, ..s }
}
#[inline(never)]
pub fn u05_written_out_twin_of_u03(s: Src, x: u32) -> Src {
    Src { a: x, b: s.b, c: s.c }
}
#[inline(never)]
pub fn u06_written_out_twin_out_of_order(s: Src, x: u32) -> Src {
    Src { c: x, b: s.b, a: s.a }
}
#[inline(never)]
pub fn u07_fru_base_is_call_e3(x: u32) -> E3 {
    E3 { b: x, ..mk_e3() }
}
#[inline(never)]
pub fn u08_written_out_cross_index(s: Src) -> Src {
    Src { a: s.c, b: s.b, c: s.a }
}

// =================================================================================================
// GROUP T — TUPLE aggregates, which take the same Return-arm collapse as a struct.
// =================================================================================================

#[inline(never)]
pub fn t01_tuple_places(x: u32, y: u32) -> (u32, u32) {
    (x, y)
}
#[inline(never)]
pub fn t02_tuple_swapped(x: u32, y: u32) -> (u32, u32) {
    (y, x)
}
#[inline(never)]
pub fn t03_tuple_mixed_type(x: u8, y: u64) -> (u8, u64) {
    (x, y)
}
#[inline(never)]
pub fn t04_tuple_computed_first(x: u32, y: u32) -> (u32, u32) {
    (x & y, y)
}
#[inline(never)]
pub fn t05_tuple_computed_last(x: u32, y: u32) -> (u32, u32) {
    (x, x & y)
}
#[inline(never)]
pub fn t06_tuple_const_and_place(x: u32) -> (u32, u32) {
    (1, x)
}
#[inline(never)]
pub fn t07_tuple_load_first(p: &u32, y: u32) -> (u32, u32) {
    (*p, y)
}
#[inline(never)]
pub fn t08_tuple_cast_last(x: u32, y: u16) -> (u32, u32) {
    (x, y as u32)
}
