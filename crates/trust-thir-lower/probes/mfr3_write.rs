// LANE MF-R3 (round-3 independent review, 2026-08-13) — THE FIELD-WRITE ARM AND THE OPERAND
// POSITIONS, PROBED FROM SCRATCH.
//
// Round 1 claimed the admitted-and-wrong marker residual was zero and died to a corpus its author
// did not write (12 survivors). Round 2 claims zero again. This corpus is written to kill round 2
// the same way: none of these shapes appears in `mf_residual.rs`, `mf_operand_temps.rs`,
// `mf_aggregate_temps.rs`, `mf_aggregate_adversarial.rs`, `mf_multiblock.rs`, `mb_*.rs`
// (round 1's eight) or `rmfz_adversarial.rs`, `rmfz_adversarial2.rs`, `rmfz_write3.rs`,
// `rmfz_borrow4.rs` (the review's four) or `mfz2_residual.rs` (round 2's own).
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr3_write \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr3_write.rs --out-dir OUT
//
// Bucket definition, re-derived from `mir_differential.rs` (compare_derived step 5 + first_diff):
//   markers_exact: true                             -> ADMITTED AND RIGHT
//   markers_exact: false, derived side EMPTY        -> REFUSED
//   markers_exact: false, derived side NON-EMPTY    -> ADMITTED AND WRONG   <- must be zero
//
// GROUP M — the field-write arm (`recognize_field_write`), one probe per `as_local_rvalue`
//   category REACHED BY A SPELLING ROUND 2 DID NOT USE: a cast of a load, a field of a field, a
//   unary, a comparison, a same-field self-write, a tuple-struct index, TWO writes in one body.
// GROUP X — casts and loads in EVERY operand position of every admitted instruction.
// GROUP R — a value used twice (the once-use rule's would-be witnesses).
// GROUP S — two locals of the SAME type appearing in swapped order.
//
// Every body is `#[inline(never)]`; every operator is bitwise / comparison / cast so no body picks
// up an overflow `Assert`.

#![allow(clippy::eq_op, clippy::identity_op, clippy::needless_bool, dead_code)]
#![allow(clippy::unnecessary_cast, clippy::double_neg, clippy::self_assignment)]

#[derive(Clone, Copy)]
pub struct W {
    pub b8: u8,
    pub b16: u16,
    pub b32: u32,
    pub b64: u64,
    pub sf: i32,
    pub fl: bool,
}
#[derive(Clone, Copy)]
pub struct Deep {
    pub k: u32,
    pub n: Nest,
}
#[derive(Clone, Copy)]
pub struct Nest {
    pub p: u32,
    pub q: u64,
}
#[derive(Clone, Copy)]
pub struct Ix(pub u64, pub u32, pub u8);

pub const CK32: u32 = 11;
pub const CK64: u64 = 12;

// =================================================================================================
// GROUP M — THE FIELD-WRITE ARM. Built's `stmt_expr`/`ExprKind::Assign` -> `as_local_rvalue(rhs)`:
//   Category::Constant -> one assign, NO temp, NO marker.
//   Category::Rvalue   -> the rvalue straight into the field place; only its own PLACE operands
//                         take temps, and they are minted at the rvalue, not at index 0.
//   Category::Place    -> `as_operand` -> `as_temp`: exactly ONE marked temp, at index 0.
// =================================================================================================

// --- Category::Place, spellings round 2 did not write --------------------------------------------
#[inline(never)]
pub fn m01_write_field_of_field(d: &mut Deep, src: Nest) {
    d.n.q = src.q;
}
#[inline(never)]
pub fn m02_write_from_nested_read(d: &mut Deep, src: &Deep) {
    d.k = src.n.p;
}
#[inline(never)]
pub fn m03_write_self_same_field(w: &mut W) {
    w.b32 = w.b32;
}
#[inline(never)]
pub fn m04_write_self_other_field(w: &mut W) {
    w.b64 = w.b64;
}
#[inline(never)]
pub fn m05_write_tuple_index0(t: &mut Ix, v: u64) {
    t.0 = v;
}
#[inline(never)]
pub fn m06_write_tuple_index2(t: &mut Ix, v: u8) {
    t.2 = v;
}
#[inline(never)]
pub fn m07_write_bool_from_param(w: &mut W, v: bool) {
    w.fl = v;
}
#[inline(never)]
pub fn m08_write_signed_from_param(w: &mut W, v: i32) {
    w.sf = v;
}

// --- Category::Constant, spellings round 2 did not write ------------------------------------------
#[inline(never)]
pub fn m09_write_neg_literal(w: &mut W) {
    w.sf = -5;
}
#[inline(never)]
pub fn m10_write_bool_literal(w: &mut W) {
    w.fl = true;
}
#[inline(never)]
pub fn m11_write_const_path_u64(w: &mut W) {
    w.b64 = CK64;
}
#[inline(never)]
pub fn m12_write_const_path_u32(w: &mut W) {
    w.b32 = CK32;
}
#[inline(never)]
pub fn m13_write_max_literal(w: &mut W) {
    w.b16 = u16::MAX;
}

// --- Category::Rvalue over CONSTANTS (built folds: zero markers on either side) --------------------
#[inline(never)]
pub fn m14_write_const_cast(w: &mut W) {
    w.b64 = 9u16 as u64;
}
#[inline(never)]
pub fn m15_write_const_and(w: &mut W) {
    w.b32 = CK32 & 3;
}
#[inline(never)]
pub fn m16_write_const_not(w: &mut W) {
    w.b8 = !0u8;
}
#[inline(never)]
pub fn m17_write_const_cmp(w: &mut W) {
    w.fl = CK32 == 11;
}
#[inline(never)]
pub fn m18_write_const_cast_of_cast(w: &mut W) {
    w.b64 = (7u8 as u16) as u64;
}

// --- Category::Rvalue over a PLACE: built mints ONE temp, at the RVALUE's own operand slot --------
#[inline(never)]
pub fn m19_write_cast_of_param(w: &mut W, v: u16) {
    w.b64 = v as u64;
}
#[inline(never)]
pub fn m20_write_cast_narrowing(w: &mut W, v: u64) {
    w.b8 = v as u8;
}
#[inline(never)]
pub fn m21_write_cast_signed(w: &mut W, v: i32) {
    w.b32 = v as u32;
}
#[inline(never)]
pub fn m22_write_not_of_param(w: &mut W, v: u8) {
    w.b8 = !v;
}
#[inline(never)]
pub fn m23_write_cmp_of_params(w: &mut W, a: u32, b: u32) {
    w.fl = a == b;
}
#[inline(never)]
pub fn m24_write_and_of_params(w: &mut W, a: u32, b: u32) {
    w.b32 = a & b;
}
#[inline(never)]
pub fn m25_write_cast_of_field(w: &mut W, n: Nest) {
    w.b64 = n.p as u64;
}
#[inline(never)]
pub fn m26_write_cmp_of_fields(w: &mut W, n: Nest) {
    w.fl = n.p == 3;
}

// --- Category::Rvalue reached through a LOAD (the shim's `Inst::Load` statement) -------------------
#[inline(never)]
pub fn m27_write_deref_u64(w: &mut W, p: &u64) {
    w.b64 = *p;
}
#[inline(never)]
pub fn m28_write_cast_of_deref(w: &mut W, p: &u16) {
    w.b64 = *p as u64;
}
#[inline(never)]
pub fn m29_write_deref_cmp(w: &mut W, p: &u32) {
    w.fl = *p == 4;
}
#[inline(never)]
pub fn m30_write_and_of_deref(w: &mut W, p: &u32, q: &u32) {
    w.b32 = *p & *q;
}
#[inline(never)]
pub fn m31_write_deref_of_deref(w: &mut W, p: &&u64) {
    w.b64 = **p;
}

// --- TWO writes in one body: the arm fires twice, and the second must not inherit the first --------
#[inline(never)]
pub fn m32_two_writes_place_then_const(w: &mut W, v: u32) {
    w.b32 = v;
    w.b64 = 3;
}
#[inline(never)]
pub fn m33_two_writes_const_then_place(w: &mut W, v: u32) {
    w.b64 = 3;
    w.b32 = v;
}
#[inline(never)]
pub fn m34_two_writes_rvalue_then_place(w: &mut W, v: u32, u: u16) {
    w.b64 = u as u64;
    w.b32 = v;
}
#[inline(never)]
pub fn m35_two_writes_place_then_rvalue(w: &mut W, v: u32, u: u16) {
    w.b32 = v;
    w.b64 = u as u64;
}
#[inline(never)]
pub fn m36_three_writes_mixed(w: &mut W, v: u32, p: &u64) {
    w.b32 = v;
    w.b64 = *p;
    w.b8 = 1;
}

// =================================================================================================
// GROUP X — CASTS AND LOADS IN EVERY OPERAND POSITION.
// A cast and a load both materialise into a shim temp, so both look like `Operand::Copy(<temp>)`
// downstream. Ordering rule (2) says a MARKED operand may not be preceded by a PLACE operand; the
// question here is whether the classification is right in each slot.
// =================================================================================================

#[inline(never)]
pub fn x01_cast_lhs_place_rhs(a: u16, b: u32) -> bool {
    (a as u32) == b
}
#[inline(never)]
pub fn x02_place_lhs_cast_rhs(a: u32, b: u16) -> bool {
    a == (b as u32)
}
#[inline(never)]
pub fn x03_cast_both(a: u16, b: u16) -> bool {
    (a as u32) == (b as u32)
}
#[inline(never)]
pub fn x04_cast_lhs_const_rhs(a: u16) -> bool {
    (a as u32) == 7
}
#[inline(never)]
pub fn x05_const_lhs_cast_rhs(a: u16) -> bool {
    7 == (a as u32)
}
#[inline(never)]
pub fn x06_load_lhs_place_rhs(p: &u32, b: u32) -> bool {
    *p == b
}
#[inline(never)]
pub fn x07_place_lhs_load_rhs(a: u32, p: &u32) -> bool {
    a == *p
}
#[inline(never)]
pub fn x08_load_both(p: &u32, q: &u32) -> bool {
    *p == *q
}
#[inline(never)]
pub fn x09_load_lhs_cast_rhs(p: &u32, b: u16) -> bool {
    *p == (b as u32)
}
#[inline(never)]
pub fn x10_cast_lhs_load_rhs(a: u16, p: &u32) -> bool {
    (a as u32) == *p
}
#[inline(never)]
pub fn x11_load_lhs_const_rhs(p: &u32) -> bool {
    *p == 5
}
#[inline(never)]
pub fn x12_const_lhs_load_rhs(p: &u32) -> bool {
    5 == *p
}
#[inline(never)]
pub fn x13_unop_of_cast(a: u16) -> u32 {
    !(a as u32)
}
#[inline(never)]
pub fn x14_unop_of_load(p: &u32) -> u32 {
    !*p
}
#[inline(never)]
pub fn x15_cast_of_cast(a: u8) -> u64 {
    (a as u16) as u64
}
#[inline(never)]
pub fn x16_cast_of_load(p: &u16) -> u64 {
    *p as u64
}
#[inline(never)]
pub fn x17_load_of_load(p: &&u32) -> u32 {
    **p
}
#[inline(never)]
pub fn x18_cast_returned(a: u16) -> u32 {
    a as u32
}
#[inline(never)]
pub fn x19_load_returned(p: &u32) -> u32 {
    *p
}
#[inline(never)]
pub fn x20_and_cast_place(a: u16, b: u32) -> u32 {
    (a as u32) & b
}
#[inline(never)]
pub fn x21_and_place_cast(a: u32, b: u16) -> u32 {
    a & (b as u32)
}
#[inline(never)]
pub fn x22_and_load_place(p: &u32, b: u32) -> u32 {
    *p & b
}
#[inline(never)]
pub fn x23_and_place_load(a: u32, p: &u32) -> u32 {
    a & *p
}
#[inline(never)]
pub fn x24_or_load_cast(p: &u32, b: u16) -> u32 {
    *p | (b as u32)
}
#[inline(never)]
pub fn x25_xor_cast_load(a: u16, p: &u32) -> u32 {
    (a as u32) ^ *p
}
#[inline(never)]
pub fn x26_cmp_of_cast_of_load(p: &u16, b: u32) -> bool {
    (*p as u32) == b
}
#[inline(never)]
pub fn x27_cmp_place_then_cast_of_load(a: u32, p: &u16) -> bool {
    a == (*p as u32)
}
#[inline(never)]
pub fn x28_field_lhs_cast_rhs(n: Nest, b: u16) -> bool {
    n.p == (b as u32)
}
#[inline(never)]
pub fn x29_cast_lhs_field_rhs(a: u16, n: Nest) -> bool {
    (a as u32) == n.p
}
#[inline(never)]
pub fn x30_field_lhs_load_rhs(n: Nest, p: &u32) -> bool {
    n.p == *p
}
#[inline(never)]
pub fn x31_load_lhs_field_rhs(p: &u32, n: Nest) -> bool {
    *p == n.p
}
#[inline(never)]
pub fn x32_bool_of_cast_pair(a: u8, b: u8) -> bool {
    (a as u32) < (b as u32)
}

// =================================================================================================
// GROUP R — A VALUE USED TWICE. The plan's "exactly-once use" rule refuses a DAG. The producer
// does not CSE, so these are the closest source spellings and they say whether the rule has any
// witness at all on real source.
// =================================================================================================

#[inline(never)]
pub fn r01_param_used_twice(a: u32) -> u32 {
    a & a
}
#[inline(never)]
pub fn r02_field_read_twice(n: Nest) -> bool {
    n.p == n.p
}
#[inline(never)]
pub fn r03_load_twice(p: &u32) -> u32 {
    *p | *p
}
#[inline(never)]
pub fn r04_cast_twice(a: u16) -> u32 {
    (a as u32) & (a as u32)
}
#[inline(never)]
pub fn r05_same_subexpr_twice(a: u32, b: u32) -> u32 {
    (a & b) | (a & b)
}
#[inline(never)]
pub fn r06_param_thrice(a: u32) -> u32 {
    (a & a) | a
}

// =================================================================================================
// GROUP S — TWO LOCALS OF THE SAME TYPE, IN SWAPPED ORDER. The marker channel alpha-renames
// locals by first appearance and carries only the TYPE, so a swap of two same-typed locals is
// exactly the case the channel is blind to — and the case a plan can therefore get wrong for free.
// =================================================================================================

#[inline(never)]
pub fn s01_swapped_same_type(x: u32, y: u32) -> bool {
    y == x
}
#[inline(never)]
pub fn s02_declared_order_same_type(x: u32, y: u32) -> bool {
    x == y
}
#[inline(never)]
pub fn s03_swapped_three(x: u32, y: u32, z: u32) -> u32 {
    (z & y) | x
}
#[inline(never)]
pub fn s04_declared_three(x: u32, y: u32, z: u32) -> u32 {
    (x & y) | z
}
#[inline(never)]
pub fn s05_swapped_mixed_width(x: u32, y: u64) -> bool {
    y == (x as u64)
}
#[inline(never)]
pub fn s06_declared_mixed_width(x: u32, y: u64) -> bool {
    (x as u64) == y
}
#[inline(never)]
pub fn s07_swapped_fields_same_type(n: Nest, m: Nest) -> bool {
    m.p == n.p
}
#[inline(never)]
pub fn s08_swapped_loads_same_type(p: &u32, q: &u32) -> bool {
    *q == *p
}
