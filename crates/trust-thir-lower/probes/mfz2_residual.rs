// LANE MF-ZERO-2 (2026-08-13) — THE PROBES THE ROUND-1 SWEEP DID NOT HAVE.
//
// Round 1 claimed `RESIDUAL ADMITTED-AND-WRONG = 0`; an independent review measured TWELVE
// survivors and SEVEN lost flips (reports/mf-residual-review-2026-08-13.md). This file pins the
// two defects that produced them, one probe per DISTINCT reason, so neither can come back
// unmeasured. It is deliberately additive to `probes/rmfz_*.rs` — that corpus stays the
// independent one and is not edited here.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfz2_residual \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfz2_residual.rs --out-dir OUT
//
// Classification (`mir_differential::first_diff`, re-derived):
//   markers_exact: true                             -> ADMITTED AND RIGHT
//   markers_exact: false, derived side EMPTY        -> REFUSED         (fallback to built MIR)
//   markers_exact: false, derived side NON-EMPTY    -> ADMITTED AND WRONG   <- must be zero
//
// GROUP Q is the field-write arm, one probe per `as_local_rvalue` CATEGORY — the split round 1
// keyed wrongly. GROUP P is the struct-literal written field order, one probe per reason a
// permutation is or is not OBSERVABLE in the marker channel. GROUP A is what is left of the
// aggregate ordering rules after the field-position proxy was retired.
//
// Every body is `#[inline(never)]`; every operator is bitwise / comparison / cast so no body
// picks up an overflow `Assert`.

#![allow(clippy::eq_op, clippy::identity_op, clippy::needless_bool, dead_code)]

#[derive(Clone, Copy)]
pub struct S1 {
    pub g: u8,
    pub h: u64,
}
#[derive(Clone, Copy)]
pub struct Tup(pub u64, pub u8);
#[derive(Clone, Copy)]
pub struct T3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct W3 {
    pub a: u8,
    pub b: u32,
    pub c: u64,
}
#[derive(Clone, Copy)]
pub struct P2 {
    pub l: u32,
    pub r: u32,
}
#[derive(Clone, Copy)]
pub struct Flag2 {
    pub f: bool,
    pub w: u32,
}

pub const K32: u32 = 9;
pub const K8: u8 = 3;

// =================================================================================================
// GROUP Q — THE FIELD-WRITE ARM, ONE PROBE PER `as_local_rvalue` CATEGORY.
//
// `stmt_expr`'s `ExprKind::Assign` calls `as_local_rvalue(rhs)`:
//   Category::Constant -> `Rvalue::Use(Operand::Constant)`, NO temp, NO markers.
//   Category::Rvalue   -> the rvalue straight into the field place, NO temp for the RESULT; only
//                         the rvalue's own place operands take temps.
//   Category::Place    -> `as_operand`->`as_temp`: ONE marked temp, at index 0.
// Round 1 keyed on `matches!(v_op, Operand::Constant(_))`, which is Category::Constant ONLY, and
// left every Category::Rvalue shape emitting a second, wrongly-typed, wrongly-placed marker.
// =================================================================================================

// --- Category::Constant: built emits `((*_1).k) = const c` and nothing else -------------------
#[inline(never)]
pub fn q01_write_int_const(s: &mut S1) {
    s.h = 7;
}
#[inline(never)]
pub fn q02_write_narrow_const(s: &mut S1) {
    s.g = 200;
}
#[inline(never)]
pub fn q03_write_const_path(s: &mut S1) {
    s.g = K8;
}

// --- Category::Rvalue over CONSTANTS ONLY: built folds the operands, so ZERO markers. These are
//     the nine bodies the review found ADMITTED-AND-WRONG; they must become `right`, not merely
//     stop being wrong. -------------------------------------------------------------------------
#[inline(never)]
pub fn q10_write_cast_of_lit(s: &mut S1) {
    s.h = 4u32 as u64;
}
#[inline(never)]
pub fn q11_write_cast_narrowing(s: &mut S1) {
    s.g = 300u32 as u8;
}
#[inline(never)]
pub fn q12_write_cast_of_signed_lit(s: &mut S1) {
    s.h = -1i64 as u64;
}
#[inline(never)]
pub fn q13_write_cast_of_char(s: &mut S1) {
    s.g = 'x' as u8;
}
#[inline(never)]
pub fn q14_write_cast_of_bool(s: &mut S1) {
    s.g = true as u8;
}
#[inline(never)]
pub fn q15_write_cast_of_assoc_const(s: &mut S1) {
    s.h = u32::MAX as u64;
}
#[inline(never)]
pub fn q16_write_cast_of_const_path(s: &mut S1) {
    s.h = K32 as u64;
}
#[inline(never)]
pub fn q17_write_tuple_cast_const(t: &mut Tup) {
    t.0 = 11u32 as u64;
}
#[inline(never)]
pub fn q18_write_cast_const_tail(s: &mut S1) {
    s.h = 4u32 as u64
}

// --- Category::Rvalue over a PLACE: built mints ONE temp, of the SOURCE type, at index 0. This
//     shim has already spent index 0 materialising the instruction, so the honest answer is an
//     EMPTY marker sequence -> `refused`. Never a wrong marker. ---------------------------------
#[inline(never)]
pub fn q20_write_cast_of_param(s: &mut S1, v: u8) {
    s.h = v as u64;
}
#[inline(never)]
pub fn q21_write_cast_of_param_narrowing(s: &mut S1, v: u64) {
    s.g = v as u8;
}
#[inline(never)]
pub fn q22_write_cast_of_field_read(s: &mut S1, t: S1) {
    s.h = t.g as u64;
}
#[inline(never)]
pub fn q23_write_tuple_cast_of_param(t: &mut Tup, v: u8) {
    t.0 = v as u64;
}

// --- Category::Rvalue reached through `Inst::Load` (a deref RHS) ------------------------------
#[inline(never)]
pub fn q30_write_load(s: &mut S1, p: &u64) {
    s.h = *p;
}
#[inline(never)]
pub fn q31_write_cast_of_load(s: &mut S1, p: &u8) {
    s.h = *p as u64;
}
#[inline(never)]
pub fn q32_write_load_narrow(s: &mut S1, p: &u8) {
    s.g = *p;
}

// --- Category::Rvalue, other operator shapes. Some of these are `unsupported` for reasons that
//     have nothing to do with markers (the comparator's fragment gate declines a `&mut Adt` in
//     certain bodies); they are here so that is a MEASURED fact per shape rather than an
//     assumption transferred from one BinOp probe to a whole category. ------------------------
#[inline(never)]
pub fn q40_write_binop_params(s: &mut S1, v: u64, w: u64) {
    s.h = v & w;
}
#[inline(never)]
pub fn q41_write_binop_const(s: &mut S1, v: u64) {
    s.h = v | 1;
}
#[inline(never)]
pub fn q42_write_unop(s: &mut S1, v: u64) {
    s.h = !v;
}
#[inline(never)]
pub fn q43_write_cmp(s: &mut Flag2, v: u32, w: u32) {
    s.f = v == w;
}
#[inline(never)]
pub fn q44_write_binop_of_consts(s: &mut S1) {
    s.h = 6u64 & 3u64;
}

// --- Category::Place: the shim was RIGHT here before this lane and must stay right ------------
#[inline(never)]
pub fn q50_write_param(s: &mut S1, v: u64) {
    s.h = v;
}
#[inline(never)]
pub fn q51_write_narrow_param(s: &mut S1, v: u8) {
    s.g = v;
}
#[inline(never)]
pub fn q52_write_field_read(s: &mut S1, t: S1) {
    s.h = t.h;
}
#[inline(never)]
pub fn q53_write_field_read_cross_width(s: &mut S1, t: S1) {
    s.g = t.g;
}
#[inline(never)]
pub fn q54_write_tuple_param(t: &mut Tup, v: u64) {
    t.0 = v;
}
#[inline(never)]
pub fn q55_write_bool_param(s: &mut Flag2, v: bool) {
    s.f = v;
}

// =================================================================================================
// GROUP P — THE WRITTEN FIELD ORDER, SPLIT BY OBSERVABILITY.
//
// `canon_markers` renames locals BY FIRST APPEARANCE and carries only the TYPE. Built mints one
// `as_operand` temp per non-constant written field, in SOURCE order; the shim mints the same
// temps at the aggregate site in FIELD order. So a permutation is observable only through the
// sequence of temp TYPES and statement INDICES.
// =================================================================================================

// --- SAME-TYPED PARAM fields: every permutation is invisible. All six must be `right`. Round 1
//     refused five of these six and that cost five flips. ---------------------------------------
#[inline(never)]
pub fn p01_abc(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn p02_acb(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn p03_bac(x: u32, y: u32, z: u32) -> T3 {
    T3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn p04_bca(x: u32, y: u32, z: u32) -> T3 {
    T3 { b: y, c: z, a: x }
}
#[inline(never)]
pub fn p05_cab(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z, a: x, b: y }
}
#[inline(never)]
pub fn p06_cba(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z, b: y, a: x }
}

// --- SAME-TYPED, with a CONSTANT in each position in turn. A constant field mints nothing on
//     either side, so it neither takes a position nor shifts anyone else's. --------------------
#[inline(never)]
pub fn p10_const_last_written(x: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: 7 }
}
#[inline(never)]
pub fn p11_const_first_written(y: u32, z: u32) -> T3 {
    T3 { c: z, b: y, a: 7 }
}
#[inline(never)]
pub fn p12_const_middle_written(x: u32, y: u32) -> T3 {
    T3 { b: y, c: 7, a: x }
}
#[inline(never)]
pub fn p13_two_consts(x: u32) -> T3 {
    T3 { c: 5, a: x, b: 7 }
}
#[inline(never)]
pub fn p14_const_path_field(x: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: K32 }
}

// --- SAME-TYPED FIELD READS, written out of order — the `f25` shape, whose refusal needed BOTH
//     the source-form clause and the (now retired) field-position proxy. -----------------------
#[inline(never)]
pub fn p20_rotate_written_cba(p: T3) -> T3 {
    T3 { c: p.a, b: p.c, a: p.b }
}
#[inline(never)]
pub fn p21_reads_cba(p: T3) -> T3 {
    T3 { c: p.c, b: p.b, a: p.a }
}
#[inline(never)]
pub fn p22_reads_mixed_sources(p: T3, q: T3) -> T3 {
    T3 { c: q.c, a: p.a, b: q.b }
}
#[inline(never)]
pub fn p23_read_and_param(p: T3, x: u32) -> T3 {
    T3 { b: p.b, a: x, c: p.c }
}
#[inline(never)]
pub fn p24_two_field_swap(p: P2) -> P2 {
    P2 { r: p.l, l: p.r }
}

// --- MIXED WIDTHS: the type sequence itself permutes, so every one of these IS observable and
//     must be REFUSED. This is the family the source-form clause exists for; `p30`..`p34` are
//     ADMITTED-AND-WRONG without it. ------------------------------------------------------------
#[inline(never)]
pub fn p30_mixed_acb(x: u8, y: u32, z: u64) -> W3 {
    W3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn p31_mixed_bac(x: u8, y: u32, z: u64) -> W3 {
    W3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn p32_mixed_cba(x: u8, y: u32, z: u64) -> W3 {
    W3 { c: z, b: y, a: x }
}
#[inline(never)]
pub fn p33_mixed_reads_cba(p: W3) -> W3 {
    W3 { c: p.c, b: p.b, a: p.a }
}
#[inline(never)]
pub fn p34_mixed_two_of_three(x: u8, y: u32, z: u64) -> W3 {
    W3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn p35_bool_and_word_reverse(f: bool, w: u32) -> Flag2 {
    Flag2 { w, f }
}
// ...and the SAME two fields in declaration order, which must stay `right`. The pair is what
// makes the refusal above attributable to the ORDER and not to the type mix.
#[inline(never)]
pub fn p36_bool_and_word_in_order(f: bool, w: u32) -> Flag2 {
    Flag2 { f, w }
}
#[inline(never)]
pub fn p37_mixed_in_order(x: u8, y: u32, z: u64) -> W3 {
    W3 { a: x, b: y, c: z }
}

// --- A COMPUTED field in a permuted literal: built builds it into its own temp at its SOURCE
//     position while the shim mints it at its instruction, so the INDICES move and not only the
//     types. Refused even when every field is same-typed. --------------------------------------
#[inline(never)]
pub fn p40_instr_written_last(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: y & 1 }
}
#[inline(never)]
pub fn p41_instr_written_first(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z & 1, a: x, b: y }
}
#[inline(never)]
pub fn p42_two_instr_swapped(a: u32, b: u32, c: u32, d: u32) -> P2 {
    P2 { r: c | d, l: a & b }
}
// ...and their declaration-order twins.
#[inline(never)]
pub fn p43_instr_in_order(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, b: y & 1, c: z }
}
#[inline(never)]
pub fn p44_two_instr_in_order(a: u32, b: u32, c: u32, d: u32) -> P2 {
    P2 { l: a & b, r: c | d }
}

// --- A DEREF field in a permuted literal: `Category::Place` for built (one temp, at the
//     aggregate) but an `Inst::Load` for the shim (a statement of its own, BEFORE it). Refused,
//     and its declaration-order twin is the sibling. -------------------------------------------
#[inline(never)]
pub fn p50_deref_field_permuted(p: &u32, q: &u32) -> P2 {
    P2 { r: *q, l: *p }
}
#[inline(never)]
pub fn p51_deref_field_in_order(p: &u32, q: &u32) -> P2 {
    P2 { l: *p, r: *q }
}

// =================================================================================================
// GROUP A — WHAT IS LEFT OF THE AGGREGATE ORDERING RULES.
//
// The field-POSITION proxy is retired: the producer lowers field values in source order, does not
// CSE, and gives a bare block param no position at all, so the positions only ever traced the
// SOURCE order — which `source_form_admits` now reads directly and can ask about observability.
// `seen_place` is NOT a proxy and stays; these are its witnesses, in DECLARATION order, where no
// source-form question arises at all.
// =================================================================================================

#[inline(never)]
pub fn a01_place_then_instr(a: u32, b: u32, c: u32) -> P2 {
    P2 { l: c, r: a & b }
}
#[inline(never)]
pub fn a02_instr_then_place(a: u32, b: u32, c: u32) -> P2 {
    P2 { l: a & b, r: c }
}
#[inline(never)]
pub fn a03_read_then_instr(p: P2, a: u32, b: u32) -> P2 {
    P2 { l: p.l, r: a & b }
}
#[inline(never)]
pub fn a04_instr_then_read(p: P2, a: u32, b: u32) -> P2 {
    P2 { l: a & b, r: p.r }
}
// The producer does not CSE: two identical field expressions get two positions, not one. In
// declaration order the positions therefore always rise, which is why the retired proxy could
// never fire on a body like these.
#[inline(never)]
pub fn a10_duplicate_read(p: T3) -> T3 {
    T3 { a: p.c, b: p.c, c: p.a }
}
#[inline(never)]
pub fn a11_duplicate_instr(a: u32, b: u32) -> P2 {
    P2 { l: a & b, r: a & b }
}
#[inline(never)]
pub fn a12_duplicate_param(x: u32) -> P2 {
    P2 { l: x, r: x }
}
