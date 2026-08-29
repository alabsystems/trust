// REVIEW LANE (rmfz, 2026-08-13) — AN INDEPENDENT ADVERSARIAL CORPUS FOR THE MARKER PLANS.
//
// Written to REFUTE "the admitted-and-wrong residual is zero". None of these shapes appears in
// `mf_residual.rs`, `mf_operand_temps.rs`, `mf_aggregate_temps.rs`,
// `mf_aggregate_adversarial.rs`, `mf_multiblock.rs`, `mb_*.rs` — i.e. none is in the set the
// subject lane tuned against.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=rmfz \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/rmfz_adversarial.rs --out-dir OUT
//
// Classification (identical to the lane's, re-derived from `mir_differential::first_diff`):
//   markers_exact: true                             -> ADMITTED AND RIGHT
//   markers_exact: false, derived side EMPTY        -> REFUSED
//   markers_exact: false, derived side NON-EMPTY    -> ADMITTED AND WRONG   <- must be zero
//
// Every body is `#[inline(never)]`; every operator is bitwise / comparison / cast / float so no
// body picks up an overflow `Assert`.

#![allow(clippy::eq_op, clippy::identity_op, clippy::double_neg, dead_code)]

#[derive(Clone, Copy)]
pub struct T3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct Mix2 {
    pub s: u8,
    pub w: u64,
}
#[derive(Clone, Copy)]
pub struct Inr {
    pub x: u32,
    pub y: u32,
}
#[derive(Clone, Copy)]
pub struct Outr {
    pub i: Inr,
    pub k: u32,
}
#[derive(Clone, Copy)]
pub struct Zst {
    pub a: u32,
    pub z: (),
}
#[derive(Clone, Copy)]
pub struct Holder {
    pub p: *const u64,
    pub n: u64,
}
#[derive(Clone, Copy)]
pub struct Bx(pub u8);
#[derive(Clone, Copy)]
pub struct Two(pub u8, pub u8);
#[derive(Clone, Copy)]
pub struct Flags {
    pub f0: bool,
    pub f1: bool,
    pub w: u32,
}

// =================================================================================================
// GROUP N — NESTING DEPTH AND OPERAND POSITION. Rule (1) (a marked result may not take a marked
// operand) plus rule (2) (a marked operand may not be preceded by a place operand) should mean the
// only admitted trees are: an unmarked root whose operands are places / constants / DEPTH-1 marked
// sub-trees, with every marked operand preceding every place operand. These probe the boundary of
// that claim at depth 3+ and in every operand position.
// =================================================================================================

// N01 — depth-3 LEFT spine, root returned. `&` is marked (consumer `|`), `|` is marked (consumer
// `^`)... rule (1) should refuse. If it is ADMITTED the derived order is a postorder.
#[inline(never)]
pub fn n01_left_spine3(a: u16, b: u16, c: u16, d: u16) -> u16 {
    ((a & b) | c) ^ d
}

// N02 — depth-3 RIGHT spine.
#[inline(never)]
pub fn n02_right_spine3(a: u16, b: u16, c: u16, d: u16) -> u16 {
    a ^ (c | (a & b) & d)
}

// N03 — BALANCED depth-2: two marked siblings under an unmarked root, WIDER TYPE than the lane's
// u8 case so the canonical first-appearance alpha-renaming cannot hide a swap.
#[inline(never)]
pub fn n03_balanced_u16(a: u16, b: u16, c: u16, d: u16) -> bool {
    (a & b) == (c | d)
}

// N04 — balanced, but the two sub-trees have DIFFERENT shapes (BinOp vs UnOp).
#[inline(never)]
pub fn n04_binop_vs_unop(a: u16, b: u16, c: u16) -> bool {
    (a & b) == !c
}

// N05 — the mirror of N04: unop first.
#[inline(never)]
pub fn n05_unop_vs_binop(a: u16, b: u16, c: u16) -> bool {
    !c == (a & b)
}

// N06 — THREE marked siblings is impossible (arity 2); the closest is a marked operand of a marked
// operand of an unmarked root, which rule (1) must refuse.
#[inline(never)]
pub fn n06_marked_under_marked(a: u32, b: u32, c: u32) -> bool {
    ((a & b) as u64) == (c as u64)
}

// N07 — constant in operand position 0 of a MARKED node.
#[inline(never)]
pub fn n07_const_lhs_of_marked(b: u32, c: u32) -> bool {
    (0 & b) == c
}

// N08 — constant in operand position 1 of a MARKED node.
#[inline(never)]
pub fn n08_const_rhs_of_marked(b: u32, c: u32) -> bool {
    (b & 7) == c
}

// N09 — BOTH operands of the marked node constant.
#[inline(never)]
pub fn n09_const_both_of_marked(c: u32) -> bool {
    (3 & 7) == c
}

// N10 — THE CONSTANT-TOLERANCE TRAP, spelled both ways, at u32. `(b & c) == 0`.
#[inline(never)]
pub fn n10_marked_then_const(b: u32, c: u32) -> bool {
    (b & c) == 0
}

// N11 — ...and `0 == (b & c)`.
#[inline(never)]
pub fn n11_const_then_marked(b: u32, c: u32) -> bool {
    0 == (b & c)
}

// N12 — a constant in the MARKED-OPERAND position itself: does a constant where the plan expects a
// marked operand change the verdict? `(b & c) == 0` with the marked side replaced by a constant.
#[inline(never)]
pub fn n12_const_in_marked_position(c: u32) -> bool {
    5 == c
}

// N13 — place, then constant, then nothing: two place operands, no marked operand at all.
#[inline(never)]
pub fn n13_two_places(a: u32, b: u32) -> bool {
    a == b
}

// N14 — marked operand preceded by a place operand where the PLACE IS A FIELD READ and the marked
// side is a UNOP.
#[inline(never)]
pub fn n14_field_then_unop(s: T3, c: u32) -> bool {
    s.a == !c
}

// N15 — the admitted mirror of N14.
#[inline(never)]
pub fn n15_unop_then_field(s: T3, c: u32) -> bool {
    !c == s.a
}

// N16 — marked operand at position 1 preceded by a CONSTANT at position 0, in a non-comparison
// binop at u64 (constant tolerance again, different type + op).
#[inline(never)]
pub fn n16_const_then_marked_binop(b: u64, c: u64) -> u64 {
    0 ^ (b & c)
}

// N17 — an ICmp whose result is the returned value and whose operands are one marked binop and one
// marked cast: two marked operands of DIFFERENT arms.
#[inline(never)]
pub fn n17_binop_and_cast(a: u32, b: u32, c: u16) -> bool {
    (a & b) == (c as u32)
}

// N18 — the mirror: cast first, binop second.
#[inline(never)]
pub fn n18_cast_and_binop(a: u32, b: u32, c: u16) -> bool {
    (c as u32) == (a & b)
}

// =================================================================================================
// GROUP C — CASTS, including loads through casts.
// =================================================================================================

// C01 — a cast whose operand is a marked ICmp (bool -> u8). The ICmp is marked, the cast returned.
#[inline(never)]
pub fn c01_bool_to_u8(a: u32, b: u32) -> u8 {
    (a == b) as u8
}

// C02 — a DOUBLE cast: the inner cast is marked, the outer returned.
#[inline(never)]
pub fn c02_double_cast(a: i8) -> i32 {
    (a as i16) as i32
}

// C03 — a marked cast as operand 0 of a binop, place at operand 1.
#[inline(never)]
pub fn c03_cast_then_place(a: u16, b: u32) -> u32 {
    (a as u32) & b
}

// C04 — the refused mirror: place first, marked cast second.
#[inline(never)]
pub fn c04_place_then_cast(a: u16, b: u32) -> u32 {
    b & (a as u32)
}

// C05 — a LOAD THROUGH A CAST: `*p as u32`, the cast returned so only the load is marked.
#[inline(never)]
pub fn c05_load_then_cast(p: &u64) -> u32 {
    *p as u32
}

// C06 — a cast of a load compared to a constant: rule (1) territory (marked cast over marked load).
#[inline(never)]
pub fn c06_cast_of_load_eq(p: &u64) -> bool {
    (*p as u32) == 0
}

// C07 — a cast of a FIELD read (place operand, not marked).
#[inline(never)]
pub fn c07_cast_of_field(s: Mix2) -> u64 {
    s.s as u64
}

// C08 — a cast of a field read, then compared: cast marked, ICmp returned.
#[inline(never)]
pub fn c08_cast_of_field_eq(s: Mix2) -> bool {
    (s.s as u64) == s.w
}

// C09 — the mirror of C08: the place precedes the marked cast.
#[inline(never)]
pub fn c09_field_then_cast_eq(s: Mix2) -> bool {
    s.w == (s.s as u64)
}

// =================================================================================================
// GROUP L — LOADS.
// =================================================================================================

// L01 — two marked loads as the two operands of an unmarked root.
#[inline(never)]
pub fn l01_load_eq_load(p: &u64, q: &u64) -> bool {
    *p == *q
}

// L02 — two marked loads under a non-comparison binop.
#[inline(never)]
pub fn l02_load_and_load(p: &u64, q: &u64) -> u64 {
    *p & *q
}

// L03 — a marked load and a marked binop as siblings.
#[inline(never)]
pub fn l03_load_and_binop(p: &u64, b: u64, c: u64) -> bool {
    *p == (b & c)
}

// L04 — the mirror of L03.
#[inline(never)]
pub fn l04_binop_and_load(p: &u64, b: u64, c: u64) -> bool {
    (b & c) == *p
}

// L05 — a load whose value is RETURNED takes no temp (built writes `_0 = copy (*_1)`).
#[inline(never)]
pub fn l05_load_returned(p: &u64) -> u64 {
    *p
}

// L06 — a load through a FIELD-held raw pointer: `ExtractField` then `Load`.
#[inline(never)]
pub unsafe fn l06_load_of_field_ptr(h: Holder) -> u64 {
    *h.p
}

// L07 — the same, compared: the load is marked, the field read is a place operand of the load.
#[inline(never)]
pub unsafe fn l07_load_of_field_ptr_eq(h: Holder) -> bool {
    *h.p == h.n
}

// L08 — a load compared against a field of the same struct, load first.
#[inline(never)]
pub unsafe fn l08_load_then_field(h: Holder) -> bool {
    h.n == *h.p
}

// =================================================================================================
// GROUP P — PLACE OPERAND KINDS: nested field reads, ZST fields, repeated reads.
// =================================================================================================

// P01 — a NESTED field read (`ExtractField` of an `ExtractField`).
#[inline(never)]
pub fn p01_nested_field(o: Outr) -> bool {
    o.i.x == 0
}

// P02 — two nested field reads as the two operands of the root.
#[inline(never)]
pub fn p02_two_nested_fields(o: Outr) -> bool {
    o.i.x == o.i.y
}

// P03 — a nested field read as the place operand AFTER a marked operand.
#[inline(never)]
pub fn p03_marked_then_nested_field(o: Outr, b: u32, c: u32) -> bool {
    (b & c) == o.i.x
}

// P04 — the same field read TWICE (two `ExtractField` instructions, one use each).
#[inline(never)]
pub fn p04_same_field_twice(s: T3) -> bool {
    s.a == s.a
}

// P05 — a field read feeding a marked binop, then the binop feeding the root, with a second field
// read as the root's other (place) operand — the marked operand is LEFTMOST so it is admitted.
#[inline(never)]
pub fn p05_fieldand_then_field(s: T3) -> bool {
    (s.a & s.b) == s.c
}

// P06 — the mirror: the place field read precedes the marked binop.
#[inline(never)]
pub fn p06_field_then_fieldand(s: T3) -> bool {
    s.c == (s.a & s.b)
}

// =================================================================================================
// GROUP G — AGGREGATE CONSTRUCTION.
// =================================================================================================

// G01 — instruction-valued field 0, place-valued field 1, written in field order.
#[inline(never)]
pub fn g01_instr_then_place(a: u32, b: u32, c: u32) -> Inr {
    Inr { x: a & b, y: c }
}

// G02 — place-valued field 0, instruction-valued field 1.
#[inline(never)]
pub fn g02_place_then_instr(a: u32, b: u32, c: u32) -> Inr {
    Inr { x: c, y: a & b }
}

// G03 — two instruction-valued fields in field order.
#[inline(never)]
pub fn g03_two_instr(a: u32, b: u32, c: u32, d: u32) -> Inr {
    Inr { x: a & b, y: c | d }
}

// G04 — two instruction-valued fields, written out of field order.
#[inline(never)]
pub fn g04_two_instr_swapped(a: u32, b: u32, c: u32, d: u32) -> Inr {
    Inr { y: c | d, x: a & b }
}

// G05 — a constant field between two place fields, in field order.
#[inline(never)]
pub fn g05_const_middle(x: u32, z: u32) -> T3 {
    T3 { a: x, b: 7, c: z }
}

// G06 — the same three fields written OUT of order with the constant last.
#[inline(never)]
pub fn g06_const_last_written(x: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: 7 }
}

// G07 — a struct with a ZST field.
#[inline(never)]
pub fn g07_zst_field(x: u32) -> Zst {
    Zst { a: x, z: () }
}

// G08 — a NESTED aggregate field.
#[inline(never)]
pub fn g08_nested_agg(a: u32, b: u32, k: u32) -> Outr {
    Outr { i: Inr { x: a, y: b }, k }
}

// G09 — a plain TUPLE (fields cannot be reordered in the source).
#[inline(never)]
pub fn g09_tuple(a: u32, b: u32) -> (u32, u32) {
    (a, b)
}

// G10 — a tuple with an instruction in field 1 and a place in field 0.
#[inline(never)]
pub fn g10_tuple_place_then_instr(a: u32, b: u32, c: u32) -> (u32, u32) {
    (c, a & b)
}

// G11 — a TUPLE STRUCT constructor with an instruction field.
#[inline(never)]
pub fn g11_tuple_struct(a: u8, b: u8) -> Bx {
    Bx(a & b)
}

// G12 — a two-field tuple struct, place then instruction.
#[inline(never)]
pub fn g12_tuple_struct2(a: u8, b: u8, c: u8) -> Two {
    Two(c, a & b)
}

// G13 — bool fields plus a wide field, in field order.
#[inline(never)]
pub fn g13_bools_in_order(f0: bool, f1: bool, w: u32) -> Flags {
    Flags { f0, f1, w }
}

// G14 — the same three fields written in REVERSE order.
#[inline(never)]
pub fn g14_bools_reverse(f0: bool, f1: bool, w: u32) -> Flags {
    Flags { w, f1, f0 }
}

// G15 — bool fields where one is an instruction (a comparison) and written out of order.
#[inline(never)]
pub fn g15_bool_instr_out_of_order(a: u32, b: u32, w: u32) -> Flags {
    Flags { w, f0: a == b, f1: false }
}

// =================================================================================================
// GROUP F — FUNCTIONAL RECORD UPDATE, EXHAUSTIVE OVER A THREE-FIELD STRUCT.
//
// All 7 non-empty FRU spellings (which subsets of {a,b,c} are written explicitly), all 6 written
// orders of the fully-written form, and the written-out twins that carry same-index base reads.
// =================================================================================================

// --- FRU: subsets ---
#[inline(never)]
pub fn f01_fru_none(p: T3) -> T3 {
    T3 { ..p }
}
#[inline(never)]
pub fn f02_fru_a(p: T3, x: u32) -> T3 {
    T3 { a: x, ..p }
}
#[inline(never)]
pub fn f03_fru_b(p: T3, x: u32) -> T3 {
    T3 { b: x, ..p }
}
#[inline(never)]
pub fn f04_fru_c(p: T3, x: u32) -> T3 {
    T3 { c: x, ..p }
}
#[inline(never)]
pub fn f05_fru_ab(p: T3, x: u32, y: u32) -> T3 {
    T3 { a: x, b: y, ..p }
}
#[inline(never)]
pub fn f06_fru_ac(p: T3, x: u32, y: u32) -> T3 {
    T3 { a: x, c: y, ..p }
}
#[inline(never)]
pub fn f07_fru_bc(p: T3, x: u32, y: u32) -> T3 {
    T3 { b: x, c: y, ..p }
}
// FRU written OUT of declaration order (the tail is still a base).
#[inline(never)]
pub fn f08_fru_ca(p: T3, x: u32, y: u32) -> T3 {
    T3 { c: y, a: x, ..p }
}

// --- the fully-written form, all six source orders, PARAM values ---
#[inline(never)]
pub fn f09_abc(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn f10_acb(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn f11_bac(x: u32, y: u32, z: u32) -> T3 {
    T3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn f12_bca(x: u32, y: u32, z: u32) -> T3 {
    T3 { b: y, c: z, a: x }
}
#[inline(never)]
pub fn f13_cab(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z, a: x, b: y }
}
#[inline(never)]
pub fn f14_cba(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z, b: y, a: x }
}

// --- the fully-written form, all six source orders, SAME-INDEX BASE READS (the written-out twin
//     of `T3 { ..p }`) ---
#[inline(never)]
pub fn f15_reads_abc(p: T3) -> T3 {
    T3 { a: p.a, b: p.b, c: p.c }
}
#[inline(never)]
pub fn f16_reads_acb(p: T3) -> T3 {
    T3 { a: p.a, c: p.c, b: p.b }
}
#[inline(never)]
pub fn f17_reads_bac(p: T3) -> T3 {
    T3 { b: p.b, a: p.a, c: p.c }
}
#[inline(never)]
pub fn f18_reads_bca(p: T3) -> T3 {
    T3 { b: p.b, c: p.c, a: p.a }
}
#[inline(never)]
pub fn f19_reads_cab(p: T3) -> T3 {
    T3 { c: p.c, a: p.a, b: p.b }
}
#[inline(never)]
pub fn f20_reads_cba(p: T3) -> T3 {
    T3 { c: p.c, b: p.b, a: p.a }
}

// --- partial written-out twins: one explicit value, two same-index base reads, every position ---
#[inline(never)]
pub fn f21_twin_a(p: T3, x: u32) -> T3 {
    T3 { a: x, b: p.b, c: p.c }
}
#[inline(never)]
pub fn f22_twin_b(p: T3, x: u32) -> T3 {
    T3 { a: p.a, b: x, c: p.c }
}
#[inline(never)]
pub fn f23_twin_c(p: T3, x: u32) -> T3 {
    T3 { a: p.a, b: p.b, c: x }
}

// --- a rotation: no FRU spelling exists (every read is a DIFFERENT index) ---
#[inline(never)]
pub fn f24_rotate(p: T3) -> T3 {
    T3 { a: p.b, b: p.c, c: p.a }
}

// --- a rotation written out of source order ---
#[inline(never)]
pub fn f25_rotate_written_cba(p: T3) -> T3 {
    T3 { c: p.a, b: p.c, a: p.b }
}

// --- base reads from TWO different structs, same indices ---
#[inline(never)]
pub fn f26_cross_same_index(p: T3, q: T3) -> T3 {
    T3 { a: p.a, b: q.b, c: p.c }
}

// --- an instruction field plus same-index base reads ---
#[inline(never)]
pub fn f27_instr_plus_reads(p: T3, x: u32, y: u32) -> T3 {
    T3 { a: x & y, b: p.b, c: p.c }
}

// --- same, but the instruction is in the LAST field ---
#[inline(never)]
pub fn f28_reads_plus_instr(p: T3, x: u32, y: u32) -> T3 {
    T3 { a: p.a, b: p.b, c: x & y }
}

// =================================================================================================
// GROUP S — SOURCE FORM: parameter patterns, statements, blocks.
// =================================================================================================

// S01 — a TUPLE-pattern parameter.
#[inline(never)]
pub fn s01_tuple_pat((a, b): (u64, u64)) -> bool {
    a == b
}

// S02 — a REF-binding parameter.
#[inline(never)]
pub fn s02_ref_binding(ref a: u64) -> bool {
    *a == 0
}

// S03 — an `@` binding parameter (a binding WITH a subpattern).
#[inline(never)]
pub fn s03_at_binding(x @ _: u64) -> bool {
    x == 0
}

// S04 — a TUPLE-STRUCT-pattern parameter.
#[inline(never)]
pub fn s04_tuple_struct_pat(Bx(v): Bx) -> bool {
    v == 0
}

// S05 — a `mut` binding parameter with NO statement: the gate admits it and built reuses the arg
// local, so it must be exact.
#[inline(never)]
pub fn s05_mut_param_no_stmt(mut a: u64) -> bool {
    a == 0
}

// S06 — TWO wild parameters.
#[inline(never)]
pub fn s06_two_wild(_: u64, _: u64, c: u64) -> bool {
    c == 0
}

// S07 — a wild parameter FIRST and a marked sub-tree.
#[inline(never)]
pub fn s07_wild_then_marked(_: u64, b: u64, c: u64) -> bool {
    (b & c) == 0
}

// S08 — a nested BLOCK with no statements.
#[inline(never)]
pub fn s08_nested_block(a: u64, b: u64) -> bool {
    { (a & b) == 0 }
}

// S09 — a block whose only statement is an ITEM (which the gate deliberately admits).
#[inline(never)]
pub fn s09_item_stmt(a: u64, b: u64) -> bool {
    struct Unused;
    (a & b) == 0
}

// S10 — a TAIL assignment expression: `s.f = <const>` with NO semicolon, so `blk.stmts` is empty
// and the source-form gate ADMITS the body. Pairs with the lane's group E, which used `;`.
#[inline(never)]
pub fn s10_tail_assign_const(s: &mut Flags) {
    s.f0 = true
}

// S11 — the same as a STATEMENT (semicolon), which the gate refuses but the emission change still
// reaches.
#[inline(never)]
pub fn s11_stmt_assign_const(s: &mut Flags) {
    s.f0 = true;
}

// S12 — a constant write to a WIDE field.
#[inline(never)]
pub fn s12_stmt_assign_const_wide(s: &mut Flags) {
    s.w = 4242;
}

// S13 — a place-valued write (built DOES mint a temp).
#[inline(never)]
pub fn s13_stmt_assign_place(s: &mut Flags, v: u32) {
    s.w = v;
}

// S14 — an rvalue-valued write.
#[inline(never)]
pub fn s14_stmt_assign_rvalue(s: &mut Flags, v: u32, w: u32) {
    s.w = v & w;
}

// S15 — TWO constant writes in one body.
#[inline(never)]
pub fn s15_two_const_writes(s: &mut Flags) {
    s.f0 = true;
    s.f1 = false;
}

// S16 — a constant write followed by a place write.
#[inline(never)]
pub fn s16_const_then_place_write(s: &mut Flags, v: u32) {
    s.f0 = true;
    s.w = v;
}

// S17 — a closure with a DESTRUCTURING parameter, invoked immediately (its own body).
#[inline(never)]
pub fn s17_closure_destructure(xs: &[(u64, u64)]) -> bool {
    xs.iter().any(|&(a, b)| a == b)
}

// S18 — a closure with a SIMPLE parameter (its own body must stay admitted).
#[inline(never)]
pub fn s18_closure_simple(xs: &[u64]) -> bool {
    xs.iter().any(|v| *v == 0)
}

// S19 — a closure with a WILD parameter.
#[inline(never)]
pub fn s19_closure_wild(xs: &[u64]) -> bool {
    xs.iter().any(|_| true)
}

// =================================================================================================
// GROUP M — MULTI-USE vs SINGLE-USE, and float.
// =================================================================================================

// M01 — the same param used in BOTH operands of a marked node (single-use of the RESULT, but the
// operand value is used twice).
#[inline(never)]
pub fn m01_param_used_twice(a: u32, c: u32) -> bool {
    (a & a) == c
}

// M02 — the marked result feeding the root, with the same param also the root's other operand.
#[inline(never)]
pub fn m02_param_in_both_levels(a: u32, b: u32) -> bool {
    (a & b) == a
}

// M03 — the mirror of M02 (place first).
#[inline(never)]
pub fn m03_param_first_both_levels(a: u32, b: u32) -> bool {
    a == (a & b)
}

// M04 — FLOAT arithmetic (no overflow assert), marked then place.
#[inline(never)]
pub fn m04_float_marked_then_place(x: f64, y: f64, z: f64) -> bool {
    (x + y) == z
}

// M05 — float, place then marked.
#[inline(never)]
pub fn m05_float_place_then_marked(x: f64, y: f64, z: f64) -> bool {
    z == (x + y)
}

// M06 — a marked float cast.
#[inline(never)]
pub fn m06_float_cast(x: f32, y: f64) -> bool {
    (x as f64) == y
}

// =================================================================================================
// GROUP Z — degenerate controls.
// =================================================================================================

#[inline(never)]
pub fn z01_ident(a: u64) -> u64 {
    a
}
#[inline(never)]
pub fn z02_field(s: T3) -> u32 {
    s.a
}
#[inline(never)]
pub fn z03_const() -> u32 {
    9
}
#[inline(never)]
pub fn z04_unit() {}
