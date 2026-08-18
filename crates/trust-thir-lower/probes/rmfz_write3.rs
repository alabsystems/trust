// REVIEW LANE (rmfz, 2026-08-13) — CHARACTERISING THE FIELD-WRITE RHS FAMILY.
//
// The subject's group-E fix is `if matches!(v_op, Operand::Constant(_)) { assign directly }`.
// Built's rule is not "a CONSTANT right-hand side takes no temp" — it is `stmt_expr`'s
// `ExprKind::Assign` calling `as_local_rvalue(rhs)`, which writes ANY `Category::Rvalue` or
// `Category::Constant` right-hand side straight into the destination place with no `as_temp` at
// all. Only a `Category::Place` RHS takes a temp (`as_operand` on a place -> `as_temp`).
//
// So every RHS whose trust-ir value is the result of an INSTRUCTION (cast / binop / icmp / unop /
// load) is a shape where built emits ZERO markers and the shim still emits a temp pair. This file
// enumerates them.

#![allow(clippy::eq_op, dead_code)]

#[derive(Clone, Copy)]
pub struct Slot {
    pub f: bool,
    pub g: u8,
    pub h: u64,
}

pub const KONST: u64 = 1234;

#[derive(Clone, Copy)]
pub enum E {
    A = 3,
    B = 9,
}

// --- Category::Constant RHS: the shapes the subject's fix covers -------------------------------
#[inline(never)]
pub fn q01_lit(s: &mut Slot) {
    s.h = 7;
}
#[inline(never)]
pub fn q02_assoc_const(s: &mut Slot) {
    s.h = u64::MAX;
}
#[inline(never)]
pub fn q03_module_const(s: &mut Slot) {
    s.h = KONST;
}
#[inline(never)]
pub fn q04_bool_lit(s: &mut Slot) {
    s.f = true;
}

// --- Category::Rvalue RHS whose operands are all constant: built folds it into the place, the
//     shim materialises a temp ------------------------------------------------------------------
#[inline(never)]
pub fn q05_cast_of_lit(s: &mut Slot) {
    s.h = 4u32 as u64;
}
#[inline(never)]
pub fn q06_cast_of_lit_narrow(s: &mut Slot) {
    s.g = 300u32 as u8;
}
#[inline(never)]
pub fn q07_cast_of_signed_lit(s: &mut Slot) {
    s.h = -1i64 as u64;
}
#[inline(never)]
pub fn q08_cast_of_char(s: &mut Slot) {
    s.g = 'x' as u8;
}
#[inline(never)]
pub fn q09_cast_of_bool(s: &mut Slot) {
    s.g = true as u8;
}
#[inline(never)]
pub fn q10_cast_of_enum(s: &mut Slot) {
    s.g = E::B as u8;
}
#[inline(never)]
pub fn q11_cast_of_assoc_const(s: &mut Slot) {
    s.h = u32::MAX as u64;
}

// --- Category::Rvalue RHS with non-constant operands -------------------------------------------
#[inline(never)]
pub fn q12_cast_of_param(s: &mut Slot, v: u8) {
    s.h = v as u64;
}
#[inline(never)]
pub fn q13_icmp(s: &mut Slot, a: u64, b: u64) {
    s.f = a == b;
}
#[inline(never)]
pub fn q14_binop(s: &mut Slot, a: u64, b: u64) {
    s.h = a & b;
}
#[inline(never)]
pub fn q15_unop(s: &mut Slot, a: u64) {
    s.h = !a;
}
#[inline(never)]
pub fn q16_load(s: &mut Slot, p: &u64) {
    s.h = *p;
}

// --- Category::Place RHS: built DOES take a temp, so the shim's temp path is right --------------
#[inline(never)]
pub fn q17_place_param(s: &mut Slot, v: u64) {
    s.h = v;
}
#[inline(never)]
pub fn q18_place_field(s: &mut Slot, t: Slot) {
    s.h = t.h;
}

// --- the same RHS families through a TUPLE STRUCT field ----------------------------------------
#[derive(Clone, Copy)]
pub struct Tup(pub u64, pub u8);

#[inline(never)]
pub fn q19_tuple_const(t: &mut Tup) {
    t.0 = 11;
}
#[inline(never)]
pub fn q20_tuple_cast_const(t: &mut Tup) {
    t.0 = 11u32 as u64;
}

// --- and as a TAIL expression rather than a statement (the source-form gate admits the tail) ----
#[inline(never)]
pub fn q21_tail_cast_const(s: &mut Slot) {
    s.h = 4u32 as u64
}
