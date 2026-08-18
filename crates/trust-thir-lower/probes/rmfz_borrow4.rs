// REVIEW LANE (rmfz, 2026-08-13) — the OTHER two marker-emitting sites that are not gated by
// `mf_plan`, probed for the same defect class as the field-write arm.
//
// `to_mir.rs` pushes a bare `StatementKind::StorageLive` in exactly four places. Two are inside
// `mf_result_temp` / `mf_operand` and are gated by the plan. The other two are not:
//   * the `(*P).k = v` field-write arm (the subject's group E — 11 bodies still wrong, see the
//     review report), and
//   * the wave-29b interior-borrow REBORROW temp, which reproduces built's
//     `StorageLive(_2); _2 = &((*_1).K); _0 = &(*_2); StorageDead(_2)` shape unconditionally.
// This file exercises the second one, plus the field-write shapes the first file did not reach.

#![allow(dead_code)]

#[derive(Clone, Copy)]
pub struct Slot {
    pub f: bool,
    pub g: u8,
    pub h: u64,
}
pub struct Nest {
    pub inner: Slot,
    pub k: u64,
}

// --- interior borrow: field 0, a middle field, the last field --------------------------------
#[inline(never)]
pub fn r01_borrow_first(s: &Slot) -> &bool {
    &s.f
}
#[inline(never)]
pub fn r02_borrow_middle(s: &Slot) -> &u8 {
    &s.g
}
#[inline(never)]
pub fn r03_borrow_last(s: &Slot) -> &u64 {
    &s.h
}
#[inline(never)]
pub fn r04_borrow_nested(n: &Nest) -> &u64 {
    &n.inner.h
}
#[inline(never)]
pub fn r05_borrow_whole(n: &Nest) -> &Slot {
    &n.inner
}
#[inline(never)]
pub fn r06_borrow_mut(s: &mut Slot) -> &mut u64 {
    &mut s.h
}

// --- field writes the first file did not reach -----------------------------------------------
#[inline(never)]
pub fn r07_write_nested_const(n: &mut Nest) {
    n.inner.h = 5;
}
#[inline(never)]
pub fn r08_write_nested_cast_const(n: &mut Nest) {
    n.inner.h = 5u32 as u64;
}
#[inline(never)]
pub fn r09_write_outer_const(n: &mut Nest) {
    n.k = 5;
}
#[inline(never)]
pub fn r10_write_outer_cast(n: &mut Nest, v: u8) {
    n.k = v as u64;
}
#[inline(never)]
pub fn r11_write_from_other_field(n: &mut Nest) {
    n.k = n.inner.h;
}
#[inline(never)]
pub fn r12_write_bool_from_cmp_const(s: &mut Slot) {
    s.f = 1 == 1;
}
