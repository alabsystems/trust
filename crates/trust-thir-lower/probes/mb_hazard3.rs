// LANE P (adversarial review of lane K, 2026-08-13) — targeted hunt for hazard #3: a REF/PTR-TYPED value reaching
// `mf_operand`, which mints `StorageLive` + `_t = copy <ptr>` for ANY operand place.
// `ptr_cond` (a raw-pointer `ICmp`) dies earlier at "ICmp on non-scalar type", so the
// question is whether a DIFFERENT admitted arm (`Cast`, `BinOp`, `UnOp`) can route a
// pointer through it.

// (a) ptr -> usize cast in the CONDITION. The cast's operand is ptr-typed, so
//     `mf_operand` would mint a POINTER-typed marker temp.
#[inline(never)]
pub fn ptr_cast_cond(p: *const u32, x: u32, y: u32) -> u32 {
    if p as usize == 0 { x } else { y }
}

// (b) the same, one step removed: the cast is in an ARM, not the condition.
#[inline(never)]
pub fn ptr_cast_arm(p: *const u32, a: u32) -> usize {
    if a == 0 { p as usize } else { 0 }
}

// (c) a SHARED REFERENCE cast to a raw pointer then to usize.
#[inline(never)]
pub fn ref_cast_cond(r: &u32, x: u32, y: u32) -> u32 {
    if r as *const u32 as usize == 0 { x } else { y }
}

// (d) usize arithmetic on a cast pointer in the condition (a `BinOp` whose operand
//     chain starts at a pointer).
#[inline(never)]
pub fn ptr_addr_cond(p: *const u32, x: u32, y: u32) -> u32 {
    if (p as usize) & 7 == 0 { x } else { y }
}

// (e) CONTROL for the shift guard with overflow-checks OFF: a CAST-FREE shift in an
//     arm. Lane N recorded that lane L's identical guard is INERT under
//     `overflow-checks = true` (every shift carries an `Inst::Assert`) but a real
//     refusal with checks off. This is the shape that exercises the live path.
#[inline(never)]
pub fn shift_arm_castfree(a: u32, b: u32, s: u32) -> u32 {
    if a == 0 { b << s } else { b >> s }
}

// (f) a SHIFT in the CONDITION with checks off.
#[inline(never)]
pub fn shift_cond_castfree(a: u32, s: u32, x: u32, y: u32) -> u32 {
    if (a << s) == 0 { x } else { y }
}

// (g) POSITIVE CONTROL so the crate is never trivially empty.
#[inline(never)]
pub fn min_if(a: u32, b: u32) -> bool {
    if a == 0 { b == 1 } else { b == 2 }
}

// MEASURED, control (trust e4f16776fa) vs subject (lane K rebased), at
// `-Coverflow-checks=on` AND `=off`, both drivers independently sealed:
//
//   ptr_cast_cond / ptr_cast_arm / ref_cast_cond / ptr_addr_cond
//       unsupported in BOTH, and NOT at the shim — at the PRODUCER
//       ("producer: 2 unsupported THIR shape(s)"). A pointer never reaches trust-ir's
//       instruction stream at all, so it cannot reach `mf_operand`. Hazard #3 is
//       bounded two layers upstream of `plan_branch_markers`; I could not reach it.
//   shift_arm_castfree / shift_cond_castfree
//       agreed/mk=False in BOTH drivers at BOTH check settings. The shift refusal
//       costs no verdict here. Whether removing it would yield built's sequence or a
//       wrong one is UNMEASURED — the guard was not weakened to find out.
//   min_if  agreed/mk=False -> agreed/mk=TRUE, so the crate is not trivially inert.
