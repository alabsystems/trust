// LANE MF-R3 (round-3 independent review, 2026-08-13) — PARAMETER PATTERNS, CLOSURES, AND THE
// MULTI-BLOCK PLAN.
//
// The source-form gate's rule 1 admits exactly `PatKind::Wild` and a by-value `PatKind::Binding`
// with no subpattern; everything else mints a NAMED BINDING LOCAL with its own marker pair that
// the trust-ir instruction stream cannot see. This file walks every other parameter pattern the
// language has, in functions AND in closures (a closure is its own `LocalDefId`, so the gate is
// asked again about ITS parameters), and then does the same for the multi-block plan
// (`plan_branch_markers`), whose guards round 2's table did not cover at all.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr3_bind \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr3_bind.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, clippy::unnecessary_cast)]
#![allow(clippy::toplevel_ref_arg, clippy::needless_borrow, unused_variables)]

#[derive(Clone, Copy)]
pub struct B3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct BMix {
    pub s: u8,
    pub w: u64,
}

// =================================================================================================
// GROUP D — PARAMETER PATTERNS. `_` and a plain by-value binding are ADMITTED; every other form
// mints a binding local, so the derived body must carry NO marker rather than a wrong one.
// =================================================================================================

#[inline(never)]
pub fn d01_plain_binding(a: u32, b: u32) -> bool {
    a == b
}
#[inline(never)]
pub fn d02_wild_first(_: u32, b: u32) -> bool {
    b == 0
}
#[inline(never)]
pub fn d03_wild_last(a: u32, _: u32) -> bool {
    a == 0
}
#[inline(never)]
pub fn d04_all_wild(_: u32, _: u32) -> bool {
    true
}
#[inline(never)]
pub fn d05_mut_binding(mut a: u32, b: u32) -> bool {
    a == b
}
#[inline(never)]
pub fn d06_by_ref_deref_pattern(&a: &u32, b: u32) -> bool {
    a == b
}
#[inline(never)]
pub fn d07_by_ref_deref_pattern_last(a: u32, &b: &u32) -> bool {
    a == b
}
#[inline(never)]
pub fn d08_ref_binding(ref a: u32, b: u32) -> bool {
    *a == b
}
#[inline(never)]
pub fn d09_tuple_destructure(t: (u32, u32)) -> bool {
    t.0 == t.1
}
#[inline(never)]
pub fn d10_tuple_pattern_param((a, b): (u32, u32)) -> bool {
    a == b
}
#[inline(never)]
pub fn d11_struct_pattern_param(B3 { a, b, c }: B3) -> u32 {
    (a & b) | c
}
#[inline(never)]
pub fn d12_struct_pattern_partial(B3 { a, .. }: B3) -> bool {
    a == 0
}
#[inline(never)]
pub fn d13_ref_struct_pattern(&B3 { a, b, .. }: &B3) -> bool {
    a == b
}
#[inline(never)]
pub fn d14_nested_tuple_pattern(((a, b), c): ((u32, u32), u32)) -> u32 {
    (a & b) | c
}
#[inline(never)]
pub fn d15_binding_with_subpattern(t @ (_, _): (u32, u32)) -> bool {
    t.0 == t.1
}
#[inline(never)]
pub fn d16_deref_then_field(p: &B3) -> bool {
    p.a == p.b
}
#[inline(never)]
pub fn d17_mixed_wild_and_pattern(_: u32, (a, b): (u32, u32)) -> bool {
    a == b
}
#[inline(never)]
pub fn d18_pattern_builds_struct((x, y): (u32, u32), z: u32) -> B3 {
    B3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn d19_ref_pattern_builds_struct(&x: &u32, y: u32, z: u32) -> B3 {
    B3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn d20_ref_pattern_writes_field(w: &mut B3, &v: &u32) {
    w.a = v;
}

// =================================================================================================
// GROUP L — CLOSURES. Each closure is its own body and its own `LocalDefId`, so the gate is asked
// again about ITS parameter patterns, not the enclosing function's.
// =================================================================================================

#[inline(never)]
pub fn l01_closure_plain(a: u32, b: u32) -> bool {
    (|x: u32| x == b)(a)
}
#[inline(never)]
pub fn l02_closure_by_ref_pattern(a: &u32, b: u32) -> bool {
    (|&x: &u32| x == b)(a)
}
#[inline(never)]
pub fn l03_closure_tuple_pattern(a: u32, b: u32) -> bool {
    (|(x, y): (u32, u32)| x == y)((a, b))
}
#[inline(never)]
pub fn l04_closure_wild(a: u32) -> bool {
    (|_: u32| true)(a)
}
#[inline(never)]
pub fn l05_closure_struct_pattern(s: B3) -> u32 {
    (|B3 { a, b, c }: B3| (a & b) | c)(s)
}
#[inline(never)]
pub fn l06_closure_builds_struct(x: u32, y: u32, z: u32) -> B3 {
    (|p: u32| B3 { c: z, b: y, a: p })(x)
}
#[inline(never)]
pub fn l07_closure_mixed_struct(x: u8, y: u64) -> BMix {
    (|p: u8| BMix { w: y, s: p })(x)
}
#[inline(never)]
pub fn l08_closure_deref_operand(p: &u32, b: u32) -> bool {
    (|q: &u32| *q == b)(p)
}
#[inline(never)]
pub fn l09_closure_cast_operand(a: u16, b: u32) -> bool {
    (|x: u16| (x as u32) == b)(a)
}
#[inline(never)]
pub fn l10_closure_nested(a: u32, b: u32, c: u32) -> bool {
    (|x: u32| ((x & b) | c) == 0)(a)
}

// =================================================================================================
// GROUP G — THE MULTI-BLOCK PLAN (`plan_branch_markers`). Round 2's guard-removal table has no
// row for any of these; this group exists to give them witnesses.
// =================================================================================================

#[inline(never)]
pub fn g01_if_else_places(c: bool, a: u32, b: u32) -> u32 {
    if c { a } else { b }
}
#[inline(never)]
pub fn g02_if_else_consts(c: bool) -> u32 {
    if c { 1 } else { 2 }
}
#[inline(never)]
pub fn g03_if_else_computed(c: bool, a: u32, b: u32) -> u32 {
    if c { a & b } else { a | b }
}
#[inline(never)]
pub fn g04_if_else_cast_arms(c: bool, a: u16, b: u16) -> u32 {
    if c { a as u32 } else { b as u32 }
}
#[inline(never)]
pub fn g05_if_else_load_arms(c: bool, p: &u32, q: &u32) -> u32 {
    if c { *p } else { *q }
}
#[inline(never)]
pub fn g06_andand(a: u32, b: u32, d: u32) -> bool {
    a == b && b == d
}
#[inline(never)]
pub fn g07_oror(a: u32, b: u32, d: u32) -> bool {
    a == b || b == d
}
#[inline(never)]
pub fn g08_and_or_mixed(a: u32, b: u32, d: u32) -> bool {
    (a == b && b == d) || a == d
}
#[inline(never)]
pub fn g09_nested_if(c: bool, e: bool, a: u32, b: u32) -> u32 {
    if c {
        if e { a } else { b }
    } else {
        a & b
    }
}
#[inline(never)]
pub fn g10_if_cond_is_computed(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if (a & b) == 0 { x } else { y }
}
#[inline(never)]
pub fn g11_if_cond_is_load(p: &bool, x: u32, y: u32) -> u32 {
    if *p { x } else { y }
}
#[inline(never)]
pub fn g12_if_builds_struct(c: bool, x: u32, y: u32, z: u32) -> B3 {
    if c {
        B3 { a: x, b: y, c: z }
    } else {
        B3 { c: z, b: y, a: x }
    }
}
#[inline(never)]
pub fn g13_if_arms_swapped_same_type(c: bool, x: u32, y: u32) -> bool {
    if c { y == x } else { x == y }
}
#[inline(never)]
pub fn g14_if_mixed_const_place(c: bool, a: u32) -> u32 {
    if c { a } else { 0 }
}
#[inline(never)]
pub fn g15_triple_chain(a: u32, b: u32, d: u32, e: u32) -> bool {
    a == b && b == d && d == e
}
#[inline(never)]
pub fn g16_if_writes_field(c: bool, w: &mut B3, v: u32) {
    if c {
        w.a = v;
    } else {
        w.b = v;
    }
}

// =================================================================================================
// GROUP K — SHIFTS. Both plans refuse a shift outright. With `-Coverflow-checks=on` the idiom
// carries an `Inst::Assert`; these bodies say whether the shift guard has any witness of its own.
// =================================================================================================

#[inline(never)]
pub fn k01_shl_places(a: u32, b: u32) -> u32 {
    a << (b & 31)
}
#[inline(never)]
pub fn k02_shr_places(a: u32, b: u32) -> u32 {
    a >> (b & 31)
}
#[inline(never)]
pub fn k03_shl_const(a: u32) -> u32 {
    a << 3
}
#[inline(never)]
pub fn k04_shl_then_and(a: u32, b: u32) -> u32 {
    (a << 3) & b
}
#[inline(never)]
pub fn k05_shift_in_struct(a: u32, y: u32, z: u32) -> B3 {
    B3 { a: a << 3, b: y, c: z }
}
#[inline(never)]
pub fn k06_shift_in_write(w: &mut B3, a: u32) {
    w.a = a << 3;
}
