// LANE MF-R3 (round-3 independent review, 2026-08-13) — SIZING THE SURVIVING DEFECT CLASS.
//
// `mfr3_bind::g16_if_writes_field` survived round 2's fix as ADMITTED-AND-WRONG at both opt
// levels. Its mechanism: the FIELD-WRITE ARM (`recognize_field_write` in `to_mir.rs`) emits its
// wave-24b operand temp and marker pair UNCONDITIONALLY — it is gated by neither
// `source_form_admits` nor `plan_operand_marker_temps` nor `plan_branch_markers`. Round 2 fixed
// the arm's PREDICATE (`rhs_is_place`, built's `as_local_rvalue` category) but not its SCOPE, so
// any body that (a) contains a `Category::Place` field write and (b) makes built mint a marker
// somewhere the shim does not, emits a non-empty derived sequence that is not built's.
//
// This file exists to say how big that class is. Every body is a field write PLUS one other
// ordinary construct that mints a built marker outside the write.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr3_wclass \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr3_wclass.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::needless_late_init, clippy::let_and_return)]

#[derive(Clone, Copy)]
pub struct C3 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
}

// --- BASELINE: the write ALONE. These must be `right` (round 2's fix). -------------------------
#[inline(never)]
pub fn w00_write_alone_place(w: &mut C3, v: u32) {
    w.a = v;
}
#[inline(never)]
pub fn w01_write_alone_const(w: &mut C3) {
    w.a = 1;
}
#[inline(never)]
pub fn w02_two_writes_alone(w: &mut C3, v: u32, u: u32) {
    w.a = v;
    w.b = u;
}

// --- A BRANCH AROUND THE WRITE. Built mints the condition's operand temp in the HEAD block. ----
#[inline(never)]
pub fn w03_if_else_two_writes(c: bool, w: &mut C3, v: u32) {
    if c {
        w.a = v;
    } else {
        w.b = v;
    }
}
#[inline(never)]
pub fn w04_if_one_arm(c: bool, w: &mut C3, v: u32) {
    if c {
        w.a = v;
    }
}
#[inline(never)]
pub fn w05_if_else_write_then_const(c: bool, w: &mut C3, v: u32) {
    if c {
        w.a = v;
    } else {
        w.b = 0;
    }
}
#[inline(never)]
pub fn w06_if_cond_computed_then_write(a: u32, b: u32, w: &mut C3, v: u32) {
    if a == b {
        w.a = v;
    }
}
#[inline(never)]
pub fn w07_if_cond_andand_then_write(a: u32, b: u32, c: bool, w: &mut C3, v: u32) {
    if a == b && c {
        w.a = v;
    }
}
#[inline(never)]
pub fn w08_match_bool_two_writes(c: bool, w: &mut C3, v: u32) {
    match c {
        true => w.a = v,
        false => w.b = v,
    }
}
#[inline(never)]
pub fn w09_if_else_wide_field(c: bool, w: &mut C3, v: u64) {
    if c {
        w.c = v;
    } else {
        w.c = 0;
    }
}
#[inline(never)]
pub fn w10_if_cond_is_deref(p: &bool, w: &mut C3, v: u32) {
    if *p {
        w.a = v;
    }
}

// --- A `let` AROUND THE WRITE. The scope firewall stops the PLANS; it does not stop the arm. ---
#[inline(never)]
pub fn w11_let_then_write(w: &mut C3, v: u32) {
    let t = v;
    w.a = t;
}
#[inline(never)]
pub fn w12_write_then_let_unused(w: &mut C3, v: u32) {
    w.a = v;
    let _t = v;
}
#[inline(never)]
pub fn w13_let_computed_then_write(w: &mut C3, a: u32, b: u32) {
    let t = a & b;
    w.a = t;
}

// --- A TAIL EXPRESSION AFTER THE WRITE that mints a built temp. -------------------------------
#[inline(never)]
pub fn w14_write_then_cmp_tail(w: &mut C3, v: u32, a: u32, b: u32) -> bool {
    w.a = v;
    a == b
}
#[inline(never)]
pub fn w15_write_then_nested_tail(w: &mut C3, v: u32, a: u32, b: u32, d: u32) -> bool {
    w.a = v;
    ((a & b) | d) == 0
}
#[inline(never)]
pub fn w16_write_then_load_tail(w: &mut C3, v: u32, p: &u32) -> u32 {
    w.a = v;
    *p
}
#[inline(never)]
pub fn w17_write_then_struct_tail(w: &mut C3, v: u32, x: u32, y: u32, z: u64) -> C3 {
    w.a = v;
    C3 { a: x, b: y, c: z }
}

// --- A NON-SIMPLE PARAMETER PATTERN around the write (built mints a binding local). -----------
#[inline(never)]
pub fn w18_ref_pattern_and_place_rhs(w: &mut C3, v: u32, &g: &u32) -> u32 {
    w.a = v;
    g
}
#[inline(never)]
pub fn w19_tuple_pattern_and_write((x, y): (u32, u32), w: &mut C3) {
    w.a = x;
}
#[inline(never)]
pub fn w20_struct_pattern_and_write(C3 { a, .. }: C3, w: &mut C3) {
    w.a = a;
}

// --- THE WRITE INSIDE A CLOSURE (its own body, its own gate). ---------------------------------
#[inline(never)]
pub fn w21_closure_writes_field(w: &mut C3, v: u32) {
    (|q: &mut C3| q.a = v)(w);
}
#[inline(never)]
pub fn w22_closure_ref_pattern_writes(w: &mut C3, p: &u32) {
    (|q: &mut C3, &g: &u32| q.a = g)(w, p);
}
#[inline(never)]
pub fn w23_closure_branch_writes(c: bool, w: &mut C3, v: u32) {
    (|q: &mut C3| {
        if c {
            q.a = v;
        } else {
            q.b = v;
        }
    })(w);
}

// --- THE WRITE COMBINED WITH A SHIFT (both plans refuse a shift; the arm does not). ------------
#[inline(never)]
pub fn w24_write_then_shift_tail(w: &mut C3, v: u32, a: u32) -> u32 {
    w.a = v;
    a << 3
}
#[inline(never)]
pub fn w25_if_shift_cond_then_write(a: u32, w: &mut C3, v: u32) {
    if (a << 3) == 0 {
        w.a = v;
    }
}
