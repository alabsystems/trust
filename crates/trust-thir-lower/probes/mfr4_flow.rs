// LANE MF-R4 (round-3 REVIEW, 2026-08-13) — UNUSUAL CONTROL FLOW INTO A MARKER SITE.
//
// Round 3 replaced round 2's predicate with a GRAMMAR plus a chokepoint. A grammar is refuted by
// a sentence it accepts and should not, so this file walks the control-flow forms the previous
// three corpora never wrote: loops as expressions, `break` with a value, labelled blocks, early
// `return`, `?`, match guards, `if let`, nested closures, and the same forms wrapped around a
// field write.
//
// Written WITHOUT reading round 1's, round 2's, or the round-2 review's probe files beyond the
// one style sample needed to match the harness contract (`#[inline(never)]`, `pub`, one shape
// per body). No body name here appears in any of the 18 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr4_flow \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr4_flow.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::needless_late_init, clippy::let_and_return, clippy::never_loop)]
#![allow(clippy::needless_return, clippy::comparison_chain, clippy::manual_range_contains)]

#[derive(Clone, Copy)]
pub struct F4 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
    pub d: bool,
}

#[derive(Clone, Copy)]
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

// --- A: loops as EXPRESSIONS. `loop { break v }` is statement-free at HIR, so `source_form_admits`
//        can still say yes; the trust-ir side is a back-edge-free multi-block body. -------------

#[inline(never)]
pub fn f01_loop_break_param(a: u32) -> u32 {
    loop {
        break a;
    }
}

#[inline(never)]
pub fn f02_loop_break_eq(a: u32, b: u32) -> bool {
    loop {
        break a == b;
    }
}

#[inline(never)]
pub fn f03_loop_break_if(a: u32, b: u32) -> u32 {
    loop {
        break if a == b { a } else { b };
    }
}

#[inline(never)]
pub fn f04_labelled_block_break(a: u32, b: u32) -> u32 {
    'blk: {
        if a == b {
            break 'blk a;
        }
        b
    }
}

#[inline(never)]
pub fn f05_labelled_loop_break_value(a: u32) -> u32 {
    'outer: loop {
        loop {
            break 'outer a;
        }
    }
}

#[inline(never)]
pub fn f06_while_cond_false_tail(a: u32, b: u32) -> u32 {
    while a > b {
        break;
    }
    a
}

#[inline(never)]
pub fn f07_loop_with_counter_write(w: &mut F4, v: u32) {
    loop {
        w.a = v;
        break;
    }
}

#[inline(never)]
pub fn f08_while_writes_field(c: bool, w: &mut F4, v: u32) {
    while c {
        w.a = v;
        break;
    }
}

// --- B: EARLY RETURN. `return` is a diverging expression in the middle of a body; built retires
//        live temps on the return edge and the shim must agree or refuse. --------------------

#[inline(never)]
pub fn f09_early_return_const(a: u32) -> u32 {
    if a == 0 {
        return 7;
    }
    a
}

#[inline(never)]
pub fn f10_early_return_place(a: u32, b: u32) -> u32 {
    if a == b {
        return b;
    }
    a
}

#[inline(never)]
pub fn f11_early_return_after_write(w: &mut F4, v: u32, c: bool) {
    w.a = v;
    if c {
        return;
    }
    w.b = v;
}

#[inline(never)]
pub fn f12_return_in_both_arms(a: u32, b: u32) -> u32 {
    if a == b {
        return a;
    } else {
        return b;
    }
}

#[inline(never)]
pub fn f13_early_return_expr_body(a: u32, b: u32) -> u32 {
    if a > b { return a } else { b }
}

#[inline(never)]
pub fn f14_write_then_return_place(w: &mut F4, v: u32) -> u32 {
    w.a = v;
    return v;
}

// --- C: the `?` operator. Its desugaring mints a match, a binding local and a `Try` call; this
//        is the fail-closed direction and the point is that NOTHING is admitted here. ---------

#[inline(never)]
pub fn f15_question_option(o: Option<u32>) -> Option<u32> {
    let v = o?;
    Some(v)
}

#[inline(never)]
pub fn f16_question_then_write(o: Option<u32>, w: &mut F4) -> Option<u32> {
    let v = o?;
    w.a = v;
    Some(v)
}

#[inline(never)]
pub fn f17_question_result(r: Result<u32, u32>) -> Result<u32, u32> {
    let v = r?;
    Ok(v)
}

// --- D: MATCH GUARDS. A guard is an extra condition block between the test and the arm; built
//        materialises its operand temps in a block the shim's branch plan has not modelled. ---

#[inline(never)]
pub fn f18_match_guard_scalar(a: u32, b: u32) -> u32 {
    match a {
        x if x == b => x,
        _ => b,
    }
}

#[inline(never)]
pub fn f19_match_guard_two_arms(a: u32, b: u32, c: u32) -> u32 {
    match a {
        x if x == b => b,
        x if x == c => c,
        _ => a,
    }
}

#[inline(never)]
pub fn f20_match_guard_writes_field(a: u32, b: u32, w: &mut F4, v: u32) {
    match a {
        x if x == b => w.a = v,
        _ => w.b = v,
    }
}

#[inline(never)]
pub fn f21_match_binding_arm(a: u32) -> u32 {
    match a {
        0 => 0,
        n => n,
    }
}

#[inline(never)]
pub fn f22_match_range_arm(a: u32) -> u32 {
    match a {
        0..=9 => 1,
        _ => 2,
    }
}

#[inline(never)]
pub fn f23_match_or_pattern(a: u32) -> u32 {
    match a {
        0 | 1 | 2 => 1,
        _ => 0,
    }
}

// --- E: `if let` / `let else`. Both mint binding locals with their own pairs. ------------------

#[inline(never)]
pub fn f24_if_let_some(o: Option<u32>, d: u32) -> u32 {
    if let Some(v) = o { v } else { d }
}

#[inline(never)]
pub fn f25_if_let_then_write(o: Option<u32>, w: &mut F4) {
    if let Some(v) = o {
        w.a = v;
    }
}

#[inline(never)]
pub fn f26_let_else_write(o: Option<u32>, w: &mut F4, d: u32) {
    let Some(v) = o else {
        w.a = d;
        return;
    };
    w.a = v;
}

// --- F: NESTED CLOSURES. The closure is its own `LocalDefId`; the plans are asked again on IT,
//        and the enclosing body must not inherit the answer. ---------------------------------

#[inline(never)]
pub fn f27_closure_call_immediate(a: u32) -> u32 {
    (|x: u32| x)(a)
}

#[inline(never)]
pub fn f28_closure_eq_immediate(a: u32, b: u32) -> bool {
    (|x: u32, y: u32| x == y)(a, b)
}

#[inline(never)]
pub fn f29_closure_writes_field(w: &mut F4, v: u32) {
    (|s: &mut F4, u: u32| s.a = u)(w, v);
}

#[inline(never)]
pub fn f30_closure_destructuring_param(p: Pair) -> u32 {
    (|Pair { x, y }: Pair| x + y)(p)
}

#[inline(never)]
pub fn f31_nested_closure_two_deep(a: u32) -> u32 {
    (|x: u32| (|y: u32| y)(x))(a)
}

// --- G: SHORT-CIRCUIT operators, which are branches with no `if` in sight. --------------------

#[inline(never)]
pub fn f32_andand_tail(a: u32, b: u32, c: bool) -> bool {
    a == b && c
}

#[inline(never)]
pub fn f33_oror_tail(a: u32, b: u32, c: bool) -> bool {
    a == b || c
}

#[inline(never)]
pub fn f34_andand_write(a: u32, b: u32, w: &mut F4) {
    w.d = a == b && a > 0;
}

#[inline(never)]
pub fn f35_oror_of_two_cmps(a: u32, b: u32, c: u32) -> bool {
    a == b || b == c
}

#[inline(never)]
pub fn f36_andand_chain_three(a: u32, b: u32, c: bool, d: bool) -> bool {
    a == b && c && d
}

// --- H: a WRITE reached through each control-flow form above, so the field-write grammar is
//        asked the same question from every direction. ---------------------------------------

#[inline(never)]
pub fn f37_write_in_match_arm_block(a: u32, w: &mut F4, v: u32) {
    match a {
        0 => {
            w.a = v;
        }
        _ => {
            w.b = v;
        }
    }
}

#[inline(never)]
pub fn f38_write_in_labelled_block(a: u32, b: u32, w: &mut F4, v: u32) {
    'blk: {
        if a == b {
            break 'blk;
        }
        w.a = v;
    }
}

#[inline(never)]
pub fn f39_write_after_loop(w: &mut F4, v: u32) {
    loop {
        break;
    }
    w.a = v;
}

#[inline(never)]
pub fn f40_write_before_loop(w: &mut F4, v: u32) {
    w.a = v;
    loop {
        break;
    }
}

#[inline(never)]
pub fn f41_write_in_nested_if(a: u32, b: u32, c: bool, w: &mut F4, v: u32) {
    if a == b {
        if c {
            w.a = v;
        }
    }
}

#[inline(never)]
pub fn f42_two_writes_around_branch(c: bool, w: &mut F4, v: u32) {
    w.a = v;
    if c {
        w.b = v;
    }
    w.c = 0;
}
