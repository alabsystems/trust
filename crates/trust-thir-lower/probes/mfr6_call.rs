// LANE MF-R6 (sixth review) — CALLS: IN A SCRUTINEE, IN AN OPERAND POSITION, AND AS A TAIL.
//
// A call is the one instruction whose result the shim does not mint through `mf_result_temp`, and
// `routed_operands` has no `Inst::Call` arm — so `predict` counts ZERO markers for every operand of
// every call. Built does not: `as_operand` on a call argument mints a temp exactly as it does for a
// binary operator's operand, and a call in a MATCH SCRUTINEE is a temp whose scope ends at the
// scrutinee. If any call-carrying body reaches the operand-temp class, `predict` under-counts and
// the body fails closed (safe) — unless the emitter under-emits by the same amount, in which case
// the counts agree and the sequence does not. That is the shape this file exists to find.
//
// Every callee here is `#[inline(never)]` so the call survives to MIR.
//
// No body name in this file appears in any of the 27 probe files rounds 1-5 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::match_like_matches_macro, clippy::needless_match)]

#[inline(never)]
pub fn c_id(x: u32) -> u32 {
    x
}

#[inline(never)]
pub fn c_eq(x: u32, y: u32) -> bool {
    x == y
}

#[inline(never)]
pub fn c_flag() -> bool {
    true
}

// --- A: a call in a MATCH SCRUTINEE — k18's family with a call instead of a comparison. --------

#[inline(never)]
pub fn m01_match_call_bool(a: u32, b: u32, x: u32, y: u32) -> u32 {
    match c_eq(a, b) {
        true => x,
        false => y,
    }
}

#[inline(never)]
pub fn m02_match_nullary_call(x: u32, y: u32) -> u32 {
    match c_flag() {
        true => x,
        false => y,
    }
}

#[inline(never)]
pub fn m03_match_call_u32(a: u32, x: u32) -> u32 {
    match c_id(a) {
        0 => x,
        _ => a,
    }
}

#[inline(never)]
pub fn m04_match_cmp_of_call(a: u32, b: u32, x: u32, y: u32) -> u32 {
    match c_id(a) == b {
        true => x,
        false => y,
    }
}

// --- B: the `if` siblings of A. ----------------------------------------------------------------

#[inline(never)]
pub fn m05_if_call_bool(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if c_eq(a, b) { x } else { y }
}

#[inline(never)]
pub fn m06_if_cmp_of_call(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if c_id(a) == b { x } else { y }
}

// --- C: a call in an OPERAND position — `routed_operands` has no arm for the call's own args. --

#[inline(never)]
pub fn m07_cmp_of_two_calls(a: u32, b: u32) -> bool {
    c_id(a) == c_id(b)
}

#[inline(never)]
pub fn m08_and_of_call_and_param(a: u32, b: u32) -> u32 {
    c_id(a) & b
}

#[inline(never)]
pub fn m09_call_of_cmp_result(a: u32, b: u32) -> u32 {
    c_id(a & b)
}

#[inline(never)]
pub fn m10_call_of_call(a: u32) -> u32 {
    c_id(c_id(a))
}

// --- D: a call as the whole tail, and a call in one arm only. ---------------------------------

#[inline(never)]
pub fn m11_call_tail(a: u32) -> u32 {
    c_id(a)
}

#[inline(never)]
pub fn m12_call_in_one_arm(c: bool, a: u32, b: u32) -> u32 {
    if c { c_id(a) } else { b }
}

#[inline(never)]
pub fn m13_call_in_match_arm(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => c_id(a),
        false => b,
    }
}

// --- E: a call beside a field write — the write plan's straight-line grammar with a call. ------

#[derive(Clone, Copy)]
pub struct Box2 {
    pub u: u32,
    pub v: u32,
}

#[inline(never)]
pub fn m14_write_then_call_return(bx: &mut Box2, a: u32) -> u32 {
    bx.u = a;
    return c_id(a);
}

#[inline(never)]
pub fn m15_write_call_result(bx: &mut Box2, a: u32) {
    bx.u = c_id(a);
}

// --- F: a closure, which is its own def and asks every plan again on its own parameters. -------

#[inline(never)]
pub fn m16_closure_match_cmp(a: u32, b: u32) -> u32 {
    let f = |x: u32, y: u32| match x == y {
        true => x,
        false => y,
    };
    f(a, b)
}

// --- G: an IIFE closure whose ENCLOSING body admits the source-form gate while the closure's own
//        body does not. `source_form_admits` is asked per def and `typeck_root_def_id` names the
//        enclosing one; these rows exist so an attack that seals against the ROOT has something to
//        be measured on. ------------------------------------------------------------------------

#[inline(never)]
pub fn m17_iife_match_cmp(a: u32, b: u32) -> u32 {
    (|x: u32, y: u32| match x == y {
        true => x,
        false => y,
    })(a, b)
}

#[inline(never)]
pub fn m18_iife_if_cmp(a: u32, b: u32) -> u32 {
    (|x: u32, y: u32| if x == y { x } else { y })(a, b)
}

#[inline(never)]
pub fn m19_iife_match_bare(c: bool, a: u32, b: u32) -> u32 {
    (|f: bool, x: u32, y: u32| match f {
        true => x,
        false => y,
    })(c, a, b)
}

#[inline(never)]
pub fn m20_iife_plain_cmp(a: u32, b: u32) -> bool {
    (|x: u32, y: u32| x == y)(a, b)
}
