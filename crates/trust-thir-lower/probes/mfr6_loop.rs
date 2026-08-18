// LANE MF-R6 (sixth review) — LOOPS, AND LOOPS WHOSE BODY WRITES A FIELD.
//
// `hir_tail_is_marker_free` recognizes exactly one loop by name — `loop { break; }` — and refuses
// every other loop grammar. `plan_field_write_markers` counts writes from a STRAIGHT-LINE statement
// list. A loop whose body writes a field is therefore a body where the SOURCE plan sees a shape it
// refuses and the trust-ir sees a multi-block CFG with a repeated `Store`: if the write arm ever
// emitted a pair per DYNAMIC execution while the plan counted per SOURCE occurrence, the two sides
// of the law would differ by the trip count — and the source-counted `marking_writes` is exactly
// what `predict` uses.
//
// This file also carries the loop shapes nothing has measured: a `while` with a comparison
// condition (whose operand temps built retires on the back edge as well as the exit edge), a
// `loop`/`break` with a value, nested loops, and a loop carrying a comparison in its body.
//
// No body name in this file appears in any of the 27 probe files rounds 1-5 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::needless_range_loop, clippy::while_immutable_condition)]
#![allow(clippy::never_loop, clippy::mut_range_bound)]

#[derive(Clone, Copy)]
pub struct Cell {
    pub v: u32,
    pub w: u32,
}

// --- A: the ONE named marker-free loop, and its neighbours by one token. -----------------------

#[inline(never)]
pub fn l01_write_then_loop_break(c: &mut Cell, v: u32) {
    c.v = v;
    loop {
        break;
    }
}

#[inline(never)]
pub fn l02_write_then_loop_break_value(c: &mut Cell, v: u32) -> u32 {
    c.v = v;
    loop {
        break 0;
    }
}

#[inline(never)]
pub fn l03_write_then_labelled_loop(c: &mut Cell, v: u32) {
    c.v = v;
    'a: loop {
        break 'a;
    }
}

#[inline(never)]
pub fn l04_write_then_loop_two_stmts(c: &mut Cell, v: u32) {
    c.v = v;
    loop {
        break;
    }
}

// --- B: LOOPS THAT WRITE A FIELD IN THE BODY — the write plan's shape under a back edge. -------

#[inline(never)]
pub fn l05_while_lt_writes_field(c: &mut Cell, n: u32) {
    let mut i = 0u32;
    while i < n {
        c.v = i;
        i += 1;
    }
}

#[inline(never)]
pub fn l06_loop_break_writes_field(c: &mut Cell, v: u32) {
    loop {
        c.v = v;
        break;
    }
}

#[inline(never)]
pub fn l07_loop_cond_break_writes(c: &mut Cell, n: u32) {
    let mut i = 0u32;
    loop {
        if i == n {
            break;
        }
        c.v = i;
        i += 1;
    }
}

#[inline(never)]
pub fn l08_while_writes_two_fields(c: &mut Cell, n: u32) {
    let mut i = 0u32;
    while i < n {
        c.v = i;
        c.w = i;
        i += 1;
    }
}

#[inline(never)]
pub fn l09_nested_loops_write_field(c: &mut Cell, n: u32, m: u32) {
    let mut i = 0u32;
    while i < n {
        let mut j = 0u32;
        while j < m {
            c.v = j;
            j += 1;
        }
        i += 1;
    }
}

// --- C: LOOPS WITH NO WRITE — a pure accumulator, so the branch plan owns the body. ------------

#[inline(never)]
pub fn l10_while_lt_accumulate(n: u32) -> u32 {
    let mut i = 0u32;
    let mut acc = 0u32;
    while i < n {
        acc = acc & i;
        i += 1;
    }
    acc
}

#[inline(never)]
pub fn l11_loop_with_inner_cmp(a: u32, b: u32) -> u32 {
    let mut k = a;
    loop {
        if k == b {
            break;
        }
        k = k & b;
    }
    k
}

#[inline(never)]
pub fn l12_while_bool_flag(f: bool, a: u32) -> u32 {
    let mut k = a;
    while f {
        k = k & 1;
        break;
    }
    k
}

// --- D: WRITE + LOOP TAIL in the exact two spellings the write plan distinguishes. -------------

#[inline(never)]
pub fn l13_write_semi_then_loop_tail(c: &mut Cell, v: u32) {
    c.v = v;
    loop {
        break;
    }
}

#[inline(never)]
pub fn l14_loop_tail_only(c: &mut Cell) {
    loop {
        break;
    }
}

// --- E: a loop whose CONDITION is a field comparison — two plans' inputs in one CFG. -----------

#[inline(never)]
pub fn l15_while_field_cmp_writes_other(c: &mut Cell) {
    while c.v == c.w {
        c.v = 0;
    }
}
