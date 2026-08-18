// LANE MF-R5 — FIELD WRITES THE FIELD-WRITE PLAN REFUSES.
//
// Round 3's fix made the `recognize_field_write` arm ask a plan whose subject is the WHOLE body,
// so a `w.a = v` sitting next to any construct the plan cannot account for is refused — the
// derived body then carries no markers at all and reads as `built ... vs derived <end>`, an
// honest refusal. That refusal is the round's central asset: it is the difference between a
// wrong marker sequence and a fallback to built MIR.
//
// This file is that refusal's population, written from scratch: a single place-RHS field write
// wrapped in every construct that makes the whole-body plan say no, so a driver that finds ANY
// way back to a lease turns each of these from a refusal into an admitted-and-wrong body.
//
// No body name here appears in any of the 22 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr5_write \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr5_write.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::self_assignment)]
#![allow(clippy::needless_late_init, clippy::never_loop, clippy::no_effect, unused_unsafe)]

#[derive(Clone, Copy)]
pub struct R5 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
    pub d: u8,
    pub e: bool,
}

#[derive(Clone, Copy)]
pub struct Outer {
    pub head: u32,
    pub inner: R5,
}

pub const RK: u32 = 21;

// --- A: the write ALONE — the plan admits, and these must stay exact under every driver. ----

#[inline(never)]
pub fn r01_write_from_param(w: &mut R5, v: u32) {
    w.a = v;
}

#[inline(never)]
pub fn r02_write_from_field(w: &mut R5, s: R5) {
    w.b = s.b;
}

#[inline(never)]
pub fn r03_write_nested_from_param(o: &mut Outer, v: u32) {
    o.inner.a = v;
}

#[inline(never)]
pub fn r04_write_wide_from_param(w: &mut R5, v: u64) {
    w.c = v;
}

// --- B: the write PLUS a `let` — a named binding local the instruction stream cannot see. ---

#[inline(never)]
pub fn r05_write_after_let(w: &mut R5, v: u32) {
    let t = v;
    w.a = t;
}

#[inline(never)]
pub fn r06_write_before_let(w: &mut R5, v: u32) {
    w.a = v;
    let t = v;
}

#[inline(never)]
pub fn r07_write_between_lets(w: &mut R5, v: u32, u: u32) {
    let t = u;
    w.a = v;
    let s = t;
}

// --- C: the write PLUS a branch — built hoists the condition's temp into the head block, and
//        the arm knows nothing about it. -----------------------------------------------------

#[inline(never)]
pub fn r08_write_then_if(w: &mut R5, v: u32, c: bool) {
    w.a = v;
    if c {
        w.b = v;
    }
}

#[inline(never)]
pub fn r09_if_then_write(w: &mut R5, v: u32, c: bool) {
    if c {
        w.a = v;
    }
}

#[inline(never)]
pub fn r10_write_in_both_arms(w: &mut R5, v: u32, u: u32, c: bool) {
    if c {
        w.a = v;
    } else {
        w.b = u;
    }
}

#[inline(never)]
pub fn r11_write_under_cmp_cond(w: &mut R5, v: u32, u: u32) {
    if v == u {
        w.a = v;
    }
}

// --- D: the write PLUS a marker-free statement the grammar is not a whitelist for. -----------

#[inline(never)]
pub fn r12_write_then_return(w: &mut R5, v: u32) -> u32 {
    w.a = v;
    v
}

#[inline(never)]
pub fn r13_write_then_empty_loop(w: &mut R5, v: u32) {
    w.a = v;
    loop {
        break;
    }
}

#[inline(never)]
pub fn r14_write_inside_block(w: &mut R5, v: u32) {
    {
        w.a = v;
    }
}

#[inline(never)]
pub fn r15_write_then_unit_block(w: &mut R5, v: u32) {
    w.a = v;
    {}
}

#[inline(never)]
pub fn r16_unsafe_wrapped_write(w: &mut R5, v: u32) {
    unsafe {
        w.a = v;
    }
}

// --- E: TWO writes in one body — the plan counts pairs, and a forged lease that is capped at
//        one pair per body fails these CLOSED rather than admitting them wrong. --------------

#[inline(never)]
pub fn r17_two_writes_same_struct(w: &mut R5, v: u32, u: u32) {
    w.a = v;
    w.b = u;
}

#[inline(never)]
pub fn r18_three_writes(w: &mut R5, v: u32, u: u32, t: u64) {
    w.a = v;
    w.b = u;
    w.c = t;
}

#[inline(never)]
pub fn r19_two_writes_two_structs(w: &mut R5, x: &mut R5, v: u32) {
    w.a = v;
    x.a = v;
}

// --- F: the write PLUS an operand-tree neighbour — the two plans are mutually exclusive, so a
//        body holding both constructs is refused by BOTH. -----------------------------------

#[inline(never)]
pub fn r20_write_then_compare(w: &mut R5, v: u32, u: u32) -> bool {
    w.a = v;
    v == u
}

#[inline(never)]
pub fn r21_write_then_and(w: &mut R5, v: u32, u: u32) -> u32 {
    w.a = v;
    v & u
}

#[inline(never)]
pub fn r22_write_from_field_then_read(w: &mut R5, s: R5) -> u32 {
    w.a = s.a;
    s.b
}

// --- G: the write through a raw pointer, alone and in company. -----------------------------

#[inline(never)]
pub unsafe fn r23_ptr_write_from_param(p: *mut R5, v: u32) {
    (*p).a = v;
}

#[inline(never)]
pub unsafe fn r24_ptr_write_then_let(p: *mut R5, v: u32) {
    (*p).a = v;
    let t = v;
}

#[inline(never)]
pub unsafe fn r25_ptr_write_under_if(p: *mut R5, v: u32, c: bool) {
    if c {
        (*p).a = v;
    }
}
