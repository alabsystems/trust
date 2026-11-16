//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A same-crate helper's return INTERVAL reaches its callers
//! (`compute_return_interval_summaries`, 2026-09-30): the production interval
//! fixpoint over the helper's own body, for every input, joined over its returns.
//! Each caller below was refused before, for want of any fact about the call's
//! result. `return_interval_bounds_the_call_result_refused.rs` is the twin.

fn widen(x: u8) -> u32 {
    x as u32 + 1
}

// Each `widen` result is in `[1, 256]`, so the sum is at most 512.
pub fn widened_sum(a: u8, b: u8) -> u32 {
    widen(a) + widen(b)
}

// And at least 1: a divisor that is never zero.
pub fn divide_by_widened(h: u32, x: u8) -> u32 {
    h / widen(x)
}

#[derive(Clone, Copy)]
pub enum Dir {
    North,
    East,
    South,
    West,
}

impl Dir {
    pub fn index(self) -> usize {
        self as usize
    }
}

// A fieldless enum's discriminant, cast: at most 3.
pub fn lookup(table: &[u8; 4], d: Dir) -> u8 {
    table[d.index()]
}

fn clamp10(n: u32) -> u32 {
    if n > 10 { 10 } else { n }
}

pub fn clamped_index(a: &[u8; 11], n: u32) -> u8 {
    a[clamp10(n) as usize]
}

pub struct S {
    pub x: u8,
}

impl S {
    pub fn widened(&self) -> u32 {
        self.x as u32 + 1
    }
}

// A field read through `&self` is a value of its type.
pub fn method_field_sum(s: &S, t: &S) -> u32 {
    s.widened() + t.widened()
}
