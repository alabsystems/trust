#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]

// ---- Channel 1 shape: slice range index over an OWNED Vec (non-derivable len) ----
#[trust::ensures(result < 8)]
pub fn vec_range_index_with_ensures(v: Vec<u32>, end: usize) -> u32 {
    let _s = &v[..end];
    7
}

// ---- Channel-2 style probes: panicking bodies whose safety rows are declines ----

pub fn a1_min_div(a: u32, b: u32) -> u32 {
    a / b.min(3)
}

pub fn a2_min_sub(a: u32, b: u32) -> u32 {
    a.min(4) - b
}

pub fn a3_char_idx(s: &str, i: usize) -> u8 {
    s.as_bytes()[i]
}

pub fn a7_max_mul(a: u32, b: u32) -> u32 {
    a.max(2) * b
}

pub fn e3_branch_div(a: u32, b: u32, c: bool) -> u32 {
    if c { a / b } else { a / (b + 1) }
}

pub fn e5_straight_idx(v: Vec<u32>, i: usize) -> u32 {
    v[i]
}

// ---- three more panicking bodies of my own ----

// P1: slice RANGE index over an owned Vec (no ensures) — declined SliceBoundsCheck.
pub fn p1_vec_range_sum(v: Vec<u32>, end: usize) -> u32 {
    let s = &v[..end];
    s.len() as u32
}

// P2: an unmodelled callee return feeding a division.
#[inline(never)]
pub fn opaque_divisor(x: u32) -> u32 {
    x.wrapping_sub(1)
}
pub fn p2_opaque_callee_div(a: u32, x: u32) -> u32 {
    a / opaque_divisor(x)
}

// P3: an opaque call (HashMap index — key presence unmodelled) that panics.
pub fn p3_map_index(m: std::collections::HashMap<u32, u32>, k: u32) -> u32 {
    m[&k]
}

// ---- MUST-STILL-CERTIFY controls (genuinely safe) ----
#[trust::requires(b != 0)]
#[trust::ensures(result <= a)]
pub fn safe_div(a: u32, b: u32) -> u32 {
    a / b
}

#[trust::requires(a < 1000)]
#[trust::requires(b < 1000)]
#[trust::ensures(result < 2000)]
pub fn safe_add(a: u32, b: u32) -> u32 {
    a + b
}
