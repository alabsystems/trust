// GROUP 3 probe corpus: havocked callee return reported as a REFUTATION.
//
// (a) CANNOT-FAULT rows: no execution can violate the obligation, so REFUTED
//     is a FALSE REFUTATION.
// (b) REAL BUG rows with LOCAL operands: must STAY refuted.
#![allow(dead_code)]
#![crate_type = "lib"]

// --- (a) unmodelled std call feeding a DIVISOR -----------------------------
// `core::cmp::max(x, 1) >= 1` for every x.
pub fn hv_div_cmp_max(x: u32) -> u32 {
    100u32 / core::cmp::max(x, 1)
}

// `c.len_utf8()` is in 1..=4 for every char.
pub fn hv_div_len_utf8(c: char) -> usize {
    100usize / c.len_utf8()
}

// --- (a) unmodelled std call feeding an OVERFLOW ---------------------------
// `core::cmp::min(x, 10) + 1 <= 11`, never overflows u32.
pub fn hv_add_cmp_min(x: u32) -> u32 {
    core::cmp::min(x, 10) + 1
}

// --- (a) unmodelled std call feeding a BOUNDS CHECK ------------------------
// `core::cmp::min(x, 3) <= 3 < 4`.
pub fn hv_idx_cmp_min(x: usize) -> u32 {
    let a: [u32; 4] = [1, 2, 3, 4];
    a[core::cmp::min(x, 3)]
}

// --- (a) size_of / align_of, CLOSED and INPUT-FREE -------------------------
pub fn hv_div_size_of() -> usize {
    1024usize / core::mem::size_of::<u64>()
}
pub fn hv_div_align_of() -> usize {
    1024usize / core::mem::align_of::<u32>()
}
pub fn hv_idx_size_of() -> u8 {
    let a: [u8; 16] = [0; 16];
    a[core::mem::size_of::<u32>()]
}
pub fn hv_idx_align_of() -> u8 {
    let a: [u8; 16] = [0; 16];
    a[core::mem::align_of::<u64>()]
}

// --- CONTROL: same-crate callee -------------------------------------------
#[inline(never)]
pub fn hv_local_max(a: u32, b: u32) -> u32 {
    if a > b { a } else { b }
}
pub fn hv_div_local_max(x: u32) -> u32 {
    100u32 / hv_local_max(x, 1)
}

// --- CONTROL: leading_zeros -----------------------------------------------
// NB `x.leading_zeros()` IS 0 for x >= 0x8000_0000, so this really can divide
// by zero: the correct verdict is a refutation or a decline, never Proved.
pub fn hv_div_leading_zeros(x: u32) -> u32 {
    100u32 / x.leading_zeros()
}
// `leading_zeros(x) <= 32 < 64`, so this index CANNOT fault.
pub fn hv_idx_leading_zeros(x: u32) -> u8 {
    let a: [u8; 64] = [0; 64];
    a[x.leading_zeros() as usize]
}

// --- (b) REAL BUGS, all operands LOCAL. MUST STILL REFUTE. -----------------
pub fn hv_real_overflow(x: u32) -> u32 {
    x + 1
}
pub fn hv_real_divzero(x: u32, y: u32) -> u32 {
    x / y
}
pub fn hv_real_bounds(i: usize) -> u32 {
    let a: [u32; 4] = [1, 2, 3, 4];
    a[i]
}

// --- (b) REAL BUG through an unmodelled std call ---------------------------
// `core::cmp::min(x, 1)` is 0 at x == 0: a genuine division by zero. Must
// never become Proved.
pub fn hv_real_divzero_via_call(x: u32) -> u32 {
    100u32 / core::cmp::min(x, 1)
}

// --- (c) a DIFFERENT emitter's `UnsupportedMir` row, carried here so the
//         crate-wide fail-closed-polarity sweep actually reaches one. -------
// `&v[..end]` over an owned `Vec` whose length is a non-derivable abstract
// placeholder: `panic_calls`'s soft-len arm declines rather than false-REFUTE.
// The row this produces is `UnsupportedMir { kind: "SliceBoundsCheck" }`, NOT a
// `UnmodeledCalleeReturn`. This body DOES panic (`end > v.len()`), so the
// decline must never be readable as a discharge.
pub fn hv_slice_soft_len(v: Vec<u32>, end: usize) -> usize {
    let s = &v[..end];
    s.len()
}

// Both passes at once: an unmodelled call feeding the divisor (this pass
// DECLINES it) alongside the soft-len slice row above (a DIFFERENT emitter's
// decline). This is the shape whose two coexisting `UnsupportedMir` rows a
// crate-wide `debug_assert!` inside the reclassification pass turned into a
// compiler panic on valid Rust.
pub fn hv_slice_soft_len_and_call(v: Vec<char>, end: usize, x: u32) -> u32 {
    let n = core::cmp::max(x, 1);
    let s = &v[..end];
    (s.len() as u32) / n
}
