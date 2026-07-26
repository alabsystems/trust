#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): a bounded reduction into a WIDE accumulator
// from SIGNED narrow elements. `s += x as i32` over `&[i8; 8]` keeps the accumulator in
// `[8*-128, 8*127] = [-1024, 1016]`, comfortably inside i32 — but the reduction
// infrastructure was UNSIGNED-only (it emitted a single UPPER bound `acc <= C + K*MAX`,
// unsound when the addend can be negative), so signed elements were rejected and the
// per-add overflow stayed runtime-checked. Fixed by emitting the SYMMETRIC pair
// `[C + K*MIN, C + K*MAX]` for both the accumulator and the post-add sum
// (`signed_addend_per_iteration_range`); ay discharges both directions of the i-typed add
// overflow by Farkas. SELF-LIMITING: a genuinely-overflowing signed reduction has an
// endpoint outside the ACC type, so the bound fails to discharge (see the mutant twin).
pub fn sum_i8(a: &[i8; 8]) -> i32 {
    let mut s: i32 = 0;
    for &x in a {
        s += x as i32;
    }
    s
}

// i16 element → i64 accumulator: `[32 * -32768, 32 * 32767] = [-1048576, 1047520]` ⊂ i64.
pub fn sum_i16(a: &[i16; 32]) -> i64 {
    let mut s: i64 = 0;
    for &x in a {
        s += x as i64;
    }
    s
}
