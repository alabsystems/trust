// Source of the `shift_amount_guard_copy_*_mir.json` fixtures beside this file.
// Captured with the stage1 compiler's own extraction, both lanes:
//
//   trustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> \
//          crates/trust-vcgen/tests/fixtures/shift_amount_guard_copy.rs
//   trustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> \
//          crates/trust-vcgen/tests/fixtures/shift_amount_guard_copy.rs
//
// These are the `signed_max` shape, because that is the only lane that reaches
// `v2_dominating_strict_upper_bound`: the dominating shift-amount bound is
// emitted by `v2_collect_bv_shl_blockdef`, which runs for a SIGNED 128-bit
// overflow row whose operand is defined by `Shl(const, amount)`.
//
// The row of interest is the `Sub` overflow of `(1i128 << (width - 1)) - 1`. It
// is provable EXACTLY when a dominating bound puts the shift amount below 127:
// at `amount = 127` the shift result is `i128::MIN` and `- 1` really underflows.

/// SAFE. Exercises BOTH entries to the helper: the direct dominating bound on the
/// shift amount, and the bound established on the `amount = width - 1` SOURCE and
/// carried through the subtraction (`width <= 127` ⇒ `amount <= 126`).
pub fn signed_max_safe(width: u32) -> i128 {
    if width >= 1 && width <= 127 { (1i128 << (width - 1)) - 1 } else { 0 }
}

/// UNSAFE twin of `signed_max_safe`: the `Overflow(Shl)` assert still bounds the
/// amount below 128, but nothing bounds it below 127. `width = 128` gives
/// `1i128 << 127 == i128::MIN`, and `i128::MIN - 1` underflows.
pub fn signed_max_unbounded_unsafe(width: u32) -> i128 {
    if width >= 1 { (1i128 << (width - 1)) - 1 } else { 0 }
}

/// UNSAFE. The only shape in which Trust's extraction actually hands this lane a
/// guard whose subject is a COPY of the shift amount's source: `g` is a two-def
/// local, one of whose definitions is `g = width`. The guard bounds `g`; the
/// shift reads `width`; on the other path `g` is 1 while `width` may be 128. A
/// copy hop that bridged the joined definition would prove a real underflow.
pub fn signed_max_joined_copy_unsafe(width: u32, j: u32) -> i128 {
    let mut g = width;
    if j > 3 {
        g = 1;
    }
    if g <= 127 && width >= 1 { (1i128 << (width - 1)) - 1 } else { 0 }
}

/// SAFE control for the same shape: the joined copy is still there and still
/// contributes nothing, and the DIRECT bound on `width` proves the row. Pins that
/// the joined copy neither helps nor hurts.
pub fn signed_max_joined_copy_safe(width: u32, j: u32) -> i128 {
    let mut g = width;
    if j > 3 {
        g = 1;
    }
    if g <= 127 && width >= 1 && width <= 127 { (1i128 << (width - 1)) - 1 } else { 0 }
}
