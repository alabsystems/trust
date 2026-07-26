use trust_types::Formula;

use super::{BvGuardCmp, v2_bv_guard_constraint};

#[test]
fn signed_128_guard_renders_signed_bv_bound() {
    // `a < 100` at i128 → a signed-BV less-than over the fresh operand var.
    let r = v2_bv_guard_constraint("__trust_ovf_bv_lhs_a", BvGuardCmp::Lt, 100, 128, true);
    assert!(
        matches!(r, Some(Formula::BvSLt(..))),
        "signed-128 `a < 100` must render as BvSLt, got {r:?}"
    );
    // `a >= i128::MIN` is trivially in-range and renders (BvSLe(min, a)).
    assert!(
        v2_bv_guard_constraint("x", BvGuardCmp::Ge, i128::MIN, 128, true).is_some(),
        "signed-128 lower bound must render"
    );
}

#[test]
fn width_over_128_and_out_of_range_const_are_declined() {
    // width > 128: unsupported, declined (sound).
    assert!(v2_bv_guard_constraint("x", BvGuardCmp::Lt, 5, 129, true).is_none());
    // a constant outside the type's representable range is rejected.
    assert!(
        v2_bv_guard_constraint("x", BvGuardCmp::Lt, i128::MAX, 8, true).is_none(),
        "i128::MAX is far above i8::MAX, must be declined"
    );
    // unsigned-128 stays renderable (c is an i128, always <= i128::MAX <= u128::MAX).
    assert!(v2_bv_guard_constraint("x", BvGuardCmp::Lt, 1000, 128, false).is_some());
}
