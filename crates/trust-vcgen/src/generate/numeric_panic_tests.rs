// Trust (2026-09-25, std-numeric-family): the NAME-LEVEL half of
// `numeric_panic` — `is_numeric_value_panic_callee`, which the compiler consults
// through `callee_has_call_site_panic_family` for a sysroot fn ITEM handed to a
// callee as a type argument. Every positive spelling below is one rustc rendered
// for a probe on stage-1 `8d6aadf7e9` (`-Ztrust-dump=mir-only`); the negatives
// are the total siblings, user spellings and stamped impersonators that must
// NOT be read as the family.

use super::numeric_panic::{is_clock_reading_callee, is_numeric_value_panic_callee};

#[test]
fn every_measured_panicking_spelling_is_in_the_family() {
    for callee in [
        "<i32 as core::cmp::Ord>::clamp",
        "<T as core::cmp::Ord>::clamp",
        "<core::time::Duration as core::cmp::Ord>::clamp",
        "core::f64::<impl f64>::clamp",
        "core::f32::<impl f32>::clamp",
        "core::num::<impl u32>::ilog2",
        "core::num::<impl u32>::ilog10",
        "core::num::<impl u32>::ilog",
        "core::num::<impl i64>::isqrt",
        "core::num::<impl u32>::next_power_of_two",
        "core::num::<impl u32>::next_multiple_of",
        "core::num::<impl i32>::div_euclid",
        "core::num::<impl i32>::rem_euclid",
        "core::num::<impl u32>::from_str_radix",
        "core::num::<impl u32>::strict_add",
        "core::num::<impl u32>::strict_div",
        "core::num::<impl u32>::strict_pow",
        "core::num::nonzero::NonZero::<u32>::from_str_radix",
        "core::num::nonzero::NonZero::<i32>::abs",
        "<core::num::nonzero::NonZero<i32> as core::ops::arith::Neg>::neg",
        "core::char::from_digit",
        "core::char::methods::<impl char>::from_digit",
        "core::char::methods::<impl char>::is_digit",
        "core::char::methods::<impl char>::to_digit",
        "core::time::Duration::new",
        "core::time::Duration::from_secs_f64",
        "core::time::Duration::from_mins",
        "<core::time::Duration as core::ops::arith::Add>::add",
        "<core::time::Duration as core::ops::arith::AddAssign>::add_assign",
        "<core::time::Duration as core::ops::arith::Div<u32>>::div",
        "<core::time::Duration as core::ops::arith::MulAssign<u32>>::mul_assign",
        "<u32 as core::ops::arith::Mul<core::time::Duration>>::mul",
        "<std::time::Instant as core::ops::arith::Add<core::time::Duration>>::add",
        "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
        "<u32 as core::ops::arith::Add>::add",
        "<u8 as core::ops::bit::Shl<i8>>::shl",
        "<i32 as core::ops::arith::Neg>::neg",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::next",
        "<core::ops::range::RangeFrom<char> as core::iter::traits::iterator::Iterator>::next",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::nth",
        "<core::ops::range::RangeInclusive<u64> as core::iter::traits::iterator::Iterator>::count",
        "<core::ops::range::Range<u128> as core::iter::traits::iterator::Iterator>::count",
        // Review of `ff3a28cc92` (2026-09-28): the compound-assign operators on a
        // primitive, a `RangeFrom` consumer, and the `&mut RangeFrom` spelling.
        "<i32 as core::ops::arith::AddAssign>::add_assign",
        "<u32 as core::ops::arith::SubAssign>::sub_assign",
        "<i64 as core::ops::arith::MulAssign>::mul_assign",
        "<u32 as core::ops::bit::ShlAssign>::shl_assign",
        "<u8 as core::ops::bit::ShrAssign<i8>>::shr_assign",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::find::<{closure@nm.rs:1:1: 1:2}>",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::count",
        "<core::ops::range::RangeFrom<char> as core::iter::traits::iterator::Iterator>::position::<F>",
        "<&mut core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::next",
    ] {
        assert!(is_numeric_value_panic_callee(callee), "{callee} must be in the family");
    }
}

/// Trust (ASCII-FROM-ASCII-RADIX-1, 2026-10-05): the nightly `int_from_ascii`
/// parser `from_ascii_radix` runs the radix check `from_str_radix` delegates to
/// (core `num/mod.rs`: "from_ascii_radix: radix must lie in the range `[2, 36]`"),
/// but the 2026-09-25 audit covered stable methods only, so it built rc=0 on the
/// default lane and panicked on radix 37 (and `NonZero`'s on radix 1). Spellings
/// as rustc renders them (`-Ztrust-dump=mir-only`, the stage 1 of `ec03f72395`).
/// `from_ascii` fixes radix 10 and is total.
#[test]
fn from_ascii_radix_is_in_the_family_and_from_ascii_is_not() {
    for callee in [
        "core::num::<impl u32>::from_ascii_radix",
        "core::num::<impl i64>::from_ascii_radix",
        "core::num::nonzero::NonZero::<u32>::from_ascii_radix",
    ] {
        assert!(is_numeric_value_panic_callee(callee), "{callee} must be in the family");
    }
    for callee in [
        "core::num::<impl u32>::from_ascii",
        "core::num::nonzero::NonZero::<u32>::from_ascii",
        "mycrate::num::<impl u32>::from_ascii_radix",
        "__trust_crate@1973d11b2baa21fa::core::num::<impl u32>::from_ascii_radix",
    ] {
        assert!(!is_numeric_value_panic_callee(callee), "{callee} must NOT be in the family");
    }
}

#[test]
fn total_siblings_user_spellings_and_impersonators_are_not() {
    for callee in [
        // total siblings
        "core::num::<impl u32>::checked_ilog2",
        "core::num::<impl u32>::isqrt",
        "core::num::<impl u32>::div_euclid",
        "core::num::<impl i32>::next_power_of_two",
        "core::num::<impl u32>::checked_next_multiple_of",
        "core::num::<impl u32>::midpoint",
        "core::num::nonzero::NonZero::<u32>::ilog2",
        "core::num::nonzero::NonZero::<u32>::abs",
        "<u32 as core::cmp::Ord>::max",
        "<std::time::Instant as core::ops::arith::Sub>::sub",
        "core::time::Duration::from_secs",
        "core::time::Duration::checked_add",
        "<core::ops::range::Range<u32> as core::iter::traits::iterator::Iterator>::next",
        // Trust (W32-PRIMINT-PIN-1, 2026-10-06): these were `Range<u64>` and
        // `RangeInclusive<u32>`. Both are total on a 64-bit target, but both panic
        // "count overflowed usize" on a 32-bit one. A name carries no target, so
        // they are now in the family (`numeric_panic_ptr_width_tests`). These two
        // are total at every pointer width.
        "<core::ops::range::Range<u16> as core::iter::traits::iterator::Iterator>::count",
        "<core::ops::range::RangeInclusive<u8> as core::iter::traits::iterator::Iterator>::count",
        // the ruled reference-arithmetic class, and a plain `u32` product
        "<u32 as core::ops::arith::Add<&u32>>::add",
        "<&u32 as core::ops::arith::Add<u32>>::add",
        "<u32 as core::ops::arith::Div>::div",
        "<i32 as core::ops::arith::AddAssign<&i32>>::add_assign",
        // a `RangeFrom` ADAPTOR advances nothing at its own call (the recorded
        // bundled-adaptor survivor), and `size_hint` is total
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::take",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::zip::<std::vec::IntoIter<u8>>",
        "<core::ops::range::RangeFrom<u8> as core::iter::traits::iterator::Iterator>::size_hint",
        // user spellings that merely share a name
        "mycrate::Mine::ilog2",
        "<u32 as mycrate::MyClamp>::clamp",
        "<mycrate::Duration2 as core::ops::arith::Add>::add",
        "mycrate::num::<impl u32>::ilog2",
        // a stamped impersonator of `core`
        "__trust_crate@1973d11b2baa21fa::core::num::<impl u32>::ilog2",
        "<i32 as __trust_crate@1973d11b2baa21fa::core::cmp::Ord>::clamp",
        "<i32 as __trust_crate@1973d11b2baa21fa::core::ops::arith::AddAssign>::add_assign",
    ] {
        assert!(!is_numeric_value_panic_callee(callee), "{callee} must NOT be in the family");
    }
    // Positive control for the `Mul` negative above: the same trait, by value,
    // without a turbofish, IS in the family — the negative is not vacuous.
    assert!(is_numeric_value_panic_callee("<u32 as core::ops::arith::Mul>::mul"));
}

#[test]
fn only_an_authenticated_std_clock_is_a_fresh_reading() {
    // The GRANTING half of the time-point carve-out (review follow-up,
    // 2026-09-28): a literal `Duration` on a time point mints nothing only when
    // that point is one of these calls' results.
    assert!(is_clock_reading_callee("std::time::Instant::now"));
    assert!(is_clock_reading_callee("std::time::SystemTime::now"));
    for callee in [
        "std::time::Instant::elapsed",
        "std::time::SystemTime::checked_add",
        "mycrate::time::Instant::now",
        "mycrate::Clock::now",
        "__trust_crate@1973d11b2baa21fa::std::time::Instant::now",
    ] {
        assert!(
            !is_clock_reading_callee(callee),
            "{callee} must NOT read as a fresh clock reading"
        );
    }
}

/// Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): the nightly integer and `Duration`
/// methods that panic on the caller's value. The 2026-09-25 audit covered stable
/// methods only, so each built rc=0 on the default lane of the stage 1 of
/// `9e11546767` and a verify-off driver passing the value exited 101. The positive
/// spellings are the extractor's (`-Ztrust-dump=mir-only` on that stage 1), so a fn
/// item handed over as a type argument (`o.map(u32::strict_cast_signed)`) is
/// withheld too. The negatives are the total siblings, the shapes core defines only
/// on the other signedness (`funnel_shl` exists only on uN, `strict_cast_signed`
/// only on uN, `strict_cast_unsigned` only on iN), user spellings and a stamped
/// impersonator.
#[test]
fn the_nightly_value_panicking_methods_are_in_the_family() {
    for callee in [
        "core::num::<impl i32>::next_multiple_of",
        "core::num::<impl i8>::next_multiple_of",
        "core::num::<impl u32>::funnel_shl",
        "core::num::<impl u64>::funnel_shr",
        "core::num::<impl u32>::strict_cast::<u8>",
        "core::num::<impl i64>::strict_cast::<i8>",
        "core::num::<impl u32>::strict_cast::<T>",
        "core::num::<impl u32>::strict_cast_signed",
        "core::num::<impl i32>::strict_cast_unsigned",
        "core::time::Duration::from_days",
        "core::time::Duration::from_weeks",
    ] {
        assert!(is_numeric_value_panic_callee(callee), "{callee} must be in the family");
    }
    for callee in [
        // total siblings
        "core::num::<impl i32>::checked_next_multiple_of",
        "core::num::<impl u32>::checked_cast::<u8>",
        "core::num::<impl u32>::saturating_cast::<u8>",
        "core::num::<impl u32>::wrapping_cast::<u8>",
        "core::num::<impl u32>::cast_signed",
        "core::num::<impl u32>::checked_cast_signed",
        "core::num::<impl i32>::saturating_cast_unsigned",
        "core::num::<impl u32>::rotate_left",
        "core::time::Duration::from_secs",
        // no such method on this signedness
        "core::num::<impl i32>::funnel_shl",
        "core::num::<impl i64>::funnel_shr",
        "core::num::<impl i32>::strict_cast_signed",
        "core::num::<impl u32>::strict_cast_unsigned",
        // user spellings that merely share a name
        "mycrate::W::funnel_shl",
        "mycrate::num::<impl u32>::funnel_shl",
        "mycrate::time::Duration::from_days",
        // a stamped impersonator of `core`
        "__trust_crate@1973d11b2baa21fa::core::num::<impl u32>::strict_cast::<u8>",
        "__trust_crate@1973d11b2baa21fa::core::time::Duration::from_weeks",
    ] {
        assert!(!is_numeric_value_panic_callee(callee), "{callee} must NOT be in the family");
    }
}

/// Trust (wave-19 review, 2026-10-09): the TRAIT spelling of `strict_cast`,
/// `<Dst as core::convert::num::CheckedCastFromInt<Src>>::strict_cast_from` (the
/// extractor renders the defining module `core::convert::num`, measured with
/// `-Ztrust-dump=mir-only` on the stage 1 of `46e9afaf95`; the unsafe lane renders the
/// unqualified trait-item path). Handed over as a fn item
/// (`o.map(<u8 as CheckedCastFromInt<u32>>::strict_cast_from)`) it was admitted with no
/// row and panicked verify-off; in the family, the admission is withheld. Its total
/// siblings, a user trait of the same name and a stamped trait are not in it.
#[test]
fn the_checked_cast_trait_strict_cast_from_is_in_the_family() {
    for callee in [
        "<u8 as core::convert::num::CheckedCastFromInt<u32>>::strict_cast_from",
        "<i8 as core::convert::num::CheckedCastFromInt<i64>>::strict_cast_from",
        "<u64 as core::convert::num::CheckedCastFromInt<i32>>::strict_cast_from",
        "<T as core::convert::num::CheckedCastFromInt<u32>>::strict_cast_from",
        "core::convert::num::CheckedCastFromInt::strict_cast_from",
    ] {
        assert!(is_numeric_value_panic_callee(callee), "{callee} must be in the family");
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    for callee in [
        // total siblings
        "<u8 as core::convert::num::CheckedCastFromInt<u32>>::checked_cast_from",
        "<u8 as core::convert::num::BoundedCastFromInt<u32>>::wrapping_cast_from",
        "<u8 as core::convert::num::BoundedCastFromInt<u32>>::saturating_cast_from",
        "core::convert::num::CheckedCastFromInt::checked_cast_from",
        // the `unsafe` one is the unsafe lane's (`[unsafe:unmodeled-call]`)
        "<u8 as core::convert::num::CheckedCastFromInt<u32>>::unchecked_cast_from",
        // user traits that merely share the name
        "<u8 as mycrate::CheckedCastFromInt<u32>>::strict_cast_from",
        "<u8 as mycrate::convert::num::CheckedCastFromInt<u32>>::strict_cast_from",
        "mycrate::convert::num::CheckedCastFromInt::strict_cast_from",
        // a stamped impersonator of `core`
        "<u8 as __trust_crate@1973d11b2baa21fa::core::convert::num::CheckedCastFromInt<u32>>::strict_cast_from",
        "__trust_crate@1973d11b2baa21fa::core::convert::num::CheckedCastFromInt::strict_cast_from",
    ] {
        assert!(!is_numeric_value_panic_callee(callee), "{callee} must NOT be in the family");
    }
}

/// W4 ITER-HOF fix round 4 (2026-10-02): the name-only union the compiler asks of a
/// sysroot fn ITEM handed over as a type argument names the zero-divisor and `pow`
/// call-site families too (`divzero_call`, `overflow_arith_call`), which
/// `is_numeric_value_panic_callee` deliberately leaves to them. Spellings as
/// `safe_def_path_str_with_args` renders the items of adversarial probes q07/q08
/// (`reduce(u32::div_ceil)`, `fold(2, u32::pow)`), which built rc=0 and panicked.
#[test]
fn the_zero_divisor_and_pow_families_withhold_a_sysroot_item() {
    for callee in [
        "core::num::<impl u32>::div_ceil",
        "core::num::<impl u64>::div_ceil",
        "core::num::<impl u32>::pow",
        "core::num::<impl i32>::pow",
        "core::num::<impl usize>::pow",
        "core::num::<impl u32>::div_euclid",
        "core::num::<impl u32>::rem_euclid",
    ] {
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    // The total siblings stay admissible: the families are matched on the exact
    // method tail, so none of these is read as `pow`/`div_ceil`.
    for callee in [
        "core::num::<impl u32>::checked_pow",
        "core::num::<impl u32>::wrapping_pow",
        "core::num::<impl u32>::saturating_pow",
        "core::num::<impl u32>::overflowing_pow",
        "core::num::<impl u32>::checked_div_euclid",
        "core::num::<impl u32>::checked_next_multiple_of",
        "core::f64::<impl f64>::powi",
        "core::f64::<impl f64>::powf",
    ] {
        assert!(
            !super::callee_has_call_site_panic_family(callee),
            "`{callee}` cannot panic and must stay admissible"
        );
    }
}

/// W4 ITER-HOF fix round 4 (2026-10-02): the integer division OPERATORS, handed as
/// items (`fold(7u32, core::ops::Div::div)`), are withheld too. The spellings are
/// the extractor's (`-Ztrust-dump=mir` on stage 1 of `a3be88bbde`: `fn(u32, &u32) ->
/// .. {<u32 as core::ops::arith::Div<&u32>>::div}`, `{<core::num::wrapping::Wrapping<u32>
/// as core::ops::arith::Div>::div}`).
#[test]
fn integer_division_operators_withhold_a_sysroot_item() {
    use super::numeric_panic::is_int_division_operator_callee as div_op;
    for callee in [
        "<u32 as core::ops::arith::Div>::div",
        "<u32 as core::ops::arith::Rem>::rem",
        "<i32 as core::ops::arith::Div>::div",
        "<u32 as core::ops::arith::Div<&u32>>::div",
        "<u32 as core::ops::arith::Rem<&u32>>::rem",
        "<&u64 as core::ops::arith::Div<u64>>::div",
        "<&'a u8 as core::ops::arith::Div<&'b u8>>::div",
        "<usize as core::ops::arith::DivAssign>::div_assign",
        "<i64 as core::ops::arith::RemAssign<&i64>>::rem_assign",
        "<core::num::wrapping::Wrapping<u32> as core::ops::arith::Div>::div",
        concat!(
            "<core::num::wrapping::Wrapping<i8> as ",
            "core::ops::arith::Rem<&core::num::wrapping::Wrapping<i8>>>::rem"
        ),
        "<core::num::saturating::Saturating<u32> as core::ops::arith::Div>::div",
    ] {
        assert!(div_op(callee), "{callee} must be an integer division operator");
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    for callee in [
        // a `NonZero` divisor cannot be zero; a float divides totally
        "<u32 as core::ops::arith::Div<core::num::nonzero::NonZero<u32>>>::div",
        "<u32 as core::ops::arith::Rem<core::num::nonzero::NonZero<u32>>>::rem",
        "<f64 as core::ops::arith::Div>::div",
        // `Duration / 0` panics, but it is `is_numeric_value_panic_callee`'s
        // (`DURATION_OPS`), not an integer operator
        "<core::time::Duration as core::ops::arith::Div<u32>>::div",
        // not a division
        "<u32 as core::ops::arith::Add>::add",
        "core::num::<impl u32>::checked_div",
        // a user type or trait that merely shares the names
        "<mycrate::Num as core::ops::arith::Div>::div",
        "<u32 as mycrate::ops::Div>::div",
        "<mycrate::Wrapping<u32> as core::ops::arith::Div>::div",
        // a stamped impersonator of `core`
        "<u32 as __trust_crate@1973d11b2baa21fa::core::ops::arith::Div>::div",
    ] {
        assert!(!div_op(callee), "{callee} must NOT be read as an integer division operator");
    }
}

/// W4 ITER-HOF fix round 4 (2026-10-02): an integer `sum`/`product` handed as an
/// item (`map(Iterator::sum::<u32>)`) is withheld like the direct call it stands for
/// (charged `iterator-fold-overflow`); a float or `Wrapping` accumulator is not.
#[test]
fn integer_sum_and_product_items_withhold_a_sysroot_item() {
    const ITER: &str =
        "<core::slice::iter::Iter<'_, u32> as core::iter::traits::iterator::Iterator>";
    const FITER: &str =
        "<core::slice::iter::Iter<'_, f64> as core::iter::traits::iterator::Iterator>";
    let withheld = [
        format!("{ITER}::sum::<u32>"),
        format!("{ITER}::product::<u32>"),
        format!("{ITER}::sum::<core::option::Option<u32>>"),
        format!("{ITER}::sum::<core::result::Result<u64, u8>>"),
        "<u32 as core::iter::traits::accum::Sum<&u32>>::sum::<core::slice::iter::Iter<'_, u32>>"
            .to_string(),
        "<i64 as core::iter::traits::accum::Product>::product::<alloc::vec::IntoIter<i64>>"
            .to_string(),
    ];
    for callee in &withheld {
        assert!(
            super::alloc_bounds::iterator_fold_item_may_overflow(callee),
            "{callee} may overflow"
        );
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    let admitted = [
        format!("{FITER}::sum::<f64>"),
        format!("{FITER}::product::<f64>"),
        "<f32 as core::iter::traits::accum::Sum<&f32>>::sum::<core::slice::iter::Iter<'_, f32>>"
            .to_string(),
        format!("{ITER}::sum::<core::num::wrapping::Wrapping<u32>>"),
        format!("{ITER}::sum::<core::num::saturating::Saturating<u32>>"),
        format!("{ITER}::max"),
        format!("{ITER}::count"),
        "<mycrate::It as mycrate::Iterator>::sum::<u32>".to_string(),
    ];
    for callee in &admitted {
        assert!(
            !super::alloc_bounds::iterator_fold_item_may_overflow(callee),
            "{callee} cannot overflow (or is not a std fold)"
        );
        assert!(
            !super::callee_has_call_site_panic_family(callee),
            "`{callee}` must stay admissible"
        );
    }
}

/// ARGS-FINGERPRINT-READ-1: the accumulator is the method's turbofish, never the
/// duplicate-crate-name fingerprint behind it. The compiler's fn-item admission
/// renders the item with `safe_def_path_str_with_args` (no tag) today; this pins
/// that a tagged spelling reads the same accumulator rather than `__trust_args@…`.
#[test]
fn the_fold_accumulator_is_read_past_the_argument_fingerprint() {
    const FITER: &str =
        "<core::slice::iter::Iter<'_, f64> as core::iter::traits::iterator::Iterator>";
    const ITER: &str =
        "<core::slice::iter::Iter<'_, u32> as core::iter::traits::iterator::Iterator>";
    let tag = trust_types::render_trailing_args_fingerprint(0x45ac_9e83, 0xfad7);
    // POSITIVE: a float accumulator cannot overflow, tag or no tag.
    assert!(!super::alloc_bounds::iterator_fold_item_may_overflow(&format!(
        "{FITER}::sum::<f64>{tag}"
    )));
    // NEGATIVE: an integer accumulator still may.
    assert!(super::alloc_bounds::iterator_fold_item_may_overflow(&format!(
        "{ITER}::sum::<u32>{tag}"
    )));
    // ROUND 2: `Wrapping` is a TYPE PATH. Untagged it is the real one and cannot
    // overflow; on a tagged callee it may be a crate built `--crate-name core`.
    const WRAP: &str = "core::num::wrapping::Wrapping<u32>";
    assert!(!super::alloc_bounds::iterator_fold_item_may_overflow(&format!(
        "{ITER}::sum::<{WRAP}>"
    )));
    assert!(super::alloc_bounds::iterator_fold_item_may_overflow(&format!(
        "{ITER}::sum::<{WRAP}>{tag}"
    )));
    // NEGATIVE: a lookalike tag is not stripped, so the reader sees it and fails
    // closed (withheld), as before.
    assert!(super::alloc_bounds::iterator_fold_item_may_overflow(&format!(
        "{FITER}::sum::<f64>::<__trust_args@45ac9e83>"
    )));
}

/// W4 ITER-HOF fix round 6 (2026-10-03): the integer OVERFLOW-checked operators,
/// handed as items — by value and, the new half, BY REFERENCE (`v.iter().fold(0u32,
/// core::ops::Add::add)`), which the call-site family leaves to the ruled
/// foundational-member class — are withheld too. The by-reference spellings are the
/// extractor's (stage 1 of `5086736f8`, `TRUST_VANILLA_DEBUG=1`: `fn(u32, &u32) -> ..
/// {<u32 as core::ops::arith::Add<&u32>>::add}`, `{<&i32 as core::ops::arith::Neg>::neg}`,
/// `{<u32 as core::ops::bit::Shl<&u32>>::shl}`).
#[test]
fn integer_overflow_operators_by_reference_withhold_a_sysroot_item() {
    use super::numeric_panic::is_int_overflow_operator_callee as ovf_op;
    for callee in [
        "<u32 as core::ops::arith::Add<&u32>>::add",
        "<&u32 as core::ops::arith::Add<u32>>::add",
        "<&'a u64 as core::ops::arith::Sub<&'b u64>>::sub",
        "<u32 as core::ops::arith::Mul<&u32>>::mul",
        "<&i32 as core::ops::arith::Neg>::neg",
        "<u32 as core::ops::bit::Shl<&u32>>::shl",
        "<i64 as core::ops::bit::Shl<&u32>>::shl",
        "<&u8 as core::ops::bit::Shr<i64>>::shr",
        "<u32 as core::ops::arith::AddAssign<&u32>>::add_assign",
        "<i16 as core::ops::bit::ShlAssign<&u8>>::shl_assign",
        // the by-value spellings `is_numeric_value_panic_callee` already names
        "<i32 as core::ops::arith::Add>::add",
        "<u64 as core::ops::arith::Sub>::sub",
        // a signed `NonZero`'s negation behind a reference overflows at `MIN`
        "<&core::num::nonzero::NonZero<i32> as core::ops::arith::Neg>::neg",
    ] {
        assert!(ovf_op(callee), "{callee} must be an overflow-checked integer operator");
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    for callee in [
        // total operators: wrapping / saturating integers, floats, bitwise
        "<core::num::wrapping::Wrapping<u32> as core::ops::arith::Add>::add",
        "<&core::num::wrapping::Wrapping<u32> as core::ops::arith::Add<&core::num::wrapping::Wrapping<u32>>>::add",
        "<core::num::saturating::Saturating<i32> as core::ops::arith::Neg>::neg",
        "<f64 as core::ops::arith::Add<&f64>>::add",
        "<&f32 as core::ops::arith::Neg>::neg",
        "<u32 as core::ops::bit::BitAnd<&u32>>::bitand",
        "<&u32 as core::ops::bit::Not>::not",
    ] {
        assert!(!ovf_op(callee), "{callee} is total, not an overflow-checked operator");
        assert!(
            !super::callee_has_call_site_panic_family(callee),
            "`{callee}` must stay admissible"
        );
    }
    for callee in [
        // the division operators are `is_int_division_operator_callee`'s
        "<u32 as core::ops::arith::Div<&u32>>::div",
        // an unsigned `NonZero` has no `Neg`; a non-integer right-hand side
        "<&core::num::nonzero::NonZero<u32> as core::ops::arith::Neg>::neg",
        "<core::time::Duration as core::ops::arith::Add<&core::time::Duration>>::add",
        // a user type or trait that merely shares the names
        "<mycrate::Num as core::ops::arith::Add<&mycrate::Num>>::add",
        "<u32 as mycrate::ops::Add<&u32>>::add",
        "<&mycrate::NonZero<i32> as core::ops::arith::Neg>::neg",
        // a stamped impersonator of `core`
        "<u32 as __trust_crate@1973d11b2baa21fa::core::ops::arith::Add<&u32>>::add",
        "<&__trust_crate@1973d11b2baa21fa::core::num::nonzero::NonZero<i32> as core::ops::arith::Neg>::neg",
    ] {
        assert!(
            !ovf_op(callee),
            "{callee} must NOT be read as an overflow-checked integer operator"
        );
    }
}

/// Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): `range_self` reads the by-value
/// iterators of the stable `core::range` types as their `core::ops` families, so
/// `range_iter_can_panic` and `range_iter_row` charge them. The spellings are the
/// extractor's (`-Ztrust-dump=mir-only` on the stage 1 of `1213387e6d`:
/// `<core::range::iter::RangeFromIter<char> as core::iter::traits::iterator::Iterator>::next`).
/// Before the fix every new-range spelling answered `None`, so the iterators got no
/// Step or count row and the default policy accepted calls that panic.
#[test]
fn range_self_reads_the_new_range_iterators_as_their_families() {
    use super::numeric_panic::range_self;
    for (ty, family, elem) in [
        ("core::range::iter::RangeFromIter<char>", "RangeFrom", "char"),
        ("core::range::iter::RangeFromIter<u8>", "RangeFrom", "u8"),
        ("core::range::iter::RangeIter<u128>", "Range", "u128"),
        ("core::range::iter::RangeInclusiveIter<u64>", "RangeInclusive", "u64"),
        // the explicit reborrow `<&mut RangeFromIter<char> as Iterator>::next`
        ("&mut core::range::iter::RangeFromIter<char>", "RangeFrom", "char"),
        ("&'a mut core::range::iter::RangeIter<u64>", "Range", "u64"),
        // the legacy families, unchanged
        ("core::ops::range::RangeFrom<u8>", "RangeFrom", "u8"),
        ("core::ops::range::Range<u128>", "Range", "u128"),
        ("&mut core::ops::range::RangeInclusive<char>", "RangeInclusive", "char"),
    ] {
        assert_eq!(range_self(ty), Some((family, elem)), "{ty}");
    }
    for ty in [
        // a type-name token that only STARTS like one
        "core::range::iter::RangeFromIterX<u8>",
        "core::range::iter::RangeIterator<u8>",
        "core::ops::range::RangeFromX<u8>",
        // the `core::range` types themselves are `IntoIterator`, not `Iterator`
        "core::range::RangeFrom<char>",
        "core::range::Range<u8>",
        "core::range::RangeInclusive<u64>",
        // other `core::ops` ranges, and a missing type argument
        "core::ops::range::RangeTo<u8>",
        "core::range::iter::RangeFromIter",
        // a user crate's namesake, and a stamped impersonator of `core`
        "mycrate::range::iter::RangeFromIter<char>",
        "mycrate::core::range::iter::RangeFromIter<char>",
        "__trust_crate@1973d11b2baa21fa::core::range::iter::RangeFromIter<char>",
        "&mut __trust_crate@1973d11b2baa21fa::core::range::iter::RangeIter<u128>",
    ] {
        assert_eq!(range_self(ty), None, "{ty} must NOT be read as a range iterator");
    }
}

/// Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): the name-level view of the same fix.
/// Every advancing `RangeFromIter` call, and a `count` that can overflow some target's
/// `usize`, is in the family (so the fn item is withheld too); the lazy adaptors, a
/// `count` that is total at every pointer width, the `IntoIterator` conversion, user
/// namesakes and a stamped root are not.
#[test]
fn the_new_range_iterators_are_in_the_family() {
    const IT: &str = "core::iter::traits::iterator::Iterator";
    for callee in [
        format!("<core::range::iter::RangeFromIter<char> as {IT}>::next"),
        format!("<core::range::iter::RangeFromIter<u8> as {IT}>::next"),
        format!("<core::range::iter::RangeFromIter<char> as {IT}>::nth"),
        format!(
            "<core::range::iter::RangeFromIter<char> as {IT}>::find::<{{closure@nrp.rs:3:93: 3:97}}>"
        ),
        format!("<core::range::iter::RangeFromIter<char> as {IT}>::position::<F>"),
        format!("<core::range::iter::RangeFromIter<i32> as {IT}>::count"),
        format!("<&mut core::range::iter::RangeFromIter<char> as {IT}>::next"),
        format!("<core::range::iter::RangeInclusiveIter<u64> as {IT}>::count"),
        format!("<core::range::iter::RangeIter<u128> as {IT}>::count"),
    ] {
        assert!(is_numeric_value_panic_callee(&callee), "{callee} must be in the family");
    }
    for callee in [
        // lazy adaptors and `size_hint` advance nothing at their own call
        format!("<core::range::iter::RangeFromIter<char> as {IT}>::take"),
        format!("<core::range::iter::RangeFromIter<u8> as {IT}>::zip::<std::vec::IntoIter<u8>>"),
        format!("<core::range::iter::RangeFromIter<char> as {IT}>::size_hint"),
        // a bounded range's `next`/`nth` cannot overflow, and these counts are total at
        // every pointer width
        format!("<core::range::iter::RangeIter<u32> as {IT}>::next"),
        format!("<core::range::iter::RangeInclusiveIter<char> as {IT}>::nth"),
        format!("<core::range::iter::RangeIter<u16> as {IT}>::count"),
        format!("<core::range::iter::RangeInclusiveIter<u8> as {IT}>::count"),
        // the conversion into the iterator is total
        "<core::range::RangeFrom<char> as core::iter::traits::collect::IntoIterator>::into_iter"
            .to_string(),
        // look-alikes, user namesakes and a stamped impersonator
        format!("<core::range::iter::RangeFromIterX<u8> as {IT}>::next"),
        format!("<core::range::RangeFrom<char> as {IT}>::next"),
        format!("<mycrate::range::iter::RangeFromIter<char> as {IT}>::next"),
        "<core::range::iter::RangeFromIter<char> as mycrate::Iterator>::next".to_string(),
        format!(
            "<__trust_crate@1973d11b2baa21fa::core::range::iter::RangeFromIter<char> as {IT}>::next"
        ),
    ] {
        assert!(!is_numeric_value_panic_callee(&callee), "{callee} must NOT be in the family");
    }
}

/// Trust (NEW-RANGE-REMAINDER-UNCHARGED-1, wave-24 review, 2026-10-12): the nightly
/// inherent `RangeFromIter::<T>::remainder` steps an EXHAUSTED iterator with
/// `Step::forward(start, 1)` and panics past `MAX`; `remainder` is no `Iterator` method,
/// so NEW-RANGE-ITER-UNCHARGED-1's arm never saw it. The positive spellings are the
/// extractor's (`-Ztrust-dump=mir-only` on the stage 1 of `51eac007f3`); before the fix
/// each answered `false`. The other iterators' `remainder` (a move of the fields),
/// look-alikes, a user namesake, a non-`int`/`char` element and a stamped root do not
/// answer.
#[test]
fn range_from_iter_remainder_is_in_the_family() {
    for callee in [
        "core::range::iter::RangeFromIter::<char>::remainder",
        "core::range::iter::RangeFromIter::<u8>::remainder",
        "core::range::iter::RangeFromIter::<i128>::remainder",
        "core::range::iter::RangeFromIter::<usize>::remainder",
    ] {
        assert!(is_numeric_value_panic_callee(callee), "{callee} must be in the family");
    }
    for callee in [
        "core::range::iter::RangeIter::<u8>::remainder",
        "core::range::iter::RangeInclusiveIter::<char>::remainder",
        "core::range::iter::RangeFromIterX::<u8>::remainder",
        "core::range::iter::RangeFromIter::<u8>::remainder_of",
        "core::range::iter::RangeFromIter::<f64>::remainder",
        "core::range::iter::RangeFromIter::<mycrate::Pos>::remainder",
        "mycrate::range::iter::RangeFromIter::<char>::remainder",
        "__trust_crate@1973d11b2baa21fa::core::range::iter::RangeFromIter::<char>::remainder",
    ] {
        assert!(!is_numeric_value_panic_callee(callee), "{callee} must NOT be in the family");
    }
}

/// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): advancing an open `x..` range over a
/// NON-integer core `Step` type panics in `Step::forward` past its `MAX`, exactly as the
/// `int | char` twins do. The positive spellings are the extractor's (`-Ztrust-dump=mir`
/// on `scratchpad/stage1-w25f` of `scout26/openlies/step-confirm/stepl.rs` and
/// `more/more.rs`); before the fix every one answered `false` here (the `RangeFrom` arms
/// read `int | char` only, and `range_count_can_overflow` answered `false` for any other
/// element), so the call minted no row and a fn item was admitted. A user element, a
/// user namesake, a `NonZero` of a user type, a type parameter, a stamped impersonator
/// element, the lazy adaptors and the counts that are total at every pointer width are
/// not in the family.
#[test]
fn core_step_elem_ranges_are_in_the_family() {
    const IT: &str = "core::iter::traits::iterator::Iterator";
    for callee in [
        format!("<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::next"),
        format!(
            "<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::find::<{{closure@stepl.rs:8:64: 8:67}}>"
        ),
        format!("<core::ops::range::RangeFrom<core::num::nonzero::NonZero<u8>> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<core::net::ip_addr::Ipv6Addr> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<core::ascii::ascii_char::AsciiChar> as {IT}>::next"),
        format!("<core::range::iter::RangeFromIter<core::net::ip_addr::Ipv4Addr> as {IT}>::next"),
        format!(
            "<&mut core::ops::range::RangeFrom<core::num::nonzero::NonZero<usize>> as {IT}>::nth"
        ),
        format!("<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::count"),
        "core::range::iter::RangeFromIter::<core::net::ip_addr::Ipv4Addr>::remainder".to_string(),
        "core::range::iter::RangeFromIter::<core::num::nonzero::NonZero<u16>>::remainder"
            .to_string(),
        "core::range::iter::RangeFromIter::<core::ascii::ascii_char::AsciiChar>::remainder"
            .to_string(),
        // A count whose span can exceed some target's `usize`: `Ipv6Addr` (128 bits) on
        // 64, `Ipv4Addr` (32) inclusive on 32 and exclusive on 16.
        format!("<core::ops::range::Range<core::net::ip_addr::Ipv6Addr> as {IT}>::count"),
        format!(
            "<core::range::iter::RangeInclusiveIter<core::net::ip_addr::Ipv4Addr> as {IT}>::count"
        ),
        format!(
            "<core::ops::range::RangeInclusive<core::num::nonzero::NonZero<u64>> as {IT}>::count"
        ),
    ] {
        assert!(is_numeric_value_panic_callee(&callee), "{callee} must be in the family");
        assert!(
            super::callee_has_call_site_panic_family(&callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    for callee in [
        // a user element: its `Step` (nightly `step_trait`) may be the user's own
        format!("<core::ops::range::RangeFrom<mycrate::Pos> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<T> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<mycrate::net::Ipv4Addr> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<core::num::nonzero::NonZero<mycrate::W>> as {IT}>::next"),
        format!("<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4AddrX> as {IT}>::next"),
        // a stamped impersonator of `core` in the element
        format!(
            "<core::ops::range::RangeFrom<__trust_crate@1973d11b2baa21fa::core::net::ip_addr::Ipv4Addr> as {IT}>::next"
        ),
        "core::range::iter::RangeFromIter::<__trust_crate@1973d11b2baa21fa::core::net::ip_addr::Ipv4Addr>::remainder"
            .to_string(),
        "core::range::iter::RangeFromIter::<mycrate::net::Ipv4Addr>::remainder".to_string(),
        // lazy adaptors advance nothing at their own call
        format!("<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::take"),
        format!("<core::range::iter::RangeFromIter<core::net::ip_addr::Ipv6Addr> as {IT}>::size_hint"),
        // a bounded range's `next` cannot step past `MAX`, and these counts are total at
        // every pointer width
        format!("<core::ops::range::RangeInclusive<core::net::ip_addr::Ipv4Addr> as {IT}>::next"),
        format!("<core::ops::range::Range<core::ascii::ascii_char::AsciiChar> as {IT}>::count"),
        format!("<core::ops::range::RangeInclusive<core::num::nonzero::NonZero<u8>> as {IT}>::count"),
        format!("<core::ops::range::Range<mycrate::Pos> as {IT}>::count"),
    ] {
        assert!(!is_numeric_value_panic_callee(&callee), "{callee} must NOT be in the family");
    }
}

/// Trust (STEP-TRAIT-DIRECT-UNCHARGED-1, 2026-10-11): a direct `Step::forward` /
/// `Step::backward` (nightly `step_trait`) on one of core's own `Step` types panics on
/// the caller's value: `char::MAX`, `'\0'`, `u8::MAX`, `i32::MIN`, `NonZero::<u8>::MAX`,
/// `Ipv4Addr::BROADCAST`. The positive spellings are the extractor's
/// (`-Ztrust-dump=mir-only` on the stage 1 of `1213387e6d`); before the fix every one
/// answered `false` here and minted no row. The total siblings, a user trait named
/// `Step`, a user type's `Step` and a stamped trait or self type are not in the family.
#[test]
fn a_direct_step_forward_or_backward_is_in_the_family() {
    const STEP: &str = "core::iter::range::Step";
    for callee in [
        format!("<char as {STEP}>::forward"),
        format!("<char as {STEP}>::backward"),
        format!("<u8 as {STEP}>::forward"),
        format!("<u8 as {STEP}>::backward"),
        format!("<i32 as {STEP}>::backward"),
        format!("<usize as {STEP}>::forward"),
        format!("<i128 as {STEP}>::forward"),
        format!("<core::num::nonzero::NonZero<u8> as {STEP}>::forward"),
        format!("<core::ascii::ascii_char::AsciiChar as {STEP}>::forward"),
        format!("<core::net::ip_addr::Ipv4Addr as {STEP}>::forward"),
        format!("<core::net::ip_addr::Ipv6Addr as {STEP}>::backward"),
    ] {
        assert!(is_numeric_value_panic_callee(&callee), "{callee} must be in the family");
        assert!(
            super::callee_has_call_site_panic_family(&callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    for callee in [
        // the total siblings, and the `unsafe` ones the unsafe lane owns
        format!("<char as {STEP}>::forward_checked"),
        format!("<u8 as {STEP}>::backward_checked"),
        format!("<char as {STEP}>::steps_between"),
        format!("<u8 as {STEP}>::forward_unchecked"),
        format!("<char as {STEP}>::backward_unchecked"),
        // a user trait that merely shares the name, and a stamped impersonator trait
        "<char as mycrate::Step>::forward".to_string(),
        "<u8 as mycrate::iter::range::Step>::forward".to_string(),
        "<char as __trust_crate@1973d11b2baa21fa::core::iter::range::Step>::forward".to_string(),
        // a user type's or a type parameter's `Step` (it may be the user's own `forward`)
        format!("<gen::My as {STEP}>::forward"),
        format!("<T as {STEP}>::forward"),
        format!("<mycrate::net::Ipv4Addr as {STEP}>::forward"),
        format!("<core::num::nonzero::NonZero<mycrate::W> as {STEP}>::forward"),
        format!(
            "<__trust_crate@1973d11b2baa21fa::core::net::ip_addr::Ipv4Addr as {STEP}>::forward"
        ),
        // a reference is not a `Step` type
        format!("<&char as {STEP}>::forward"),
    ] {
        assert!(!is_numeric_value_panic_callee(&callee), "{callee} must NOT be in the family");
    }
}

/// Trust (wave 23, STAMPED-CORE-MINT-1 residual, 2026-10-11): a STAMPED GENUINE core
/// keeps the numeric family's call-site rows.
///
/// The extractor stamps the real core's paths whenever a second crate named `core` is
/// in the graph, or under `-Zbuild-std`, and it puts the stamp in front of the WHOLE
/// rendered path: `__trust_crate@414739228a72f04f::core::num::<impl u32>::ilog2`, and
/// `__trust_crate@414739228a72f04f::<i32 as core::cmp::Ord>::clamp` for the qualified
/// spelling (read off `-Ztrust-dump=mir-only` on the stage 1 of `5911b1325f`). Every
/// recognizer behind `numeric_value_panic_row` and `numeric_overflow_call` refused the
/// stamp, so in such a graph these calls minted no row, the default policy accepted
/// them on a `runtime_checked` row, and a verify-on binary panicked on the caller's
/// value (measured on that stage 1). Both functions now read past ONE well-formed
/// leading stamp and re-authenticate the rest. Each positive below asserts that the
/// stamped spelling mints EXACTLY the row the unstamped one mints. Before the fix
/// every stamped spelling answered `None`.
mod stamped_genuine_core {
    use trust_types::{
        BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    };

    use super::super::numeric_panic::{
        NumericOverflow, int_inherent, is_numeric_value_panic_callee, numeric_overflow_call,
        numeric_value_panic_row,
    };

    /// The stable crate id the extractor stamped the genuine core with in the measured
    /// graph (`stamped_genuine_core/*.json`).
    const STAMP: &str = "__trust_crate@414739228a72f04f::";
    /// A second, well-formed stamp (a different crate).
    const OTHER: &str = "__trust_crate@1973d11b2baa21fa::";

    fn u32_() -> Ty {
        Ty::Int { width: 32, signed: false }
    }
    fn i32_() -> Ty {
        Ty::Int { width: 32, signed: true }
    }
    fn u64_() -> Ty {
        Ty::Int { width: 64, signed: false }
    }
    fn i64_() -> Ty {
        Ty::Int { width: 64, signed: true }
    }
    fn f64_() -> Ty {
        Ty::Float { width: 64 }
    }
    fn mut_ref(inner: Ty) -> Ty {
        Ty::Ref { mutable: true, inner: Box::new(inner) }
    }
    fn str_ref() -> Ty {
        Ty::Ref { mutable: false, inner: Box::new(Ty::Str) }
    }

    /// `fn f(_1: params[0], ..) -> ret { callee(_1, ..) }`, `_0` the destination.
    fn call_fn(callee: &str, params: &[Ty], ret: Ty) -> VerifiableFunction {
        let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
        for (i, t) in params.iter().enumerate() {
            locals.push(LocalDecl { index: i + 1, ty: t.clone(), name: Some(format!("p{i}")) });
        }
        let args = (1..=params.len()).map(|i| Operand::Copy(Place::local(i))).collect();
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "stamped::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            func: callee.to_string(),
                            args,
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            callee_key: None,
                            is_foreign: false,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: params.len(),
                return_ty: ret,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn call_of(f: &VerifiableFunction) -> (&str, &[Operand], &Place) {
        match &f.body.blocks[0].terminator {
            Terminator::Call { func, args, dest, .. } => (func.as_str(), args.as_slice(), dest),
            other => panic!("the fixture makes a call, got {other:?}"),
        }
    }

    fn value_row(callee: &str, params: &[Ty], ret: Ty) -> Option<(Formula, VcKind)> {
        let f = call_fn(callee, params, ret);
        let (callee, args, dest) = call_of(&f);
        numeric_value_panic_row(&f, callee, args, dest)
    }

    /// The overflow lane's answer, rendered so two answers can be compared.
    fn overflow(callee: &str, params: &[Ty], ret: Ty) -> Option<String> {
        let f = call_fn(callee, params, ret);
        let (callee, args, _) = call_of(&f);
        numeric_overflow_call(&f, callee, args).map(|o| match o {
            NumericOverflow::BinOp(op) => format!("BinOp({op:?})"),
            NumericOverflow::AssignBinOp { op, lhs } => format!("AssignBinOp({op:?}, {lhs:?})"),
            NumericOverflow::Pow => "Pow".to_string(),
        })
    }

    /// The value-panic arms: the int inherent owner (ilog*, next_power_of_two,
    /// strict_neg, strict_shl, the signed `div_euclid`), the qualified trait spellings
    /// (`Ord::clamp`, `Neg::neg`, `Shl::shl`, `ShlAssign::shl_assign`,
    /// `CheckedCastFromInt::strict_cast_from`), and the float, char, `NonZero` and
    /// `Duration` owners.
    #[test]
    fn a_stamped_genuine_core_mints_every_value_panic_row_it_mints_unstamped() {
        let cases: Vec<(&str, Vec<Ty>, Ty)> = vec![
            ("core::num::<impl u32>::ilog2", vec![u32_()], u32_()),
            ("core::num::<impl i32>::ilog10", vec![i32_()], u32_()),
            ("core::num::<impl u32>::ilog", vec![u32_(), u32_()], u32_()),
            ("core::num::<impl u32>::next_power_of_two", vec![u32_()], u32_()),
            ("std::num::<impl u32>::next_power_of_two", vec![u32_()], u32_()),
            ("core::num::<impl i32>::strict_neg", vec![i32_()], i32_()),
            ("core::num::<impl u32>::strict_shl", vec![u32_(), u32_()], u32_()),
            ("core::num::<impl i32>::div_euclid", vec![i32_(), i32_()], i32_()),
            ("<i32 as core::cmp::Ord>::clamp", vec![i32_(), i32_(), i32_()], i32_()),
            ("<i32 as core::ops::arith::Neg>::neg", vec![i32_()], i32_()),
            ("<u32 as core::ops::bit::Shl>::shl", vec![u32_(), u32_()], u32_()),
            (
                "<u32 as core::ops::bit::ShlAssign>::shl_assign",
                vec![mut_ref(u32_()), u32_()],
                Ty::Unit,
            ),
            (
                "<u8 as core::convert::num::CheckedCastFromInt<u32>>::strict_cast_from",
                vec![u32_()],
                Ty::Int { width: 8, signed: false },
            ),
            ("core::f64::<impl f64>::clamp", vec![f64_(), f64_(), f64_()], f64_()),
            ("core::char::methods::<impl char>::to_digit", vec![Ty::Char, u32_()], u32_()),
            ("core::num::nonzero::NonZero::<u32>::from_str_radix", vec![str_ref(), u32_()], u32_()),
            ("core::time::Duration::new", vec![u64_(), u32_()], Ty::Unit),
            ("core::time::Duration::from_mins", vec![u64_()], Ty::Unit),
        ];
        for (rest, params, ret) in cases {
            let plain = value_row(rest, &params, ret.clone());
            assert!(plain.is_some(), "control: unstamped `{rest}` mints a row");
            let stamped = format!("{STAMP}{rest}");
            assert_eq!(
                value_row(&stamped, &params, ret),
                plain,
                "`{stamped}` is the genuine core in a graph that stamps it, and must mint \
                 exactly the unstamped row"
            );
        }
    }

    /// The overflow-call lane: `strict_add`/`strict_sub`/`strict_mul`, `strict_pow`,
    /// the by-value `Add::add` and the compound-assign `AddAssign::add_assign`.
    #[test]
    fn a_stamped_genuine_core_mints_every_overflow_call_row_it_mints_unstamped() {
        let cases: Vec<(&str, Vec<Ty>, Ty, &str)> = vec![
            ("core::num::<impl u32>::strict_add", vec![u32_(), u32_()], u32_(), "BinOp(Add)"),
            ("core::num::<impl i64>::strict_sub", vec![i64_(), i64_()], i64_(), "BinOp(Sub)"),
            ("std::num::<impl u32>::strict_mul", vec![u32_(), u32_()], u32_(), "BinOp(Mul)"),
            ("core::num::<impl u32>::strict_pow", vec![u32_(), u32_()], u32_(), "Pow"),
            ("<u32 as core::ops::arith::Add>::add", vec![u32_(), u32_()], u32_(), "BinOp(Add)"),
            (
                "<i32 as core::ops::arith::AddAssign>::add_assign",
                vec![mut_ref(i32_()), i32_()],
                Ty::Unit,
                "AssignBinOp(Add",
            ),
        ];
        for (rest, params, ret, want) in cases {
            let plain = overflow(rest, &params, ret.clone());
            assert!(
                plain.as_deref().is_some_and(|p| p.starts_with(want)),
                "control: unstamped `{rest}` is the overflow lane's {want}, got {plain:?}"
            );
            let stamped = format!("{STAMP}{rest}");
            assert_eq!(
                overflow(&stamped, &params, ret),
                plain,
                "`{stamped}` is the genuine core in a graph that stamps it, and must take \
                 exactly the unstamped overflow row"
            );
        }
    }

    /// Only ONE well-formed stamp at the FRONT is read past, and the rest must still be
    /// the exact sysroot spelling the arm authenticates.
    #[test]
    fn only_one_well_formed_leading_stamp_is_read_past() {
        let value: Vec<(String, Vec<Ty>, Ty)> = vec![
            // two stamps
            (format!("{STAMP}{OTHER}core::num::<impl u32>::ilog2"), vec![u32_()], u32_()),
            (
                format!("{STAMP}{OTHER}<i32 as core::cmp::Ord>::clamp"),
                vec![i32_(), i32_(), i32_()],
                i32_(),
            ),
            // a stamp inside the trait half, with or without one in front
            (
                "<i32 as __trust_crate@414739228a72f04f::core::cmp::Ord>::clamp".to_string(),
                vec![i32_(), i32_(), i32_()],
                i32_(),
            ),
            (
                format!("{STAMP}<i32 as {OTHER}core::cmp::Ord>::clamp"),
                vec![i32_(), i32_(), i32_()],
                i32_(),
            ),
            // a malformed stamp: not 16 hex digits, or empty
            (
                "__trust_crate@414739228a72f04::core::num::<impl u32>::ilog2".to_string(),
                vec![u32_()],
                u32_(),
            ),
            (
                "__trust_crate@zz4739228a72f04f::core::num::<impl u32>::ilog2".to_string(),
                vec![u32_()],
                u32_(),
            ),
            ("__trust_crate@::core::num::<impl u32>::ilog2".to_string(), vec![u32_()], u32_()),
            // a stamp that is not at the front
            (
                "core::num::<impl u32>::__trust_crate@414739228a72f04f::ilog2".to_string(),
                vec![u32_()],
                u32_(),
            ),
            // a stamped USER path, owner or trait
            (format!("{STAMP}mycrate::num::<impl u32>::ilog2"), vec![u32_()], u32_()),
            (
                format!("{STAMP}<i32 as mycrate::cmp::Ord>::clamp"),
                vec![i32_(), i32_(), i32_()],
                i32_(),
            ),
            (format!("{STAMP}mycrate::time::Duration::new"), vec![u64_(), u32_()], Ty::Unit),
            // a stamped TOTAL sibling: the owner is core's, the method cannot panic
            (format!("{STAMP}core::num::<impl u32>::checked_ilog2"), vec![u32_()], u32_()),
            (format!("{STAMP}<u32 as core::cmp::Ord>::max"), vec![u32_(), u32_()], u32_()),
        ];
        for (callee, params, ret) in value {
            assert_eq!(value_row(&callee, &params, ret), None, "`{callee}` must mint no row");
        }
        let ovf: Vec<String> = vec![
            format!("{STAMP}{OTHER}core::num::<impl u32>::strict_add"),
            "__trust_crate@414739228a72f04::core::num::<impl u32>::strict_add".to_string(),
            format!("{STAMP}mycrate::num::<impl u32>::strict_add"),
            format!("{STAMP}<u32 as mycrate::ops::Add>::add"),
            format!("<u32 as {OTHER}core::ops::arith::Add>::add"),
            format!("{STAMP}core::num::<impl u32>::checked_add"),
        ];
        for callee in ovf {
            assert_eq!(
                overflow(&callee, &[u32_(), u32_()], u32_()),
                None,
                "`{callee}` must take no overflow row"
            );
        }
    }

    /// The row `numeric_value_panic_row` mints for each `(callee, params, ret)` case must be
    /// the fail-closed row of kind `want`, and the SAME row behind ONE leading extractor
    /// stamp of the genuine core.
    fn assert_fail_closed_rows(cases: Vec<(String, Vec<Ty>, Ty, &str)>) {
        for (callee, params, ret, want) in cases {
            let row = value_row(&callee, &params, ret.clone());
            assert!(
                matches!(&row, Some((_, VcKind::UnsupportedMir { kind, .. })) if kind == want),
                "`{callee}` must mint the fail-closed `{want}` row, got {row:?}"
            );
            let stamped = format!("{STAMP}{callee}");
            assert_eq!(
                value_row(&stamped, &params, ret),
                row,
                "`{stamped}` is the genuine core in a graph that stamps it, and must mint \
                 exactly the unstamped row"
            );
        }
    }

    fn usize_() -> Ty {
        Ty::Int { width: 64, signed: false }
    }

    /// Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): the ROWS the fix mints at a call. An
    /// advancing `RangeFromIter` call takes `range-from-step-overflow-unmodeled`; a
    /// `RangeInclusiveIter<u64>`/`RangeIter<u128>` `count` whose receiver is not a traced
    /// `a..=b`/`a..b` takes `range-count-overflow-unmodeled`. Each is the same behind one
    /// leading stamp of the genuine core. Before the fix every call here minted no row
    /// (`None`). The non-advancing and total siblings still mint none.
    #[test]
    fn the_new_range_iterators_mint_fail_closed_rows() {
        const IT: &str = "core::iter::traits::iterator::Iterator";
        assert_fail_closed_rows(vec![
            (
                format!("<core::range::iter::RangeFromIter<char> as {IT}>::next"),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!("<&mut core::range::iter::RangeFromIter<u8> as {IT}>::nth"),
                vec![mut_ref(Ty::Unit), usize_()],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!("<core::range::iter::RangeInclusiveIter<u64> as {IT}>::count"),
                vec![Ty::Unit],
                usize_(),
                "range-count-overflow-unmodeled",
            ),
            (
                format!("<core::range::iter::RangeIter<u128> as {IT}>::count"),
                vec![Ty::Unit],
                usize_(),
                "range-count-overflow-unmodeled",
            ),
        ]);
        let none: Vec<(String, Vec<Ty>, Ty)> = vec![
            (
                format!("<core::range::iter::RangeFromIter<char> as {IT}>::take"),
                vec![Ty::Unit, usize_()],
                Ty::Unit,
            ),
            (
                format!("<core::range::iter::RangeIter<u32> as {IT}>::next"),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
            // `RangeInclusiveIter<u32>::count` cannot overflow a 64-bit `usize`
            (
                format!("<core::range::iter::RangeInclusiveIter<u32> as {IT}>::count"),
                vec![Ty::Unit],
                usize_(),
            ),
            (
                format!("<core::range::RangeFrom<char> as {IT}>::next"),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
            (
                format!("{STAMP}{OTHER}<core::range::iter::RangeFromIter<char> as {IT}>::next"),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
        ];
        for (callee, params, ret) in none {
            assert_eq!(value_row(&callee, &params, ret), None, "`{callee}` must mint no row");
        }
    }

    /// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): the ROWS a range over a NON-integer core
    /// `Step` type mints at a call. An advancing `RangeFrom` / `RangeFromIter` call, and the
    /// nightly `RangeFromIter::remainder`, take `range-from-step-overflow-unmodeled`; a
    /// `Range<Ipv6Addr>` count on a 64-bit target, and a `RangeInclusive<Ipv4Addr>` count on
    /// a 32-bit one, take `range-count-overflow-unmodeled` with the generic message (it
    /// named `char` only). Each is the same behind one leading stamp of the genuine core.
    /// Before the fix every call here minted no row (`None`). The non-advancing, bounded
    /// and total siblings, a user element and a stamped element still mint none.
    #[test]
    fn core_step_elem_ranges_mint_fail_closed_rows() {
        const IT: &str = "core::iter::traits::iterator::Iterator";
        let usize32 = || Ty::Int { width: 32, signed: false };
        assert_fail_closed_rows(vec![
            (
                format!(
                    "<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::find::<{{closure@stepl.rs:8:64: 8:67}}>"
                ),
                vec![mut_ref(Ty::Unit), Ty::Unit],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::ops::range::RangeFrom<core::num::nonzero::NonZero<u8>> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::ops::range::RangeFrom<core::net::ip_addr::Ipv6Addr> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::ops::range::RangeFrom<core::ascii::ascii_char::AsciiChar> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::range::iter::RangeFromIter<core::net::ip_addr::Ipv4Addr> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                "core::range::iter::RangeFromIter::<core::net::ip_addr::Ipv4Addr>::remainder"
                    .to_string(),
                vec![Ty::Unit],
                Ty::Unit,
                "range-from-step-overflow-unmodeled",
            ),
            (
                format!("<core::ops::range::Range<core::net::ip_addr::Ipv6Addr> as {IT}>::count"),
                vec![Ty::Unit],
                usize_(),
                "range-count-overflow-unmodeled",
            ),
            (
                format!(
                    "<core::ops::range::RangeInclusive<core::net::ip_addr::Ipv4Addr> as {IT}>::count"
                ),
                vec![Ty::Unit],
                usize32(),
                "range-count-overflow-unmodeled",
            ),
        ]);
        // The count row's message is the generic one, not the old `char`-only text.
        let row = value_row(
            &format!("<core::ops::range::Range<core::net::ip_addr::Ipv6Addr> as {IT}>::count"),
            &[Ty::Unit],
            usize_(),
        );
        assert!(
            matches!(&row, Some((_, VcKind::UnsupportedMir { detail, .. }))
                if detail.contains("non-integer core `Step` type")),
            "the count row names the element class, not `char`: {row:?}"
        );
        let none: Vec<(String, Vec<Ty>, Ty)> = vec![
            (
                format!(
                    "<core::ops::range::RangeFrom<core::net::ip_addr::Ipv4Addr> as {IT}>::take"
                ),
                vec![Ty::Unit, usize_()],
                Ty::Unit,
            ),
            (
                format!(
                    "<core::ops::range::RangeInclusive<core::net::ip_addr::Ipv4Addr> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
            // `Range<Ipv4Addr>::count` and `RangeInclusive<NonZero<u32>>::count` cannot
            // overflow a 64-bit `usize`
            (
                format!("<core::ops::range::Range<core::net::ip_addr::Ipv4Addr> as {IT}>::count"),
                vec![Ty::Unit],
                usize_(),
            ),
            (
                format!(
                    "<core::ops::range::RangeInclusive<core::num::nonzero::NonZero<u32>> as {IT}>::count"
                ),
                vec![Ty::Unit],
                usize_(),
            ),
            (
                format!("<core::ops::range::RangeFrom<mycrate::Pos> as {IT}>::next"),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
            (
                format!(
                    "<core::ops::range::RangeFrom<{OTHER}core::net::ip_addr::Ipv4Addr> as {IT}>::next"
                ),
                vec![mut_ref(Ty::Unit)],
                Ty::Unit,
            ),
        ];
        for (callee, params, ret) in none {
            assert_eq!(value_row(&callee, &params, ret), None, "`{callee}` must mint no row");
        }
    }

    /// Trust (STEP-TRAIT-DIRECT-UNCHARGED-1, 2026-10-11): the ROW a direct `Step::forward`
    /// / `Step::backward` mints: `step-forward-overflow-unmodeled` /
    /// `step-backward-overflow-unmodeled`, the same behind one leading stamp of the genuine
    /// core. Before the fix every call here minted no row (`None`). The total siblings, a
    /// user trait and a second stamp still mint none.
    #[test]
    fn a_direct_step_call_mints_its_fail_closed_row() {
        const STEP: &str = "core::iter::range::Step";
        let u8_ = || Ty::Int { width: 8, signed: false };
        assert_fail_closed_rows(vec![
            (
                format!("<char as {STEP}>::forward"),
                vec![Ty::Char, usize_()],
                Ty::Char,
                "step-forward-overflow-unmodeled",
            ),
            (
                format!("<char as {STEP}>::backward"),
                vec![Ty::Char, usize_()],
                Ty::Char,
                "step-backward-overflow-unmodeled",
            ),
            (
                format!("<u8 as {STEP}>::forward"),
                vec![u8_(), usize_()],
                u8_(),
                "step-forward-overflow-unmodeled",
            ),
            (
                format!("<i32 as {STEP}>::backward"),
                vec![i32_(), usize_()],
                i32_(),
                "step-backward-overflow-unmodeled",
            ),
            (
                format!("<core::net::ip_addr::Ipv4Addr as {STEP}>::forward"),
                vec![Ty::Unit, usize_()],
                Ty::Unit,
                "step-forward-overflow-unmodeled",
            ),
        ]);
        let none: Vec<(String, Vec<Ty>, Ty)> = vec![
            (format!("<char as {STEP}>::forward_checked"), vec![Ty::Char, usize_()], Ty::Unit),
            (format!("<u8 as {STEP}>::backward_checked"), vec![u8_(), usize_()], Ty::Unit),
            (format!("<char as {STEP}>::steps_between"), vec![Ty::Unit, Ty::Unit], Ty::Unit),
            ("<char as mycrate::Step>::forward".to_string(), vec![Ty::Char, usize_()], Ty::Char),
            (format!("<gen::My as {STEP}>::forward"), vec![Ty::Unit, usize_()], Ty::Unit),
            (
                format!("{STAMP}{OTHER}<char as {STEP}>::forward"),
                vec![Ty::Char, usize_()],
                Ty::Char,
            ),
        ];
        for (callee, params, ret) in none {
            assert_eq!(value_row(&callee, &params, ret), None, "`{callee}` must mint no row");
        }
    }

    /// What the fix leaves alone: `int_inherent` still refuses a stamp, because the
    /// ROTATE-ITEM-NAME-1 grant in `callee_has_call_site_panic_family` (the vanilla
    /// admission of core's TOTAL `rotate_left` handed over as an item) is anchored on
    /// it; and the name-only `is_numeric_value_panic_callee` still answers `false` for a
    /// stamped spelling (a `true` there only withholds an item's admission).
    #[test]
    fn the_rotate_grant_and_the_name_only_view_still_refuse_a_stamp() {
        let rotate = "core::num::<impl u32>::rotate_left";
        assert!(int_inherent(rotate).is_some());
        assert!(
            !super::super::callee_has_call_site_panic_family(rotate),
            "core's total rotate is admitted"
        );
        let stamped_rotate = format!("{STAMP}{rotate}");
        assert!(
            int_inherent(&stamped_rotate).is_none(),
            "`int_inherent` must keep refusing a stamp"
        );
        assert!(
            super::super::callee_has_call_site_panic_family(&stamped_rotate),
            "a stamped `rotate_left` is not admitted by the rotate grant"
        );
        for rest in ["core::num::<impl u32>::ilog2", "<i32 as core::cmp::Ord>::clamp"] {
            let stamped = format!("{STAMP}{rest}");
            assert!(
                !is_numeric_value_panic_callee(&stamped),
                "`{stamped}`: name-only view unchanged"
            );
        }
    }
}
