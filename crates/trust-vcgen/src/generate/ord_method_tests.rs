use super::{
    is_bool_from_call, is_std_int_from_into_call, is_std_num_intrinsic, ord_method,
    std_lossless_scalar_conversion,
};

#[test]
fn matches_std_ord_min_max_clamp() {
    // The spellings safe_def_path_str produces for `n.min(3)` etc.
    assert_eq!(ord_method("std::cmp::Ord::min"), Some("min"));
    assert_eq!(ord_method("core::cmp::Ord::max"), Some("max"));
    assert_eq!(ord_method("std::cmp::Ord::clamp"), Some("clamp"));
    // The qualified spelling the producer emits names the trait by its full path;
    // the bare `<usize as Ord>::min` this row used to accept is a trait the
    // producer never renders for std (`a_user_trait_named_ord_is_declined`).
    assert_eq!(ord_method("<usize as core::cmp::Ord>::min"), Some("min"));
    assert_eq!(ord_method("core::cmp::min"), Some("min"));
}

#[test]
fn rejects_comparator_variants_unsound_to_bound() {
    // min_by / min_by_key take a comparator; `result <= a` does NOT hold.
    assert_eq!(ord_method("std::cmp::Ord::min_by"), None);
    assert_eq!(ord_method("core::cmp::min_by_key"), None);
    // `Iterator::min` returns the min ELEMENT (Option<&T>), not a 2-arg
    // Ord::min — outside `cmp`/`Ord`, so (correctly) not bounded.
    assert_eq!(ord_method("std::iter::Iterator::min"), None);
}

#[test]
fn rejects_user_min_outside_std_cmp() {
    // A user `mymod::min` is NOT the ordered min — must not be bounded.
    assert_eq!(ord_method("mycrate::mymod::min"), None);
    assert_eq!(ord_method("widget::clamp"), None);
    assert_eq!(ord_method("mycrate::core::cmp::min"), None);
}

#[test]
fn value_fact_callees_require_std_origin() {
    // NUM-METHOD-ANCHOR-1 (2026-10-04): a real-sysroot key plus an exact path.
    let core_key = trust_types::CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1234,
        krate_name: "core".into(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    };
    let core = Some(&core_key);
    assert!(is_bool_from_call("core::convert::From::from", core));
    assert!(is_bool_from_call("<usize as core::convert::From<bool>>::from", core));
    // The unqualified trait is not a spelling the extractor renders for std.
    assert!(!is_bool_from_call("<usize as From<bool>>::from", core));
    assert!(!is_bool_from_call("mycrate::convert::From::from", core));
    assert!(!is_bool_from_call("mycrate::core::convert::Into::into", core));
    assert!(!is_bool_from_call("<usize as mycrate::convert::From<bool>>::from", core));
    assert!(!is_bool_from_call("<usize as core::convert::From<bool>>::from", None));

    assert!(is_std_num_intrinsic("core::num::<impl u32>::count_ones"));
    assert!(!is_std_num_intrinsic("mycrate::core::num::count_ones"));
}

/// Trust (2026-09-24, TRUST-09): the lossless primitive-integer `From`/`Into`
/// recognizer matches the extractor's exact impl spellings and nothing a user
/// crate or a generic argument can spell.
#[test]
fn int_from_into_matches_only_the_std_primitive_conversions() {
    // The spellings measured on stage1 `5242fb1fe` for `usize::from(b)`,
    // `i64::from(x)` and `b.into()`.
    assert!(is_std_int_from_into_call("<usize as core::convert::From<u8>>::from"));
    assert!(is_std_int_from_into_call("<i64 as core::convert::From<i8>>::from"));
    assert!(is_std_int_from_into_call("<u8 as core::convert::Into<usize>>::into"));
    assert!(is_std_int_from_into_call("<u32 as std::convert::From<u16>>::from"));
    // Not a primitive integer on one side.
    assert!(!is_std_int_from_into_call("<usize as core::convert::From<bool>>::from"));
    assert!(!is_std_int_from_into_call("<u32 as core::convert::From<char>>::from"));
    assert!(!is_std_int_from_into_call("<p::Wrapper as core::convert::From<u8>>::from"));
    assert!(!is_std_int_from_into_call("<usize as core::convert::From<p::U8>>::from"));
    // Not the std trait, or not its method.
    assert!(!is_std_int_from_into_call("<usize as mycrate::convert::From<u8>>::from"));
    assert!(!is_std_int_from_into_call("<usize as From<u8>>::from"));
    assert!(!is_std_int_from_into_call("<usize as core::convert::TryFrom<u64>>::try_from"));
    assert!(!is_std_int_from_into_call("<usize as core::convert::From<u8>>::from_other"));
    assert!(!is_std_int_from_into_call("<u8 as core::convert::Into<usize>>::from"));
    // A generic argument cannot supply the shape.
    assert!(!is_std_int_from_into_call("p::f::<<usize as core::convert::From<u8>>::from>"));
    assert!(!is_std_int_from_into_call("core::convert::From::from"));
}

/// Trust (2026-10-03, cap from-range): the source-range recognizer admits exactly
/// the closed table of `core::convert::num` / `core::char::convert` lossless
/// impls, in both spellings, and nothing a user crate or the lossy direction can
/// spell.
#[test]
fn lossless_scalar_conversion_is_the_closed_std_table() {
    assert_eq!(
        std_lossless_scalar_conversion("<u64 as core::convert::From<u32>>::from"),
        Some(("u32", "u64"))
    );
    assert_eq!(
        std_lossless_scalar_conversion("<usize as core::convert::From<u16>>::from"),
        Some(("u16", "usize"))
    );
    assert_eq!(
        std_lossless_scalar_conversion("<u16 as core::convert::Into<u32>>::into"),
        Some(("u16", "u32"))
    );
    assert_eq!(
        std_lossless_scalar_conversion("<usize as core::convert::From<bool>>::from"),
        Some(("bool", "usize"))
    );
    assert_eq!(
        std_lossless_scalar_conversion("<u32 as std::convert::From<char>>::from"),
        Some(("char", "u32"))
    );
    assert_eq!(
        std_lossless_scalar_conversion("<i64 as core::convert::From<u32>>::from"),
        Some(("u32", "i64"))
    );
    // Not in std: lossy, same-width signedness change, or not an integer destination.
    for callee in [
        "<u32 as core::convert::From<u64>>::from",
        "<u32 as core::convert::From<i32>>::from",
        "<i32 as core::convert::From<u32>>::from",
        "<usize as core::convert::From<u32>>::from",
        "<u64 as core::convert::From<usize>>::from",
        "<u16 as core::convert::From<char>>::from",
        "<char as core::convert::From<u8>>::from",
        "<u32 as core::convert::From<u32>>::from",
        "<f64 as core::convert::From<u32>>::from",
    ] {
        assert_eq!(std_lossless_scalar_conversion(callee), None, "{callee}");
    }
    // Not the std trait, not its method, or not the impl spelling.
    for callee in [
        "<u64 as mycrate::convert::From<u32>>::from",
        "<u64 as From<u32>>::from",
        "<u64 as core::convert::TryFrom<u32>>::try_from",
        "<u64 as core::convert::From<u32>>::from_other",
        "<u32 as core::convert::Into<u64>>::from",
        "core::convert::From::from",
        "p::f::<<u64 as core::convert::From<u32>>::from>",
    ] {
        assert_eq!(std_lossless_scalar_conversion(callee), None, "{callee}");
    }
}

/// Trust (2026-10-03, NAME-ANCHOR-1): a trait NAMED `Ord` is not `core::cmp::Ord`.
///
/// The producer renders std's trait untrimmed and crate-qualified
/// (`<u32 as core::cmp::Ord>::min`), so a bare `as Ord>::` names some other trait,
/// and a user trait called `Ord` renders under its own crate. The anchor is the
/// qualifier's OWN trait half, so a substring sitting inside a generic argument
/// of a user callee cannot supply it either.
#[test]
fn a_user_trait_named_ord_is_declined() {
    for callee in [
        "<u32 as Ord>::min",
        "<usize as Ord>::max",
        "<u32 as spoof::Ord>::min",
        "<u32 as minbug2::spoof::Ord>::clamp",
        "<u32 as spoof::core::cmp::Ord>::min",
        "<spoof::W<<u32 as core::cmp::Ord>::X> as spoof::T>::min",
        "spoof::W::<<u32 as core::cmp::Ord>::X>::min",
        "spoof::core::cmp::min",
        "minbug2::util::min",
    ] {
        assert_eq!(ord_method(callee), None, "`{callee}` is not std's `Ord`/`cmp`");
    }
}

#[test]
fn std_ord_spellings_stay_recognized() {
    assert_eq!(ord_method("<usize as core::cmp::Ord>::min"), Some("min"));
    assert_eq!(ord_method("<i64 as std::cmp::Ord>::max"), Some("max"));
    assert_eq!(ord_method("<char as core::cmp::Ord>::clamp"), Some("clamp"));
    assert_eq!(ord_method("core::cmp::Ord::min"), Some("min"));
    assert_eq!(ord_method("core::cmp::min"), Some("min"));
    assert_eq!(ord_method("std::cmp::max"), Some("max"));
}
