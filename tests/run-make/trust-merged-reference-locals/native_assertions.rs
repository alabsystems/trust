fn main() {
    for flag in [false, true] {
        assert_eq!(bool_from_u8(flag), u8::from(flag));
        assert_eq!(bool_from_u16(flag), u16::from(flag));
        assert_eq!(bool_from_u32(flag), u32::from(flag));
        assert_eq!(bool_from_u64(flag), u64::from(flag));
        assert_eq!(bool_from_u128(flag), u128::from(flag));
        assert_eq!(bool_from_usize(flag), usize::from(flag));
        assert_eq!(bool_from_i8(flag), i8::from(flag));
        assert_eq!(bool_from_i16(flag), i16::from(flag));
        assert_eq!(bool_from_i32(flag), i32::from(flag));
        assert_eq!(bool_from_i64(flag), i64::from(flag));
        assert_eq!(bool_from_i128(flag), i128::from(flag));
        assert_eq!(bool_from_isize(flag), isize::from(flag));
        assert_eq!(bool_from_argument_effect(flag), 7 + u32::from(flag));
        assert_eq!(bool_from_callee_effect(flag), 11 + u32::from(flag));
        assert_eq!(bool_from_ordered_effects(flag), 120 + u32::from(flag));
        assert_eq!(from(flag), if flag { 7 } else { 9 });
        assert_eq!(named_from_control(flag), if flag { 7 } else { 9 });
        assert_eq!(dead_fresh(flag), u32::from(flag));
        assert_eq!(dead_changed(flag), 7);
        assert_eq!(dead_read_before(flag), 1);
        assert_eq!(dead_forwarded(flag), 7);
        assert_eq!(raw_live_read(flag), if flag { 2 } else { 1 });
        let expected = if flag { 112 } else { 1102 };
        assert_eq!(assigned_if(flag), expected, "assigned_if");
        assert_eq!(assigned_bool_match(flag), expected, "assigned_bool_match");
        assert_eq!(assigned_int_match(flag), expected, "assigned_int_match");
        assert_eq!(assigned_str_match(flag), expected, "assigned_str_match");
        assert_eq!(assigned_float_match(flag), expected, "assigned_float_match");
        assert_eq!(assigned_enum_match(flag), expected, "assigned_enum_match");
        assert_eq!(assigned_and(flag), expected, "assigned_and");
        assert_eq!(assigned_or(flag), expected, "assigned_or");
        assert_eq!(assigned_if_let(flag), expected, "assigned_if_let");
        assert_eq!(assigned_fresh(flag), expected, "assigned_fresh");
        assert_eq!(
            assigned_integer_tuple(flag),
            expected,
            "assigned_integer_tuple"
        );
        assert_eq!(assigned_shadow(flag), expected, "assigned_shadow");
        assert_eq!(assigned_destructure(flag), expected, "assigned_destructure");
        assert_eq!(assigned_nested(flag), expected, "assigned_nested");
        assert_eq!(returned_mut_value(flag), expected, "returned_mut_value");
        assert_eq!(shared_fresh(flag), if flag { 2 } else { 1 });
        assert_eq!(shared_from_mut(flag), if flag { 2 } else { 1 });
        let a = 1u32;
        let b = 2u32;
        // SAFETY: both callers remain alive and initialized through this read.
        assert_eq!(
            unsafe { *raw_from_caller(flag, &a, &b) },
            if flag { 2 } else { 1 }
        );
        assert_eq!(returned_shared_value(flag), if flag { 2 } else { 1 });
        assert_eq!(assigned_one_reaching(flag), if flag { 112 } else { 7 });
    }
}
