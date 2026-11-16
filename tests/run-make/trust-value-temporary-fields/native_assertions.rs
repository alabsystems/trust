fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("overflow") => {
            overflow_temporary();
            return;
        }
        Some("divide") => {
            divide_by_zero_temporary();
            return;
        }
        Some("array-oob") => {
            indexed_field_oob();
            return;
        }
        _ => {}
    }
    for actual in [
        struct_compound(),
        tuple_compound(),
        struct_plain(),
        tuple_plain(),
        promoted_struct_compound(),
        promoted_struct_plain(),
        promoted_tuple_compound(),
        promoted_tuple_plain(),
        nested_compound(),
        nested_plain(),
        guard_compound(),
    ] {
        assert_eq!(actual, 1);
    }
    assert_eq!(rhs_replaces_struct(), 7);
    assert_eq!(rhs_replaces_tuple(), 7);
    assert_eq!(side_effecting_base_compound(), 31);
    assert_eq!(side_effecting_base_plain(), 31);
    assert_eq!(real_struct_place(), 4);
    assert_eq!(real_tuple_place(), 4);
    assert_eq!(deref_of_cast_reference(), 4);
    assert_eq!(indexed_field_plain(), 1);
    assert_eq!(indexed_field_compound(), 1);
    assert_eq!(copied_array_field(), 1);
    assert_eq!(indexed_field_effect_order(), 3007);
    assert_eq!(copied_deref_array_plain(), 1);
    assert_eq!(copied_deref_array_compound(), 1);
    assert_eq!(deref_of_cast_array_reference_plain(), 4);
    assert_eq!(deref_of_cast_array_reference_compound(), 4);
    assert_eq!(dropping_plain_refused(), 7);
    assert_eq!(dropping_compound_refused(), 7);
}
