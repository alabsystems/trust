fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("overflow") => { block_field_overflow(); return; }
        Some("capture-overflow") => { block_array_capture_overflow(); return; }
        Some("divide") => { block_field_divide_by_zero(); return; }
        Some("oob") => { block_array_oob(); return; }
        _ => {}
    }
    for actual in [
        block_field_plain(), block_field_compound(), block_array_plain(), block_array_compound(),
        if_field_plain(), if_field_compound(), if_array_plain(), if_array_compound(),
        loop_field_plain(), loop_array_compound(), match_field_compound(), literal_field_plain(),
        literal_tuple_compound(), literal_array_plain(), repeat_array_compound(),
        call_field_plain(), call_array_compound(), named_const_field_plain(),
        inline_const_array_compound(),
        inline_const_tuple_compound(), inline_const_struct_compound(),
    ] {
        assert_eq!(actual, 1);
    }
    assert_eq!(make_pair().x, 1);
    assert_eq!(make_pair().y, 2);
    assert_eq!(make_array(), [1, 2]);
    assert_eq!(inline_const_array_value(), 17);
    assert_eq!(inline_const_tuple_value(), 17);
    assert_eq!(inline_const_struct_value(), 17);
    assert_eq!(inline_const_nested_value(), 17);
    assert_eq!(block_field_rhs_order(), 7);
    assert_eq!(block_array_effect_order(), 3007);
    assert_eq!(if_base_effect_order(), 123);
    assert_eq!(loop_base_effect_order(), 12);
    assert_eq!(real_reference_compound(), 4);
    assert_eq!(dropping_block_refused(), 7);
    assert_eq!(dropping_if_refused(), 7);
}
