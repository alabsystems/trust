fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("array-oob") => { ordinary_array(99); return; }
        Some("slice-oob") => { ordinary_slice_empty(); return; }
        Some("ordinary-slice-oob") => { ordinary_slice_values(99); return; }
        Some("base-panic") => { trapping_base(); return; }
        Some("inner-array-oob") => { inner_array_loop(99); return; }
        Some("inner-slice-oob") => { inner_slice_values(99); return; }
        Some("conditional-empty") => { conditional_empty(false); return; }
        Some("conditional-oob") => { conditional_values(false, 99); return; }
        _ => {}
    }
    assert_eq!(array_base_constant(), 7);
    assert_eq!(both_diverge(), 7);
    assert_eq!(array_index_break(), 7);
    for i in [0, 99] {
        assert_eq!(array_base_dynamic(i), 7);
        assert_eq!(slice_base_dynamic(i), 7);
        assert_eq!(array_base_break(i), 7);
        assert_eq!(slice_base_break(i), 7);
    }
    for s in [&[][..], &[1][..]] {
        assert_eq!(slice_index_returns(s), 7);
        assert_eq!(slice_index_break(s), 7);
        assert_eq!(earlier_refusal(s), 7);
    }
    assert_eq!(slice_return_empty(), 7);
    assert_eq!(slice_break_empty(), 7);
    assert_eq!(conditional_empty(true), 7);
    assert_eq!(conditional_values(true, 99), 7);
    for (i, value) in [(0, 3), (1, 5)] {
        assert_eq!(ordinary_array(i), value);
        assert_eq!(ordinary_slice(&[3, 5], i), value);
        assert_eq!(ordinary_slice_values(i), value);
        assert_eq!(inner_array_loop(i), value);
        assert_eq!(inner_slice_loop(&[3, 5], i), value);
        assert_eq!(inner_slice_values(i), value);
        assert_eq!(conditional_values(false, i), value);
    }
    assert_eq!(array_base_with_asm(), 7);
    assert_eq!(slice_index_with_asm(&[]), 7);
}
