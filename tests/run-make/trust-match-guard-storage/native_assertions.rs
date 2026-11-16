fn main() {
    if std::env::args().any(|a| a == "trap") {
        checked_guard(false);
        std::process::exit(0);
    }
    if std::env::args().any(|a| a == "overflow") {
        array_guard_overflow();
        std::process::exit(0);
    }
    if std::env::args().any(|a| a == "unit-overflow") {
        unit_guard_rhs_overflow();
        std::process::exit(0);
    }
    assert_eq!(unit_guard_rhs_assignment(), 7);
    assert_eq!(ssa_cast_base(), 1);
    assert_eq!(promoted_cast_base(), 1);
    assert_eq!(guard_cast_base(), 1);
    assert_eq!(cast_rhs_replaces_base(), 7);
    assert_eq!(array_guard_rhs(), 18);
    assert_eq!(unit_guard(), 7);
    assert_eq!(unrelated_guard_shadow(), 7);
    assert_eq!(literal_true(), 16);
    assert_eq!(literal_false(), 33);
    assert_eq!(chained_guards(), 33);
    assert_eq!(looped(), 2);
    assert_eq!(guard_local_shadow(), 14);
    assert_eq!(checked_guard(true), 6);
    assert_eq!(array_guard(), 10);
    assert_eq!(successive_matches(), 12);
    assert_eq!(nested_guard(), 4);
    for x in [0u32, 1, 7, 42, u32::MAX] {
        assert_eq!(catch_all(x), 2 + 2 * (x & 7));
        assert_eq!(case_then_catch(x), if x == 0 { 66 } else { 44 + (x & 7) });
        assert_eq!(guard_then_range(x), if x <= 3 { 12 } else { 22 });
        assert_eq!(mutable_parameter(x), x & 7);
    }
}
