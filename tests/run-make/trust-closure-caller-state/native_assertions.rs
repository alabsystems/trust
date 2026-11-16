fn main() {
    assert_eq!(by_value_repeated(), 2);
    assert_eq!(by_reference_repeated(), 2);
    assert_eq!(copied_value_environments(), 32);
    assert_eq!(moved_reference_environment(), 2);
    assert_eq!(moved_current_environment(), 2);
    assert_eq!(mutable_reference_alias(), 3);
    assert_eq!(shared_reference_alias(), 10);
    assert_eq!(captured_reference_alias(), 2);
    assert_eq!(destructured_value_environment(), 2);
    assert_eq!(destructured_shared_environment(), 10);
    assert_eq!(once_guard(&mut 7), 7);
    assert_eq!(once_guard_local(), 7);
    assert_eq!(projected_guard(), 2);
    assert_eq!(borrowed_array_capture(), 1);
    for flag in [false, true] {
        assert_eq!(branch_initialized(flag), 7);
        assert_eq!(match_initialized(flag), 2);
        assert_eq!(tuple_branch_initialized(flag), if flag { 8 } else { 9 });
    }
    assert_eq!(by_value_array_guard(), 1);
    assert_eq!(ordinary_tuple_guard(), 2);
}
