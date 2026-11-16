fn main() {
    for flag in [true, false] {
        let result = if flag { 42 } else { 15 };
        assert_eq!(scalar_write(flag), result);
        assert_eq!(field_write(flag), result);
        assert_eq!(shared_read(flag), if flag { 1 } else { 2 });
        assert_eq!(returned_shared(flag), if flag { 1 } else { 2 });
        assert_eq!(returned_mut(flag), result);
        assert_eq!(one_live_arm(flag), if flag { 22 } else { 4 });
        assert_eq!(mixed_outlives(flag), if flag { 99 } else { 1 });
        assert_eq!(shared_from_mut_join(flag), if flag { 1 } else { 2 });
        assert_eq!(mixed_frame(flag), if flag { 7 } else { 2 });
    }
    assert_eq!(nested_write(true, true), 423);
    assert_eq!(nested_write(true, false), 153);
    assert_eq!(nested_write(false, true), 126);
    assert_eq!(nested_write(false, false), 126);
}
