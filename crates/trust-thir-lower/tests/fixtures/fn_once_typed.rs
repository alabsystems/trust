// Source-semantic controls for the typed FnOnce environment protocol.
// The native oracle establishes expected behavior; branch IR checks run separately.
pub fn moved_reference(value: &mut i32, delta: i32) -> i32 {
    let once = move |amount| {
        let target = value;
        *target += amount;
        *target
    };
    once(delta)
}

pub fn same_reference(value: &mut i32) -> &mut i32 {
    let once = move || value;
    once()
}

pub fn receiver_before_argument(value: &mut i32) -> (i32, i32) {
    let mut order = 0;
    let result = ({
        order = order * 10 + 1;
        move |amount| {
            let target = value;
            *target += amount;
            *target
        }
    })({
        order = order * 10 + 2;
        5
    });
    (result, order)
}

pub fn once_failure(value: &mut i32) {
    let once = move || {
        let target = value;
        *target += 1;
        assert!(*target == 99);
    };
    once();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn move_retains_alias_and_post_call_store() {
        let mut value = 10;
        assert_eq!(moved_reference(&mut value, 5), 15);
        assert_eq!(value, 15);
    }
    #[test]
    fn returned_pointer_identity_is_preserved() {
        let mut value = 10;
        let original = &mut value as *mut i32;
        let returned = same_reference(&mut value);
        assert!(core::ptr::eq(returned, original));
        *returned = 23;
        assert_eq!(value, 23);
    }
    #[test]
    fn receiver_effects_precede_tuple_argument_effects() {
        let mut value = 10;
        assert_eq!(receiver_before_argument(&mut value), (15, 12));
        assert_eq!(value, 15);
    }
    #[test]
    fn panic_keeps_preceding_capture_store() {
        let mut value = 10;
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| once_failure(&mut value))).is_err());
        assert_eq!(value, 11);
    }
    #[test]
    fn ordinary_fn_and_fnmut_behavior_remains_distinct() {
        let value = 7;
        let shared = || value;
        assert_eq!((shared(), shared()), (7, 7));
        let mut value = 0;
        let mut mutable = || { value += 1; value };
        assert_eq!((mutable(), mutable()), (1, 2));
    }
}
