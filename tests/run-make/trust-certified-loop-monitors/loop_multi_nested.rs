fn multi_latch_and_nested(mut outer: u32) -> u32 {
    while outer > 0 invariant outer <= 4 decreases outer {
        let mut inner = 3u32;
        while inner > 0 invariant inner <= 3 decreases inner {
            if inner & 1 == 0 {
                inner -= 1;
                continue;
            }
            inner -= 1;
        }
        if outer & 1 == 0 {
            outer -= 1;
            continue;
        }
        outer -= 1;
    }
    outer
}

#[test]
fn every_latch_and_nested_reentry_is_measured() {
    assert_eq!(multi_latch_and_nested(4), 0);
}
