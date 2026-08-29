fn bad_inner_measure(mut outer: u32) {
    while outer > 0
        invariant outer <= 2
        decreases outer
    {
        let mut inner = 2u32;
        let mut stalled = false;
        while inner > 0
            invariant inner <= 2
            decreases inner
        {
            if stalled {
                // If the inner-loop monitor disappeared, terminate on the next trip instead of
                // leaving the regression control spinning.
                inner = 0;
            } else {
                // The authenticated inner backedge does not decrease. The outer loop remains
                // valid, so only a present inner E5 monitor can make this program fail.
                stalled = true;
            }
        }
        outer -= 1;
    }
}

#[test]
fn a_supported_inner_loop_has_its_own_measure_monitor() {
    bad_inner_measure(2);
}
