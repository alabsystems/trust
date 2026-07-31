fn bad_fallthrough_latch(mut n: u32) {
    let mut stalled = false;
    while n > 0 invariant n <= 2 decreases n {
        if n == 2 {
            // The continue latch descends correctly.
            n -= 1;
            continue;
        }
        // The distinct fallthrough latch does not. This reaches `n == 1`
        // only after the continue edge has already passed its own check.
        if stalled {
            // If the fallthrough monitor disappeared, make the next trip
            // descend and terminate rather than hanging the regression test.
            n = 0;
        } else {
            stalled = true;
        }
    }
}

#[test]
fn certified_loop_measure_checks_fallthrough_latch() {
    bad_fallthrough_latch(2);
}
