fn bad_continue_latch(mut n: u32) {
    let mut first = true;
    while n > 0 invariant n <= 2 decreases n {
        if first {
            // This is one of two distinct latches in the loop. It does not
            // decrease and must be checked independently of the fallthrough
            // latch below.
            first = false;
            continue;
        }
        // If the continue-latch monitor disappeared, terminate on the other
        // edge instead of leaving the regression test spinning.
        n = 0;
    }
}

#[test]
fn certified_loop_measure_checks_continue_latch() {
    bad_continue_latch(2);
}
