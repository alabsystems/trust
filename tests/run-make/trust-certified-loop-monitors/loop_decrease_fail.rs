fn bad_measure(mut n: u32) {
    while n > 0 invariant n <= 2 decreases 0 {
        // The loop would otherwise diverge. E5 must reject the first
        // non-decreasing backedge before another iteration begins.
        n = n;
    }
}

#[test]
fn certified_loop_measure_checks_every_backedge() {
    bad_measure(2);
}
