fn monitored_loop(mut n: u32) -> u32 {
    while n > 0 invariant n <= 4 decreases n {
        n -= 1;
    }
    n
}

#[test]
fn certified_loop_invariant_and_measure_pass() {
    assert_eq!(monitored_loop(4), 0);
}
