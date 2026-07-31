fn bad_invariant(mut n: u32) {
    while n > 0 invariant n <= 1 {
        n -= 1;
    }
}

#[test]
fn certified_loop_invariant_checks_initial_entry() {
    bad_invariant(2);
}
