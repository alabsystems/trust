fn unmonitored_loop() {
    let mut n = 2u32;

    // This scalar predicate is deliberately false on the first iteration. If
    // loop clauses ever acquire an uncertified runtime projection, the test
    // executable below must fail instead of silently exercising that change.
    while n > 0 invariant n <= 1 decreases n {
        n -= 1;
    }
}

#[test]
fn loop_clauses_have_no_runtime_projection() {
    unmonitored_loop();
}
