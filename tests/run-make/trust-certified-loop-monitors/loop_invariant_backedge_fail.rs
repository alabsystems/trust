fn bad_after_iteration(mut n: u32) {
    let mut violated = false;
    while n > 0 invariant n <= 2 {
        // The invariant holds on initial entry (`n == 1`) and fails only
        // after the first completed iteration.
        if !violated {
            n = 3;
            violated = true;
        } else {
            // If the post-iteration monitor disappeared, terminate instead
            // of turning the regression control into a hung test.
            n = 0;
        }
    }
}

#[test]
fn certified_loop_invariant_checks_completed_iterations() {
    bad_after_iteration(1);
}
