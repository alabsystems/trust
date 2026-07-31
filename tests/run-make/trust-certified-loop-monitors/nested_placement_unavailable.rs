pub fn optimized_away_inner_loop(mut n: u32) {
    while n > 0 invariant n <= 4 decreases n {
        while false invariant n == n {
            unreachable!();
        }
        n -= 1;
    }
}
