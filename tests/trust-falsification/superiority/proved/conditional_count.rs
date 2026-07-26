#![crate_type = "lib"]
// Conditional COUNT reduction (#50): count the elements matching a predicate. The self-add
// `t += 1` is a non-negative CONSTANT addend guarded by a condition, so it runs at most once
// per loop iteration — `t <= K * 1 = 4 < u16::MAX`. rustc keeps the per-iteration
// add-overflow check; Trust discharges it BY DEFAULT via the accumulator bound, with the
// trip count `K` taken from the loop's own exclusive `Range` (`loop_trip_count`, since a
// constant addend carries no element to trace). Pairs with the discriminating overflow
// mutant `count_overflow`.
pub fn conditional_count(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for i in 0..4 {
        if a[i] > 10 {
            t += 1;
        }
    }
    t
}
