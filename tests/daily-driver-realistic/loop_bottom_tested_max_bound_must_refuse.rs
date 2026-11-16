// MUST STAY REFUTED. `max(a, c) >= c` bounds the limit from BELOW, so it says
// nothing about how far the counter can run — `x.max(5)` is unbounded above and
// `r` really can reach u32::MAX and overflow.
//
// This is the guard rail for `bound_operand_upper_bound`: reading `max` as if it
// were `min` would UNDER-count the trip count, which is the false-bound
// direction. The only difference from the passing sibling is the method name.
pub fn f(x: u32) -> u32 {
    let mut r = 0;
    loop {
        r += 1;
        if r > x.max(5) {
            break;
        }
    }
    r
}
