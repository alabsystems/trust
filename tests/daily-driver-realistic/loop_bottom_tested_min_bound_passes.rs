// The daily-driver bench's `ctrl/c5`, checked in so the class is pinned here too.
// Was the bench's LAST false refutation; closed 2026-09-19.
//
// It differs from a `while` loop in three ways at once, each a separate refusal
// until handled: the loop is BOTTOM-tested so the TRUE edge exits (continuing is
// the comparison's NEGATION), the compared operand is a COPY of the counter, and
// the limit is an `Ord::min` destination rather than a literal.
// `TRUST_ACC_DEBUG=1` shows `K=6 per_max=1` — `r` runs 1..=6.
pub fn f(x: u32) -> u32 {
    let mut r = 0;
    loop {
        r += 1;
        if r > x.min(5) {
            break;
        }
    }
    r
}
