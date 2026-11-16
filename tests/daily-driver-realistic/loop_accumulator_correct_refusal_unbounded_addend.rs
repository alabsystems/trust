// MUST STAY REFUTED. Summing arbitrary `u32` values really can overflow: nothing
// about the loop bounds the addend. A trip-count refinement that makes this pass
// has over-fired, because the trip count bounds how MANY additions happen and not
// how large each one is.
pub fn f(xs: &[u32]) -> u32 {
    let mut s = 0u32;
    for x in xs {
        s += *x;
    }
    s
}
