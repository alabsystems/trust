// MUST STAY REFUTED. `x` is an unconstrained parameter, so the loop has no
// finite trip count and `r += 1` really can overflow at `x == u32::MAX`.
// The control that isolates the `min`: same loop, limit not bounded above.
pub fn f(x: u32) -> u32 {
    let mut r = 0;
    loop {
        r += 1;
        if r > x {
            break;
        }
    }
    r
}
