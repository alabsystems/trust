#![crate_type = "lib"]
// Nested 2D matrix sum (#50): the canonical grid/matrix reduction. The self-add runs
// N*M = 4*4 = 16 times, each adding a widened u8 (<= 255), so `t <= 16 * 255 = 4080 <
// u32::MAX`. rustc keeps the per-iteration add-overflow check; Trust discharges it BY
// DEFAULT via the accumulator bound with the trip count `K` taken as the PRODUCT of both
// loops' const trip counts (`total_loop_iterations`). Pairs with the discriminating
// overflow mutant `nested_2d_overflow` and the unbounded-inner-loop soundness mutant
// `nested_while_unbounded`.
pub fn nested_2d_sum(a: &[[u8; 4]; 4]) -> u32 {
    let mut t: u32 = 0;
    for i in 0..4 {
        for j in 0..4 {
            t += a[i][j] as u32;
        }
    }
    t
}
