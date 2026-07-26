#![crate_type = "lib"]
// MUTANT (signed-accumulator NESTED soundness): the inner reduction runs `M*LEN` times, so the
// trip count is the WHOLE-NEST product (`total_loop_iterations`), NOT the inner array length.
// With M=3_000_000 and LEN=8, k=24_000_000 and the i32 accumulator CAN overflow
// (24_000_000 * 127 > i32::MAX), so `-full` MUST refute (exit 1). This PINS that the signed
// reduction bound multiplies by `k`, not `LEN`: a regression that used the inner array length
// would synthesize a bogus `[LEN*MIN, LEN*MAX] = [-1024, 1016]` bound — entirely inside i32 — and
// FALSE-PROVE a reduction that overflows at runtime.
pub fn f(a: &[i8; 8]) -> i32 {
    let mut s: i32 = 0;
    for _ in 0..3_000_000 {
        for &x in a {
            s += x as i32;
        }
    }
    s
}
