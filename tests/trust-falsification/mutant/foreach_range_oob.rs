#![crate_type = "lib"]
// MUTANT (range for-loop bounds): `for i in 0..n` over a fixed-size `[u8; 4]` is
// OUT OF BOUNDS whenever `n > 4` (e.g. n=5 reaches i=4). Genuinely violable, so
// `-full` MUST refute it (exit 1). This also pins the soundness of the new Range
// iterator lowering (`total_range_iterator_call`): modelling the loop index as
// unconstrained lets the precise V1 path find the real counterexample (i=4, n=5),
// rather than the whole function fail-closing on the unlowerable `into_iter`.
pub fn f(n: usize) -> u8 {
    let a = [0u8; 4];
    let mut t = 0u8;
    for i in 0..n {
        t = t.wrapping_add(a[i]);
    }
    t
}
