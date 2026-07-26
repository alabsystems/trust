#![crate_type = "lib"]
// MUTANT (fp benign-cast soundness twin): WITHOUT the `& 3` mask, `arr[(a + b) as usize]`
// over `[u8;4]` is OUT OF BOUNDS — `(a+b) as usize` saturates to usize::MAX (or any
// large value), indexing far past len 4. Suppressing the (benign) float-overflow
// obligation must NOT hide this: the index BOUNDS obligation is separate and genuinely
// violable, so `-full` MUST refute (exit 1). Pins that the float-overflow suppression
// is sound (it removes only the non-trapping numerical obligation, never a real OOB).
pub fn f(a: f64, b: f64, arr: &[u8; 4]) -> u8 {
    arr[(a + b) as usize]
}
