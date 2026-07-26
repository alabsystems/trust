#![crate_type = "lib"]
// MUTANT of proved/mixed_total_call.rs: swap the total `x.min(1000)` for
// `x.pow(20)`. `u32::pow` is an UNMODELED external call that PANICS on overflow
// (`x` can be up to 256, and 256^20 overflows u32 enormously). The `(a as u32)+1`
// obligation is still provable, so before the #48 fix the function read as "1
// proved, 0 failed" — a FALSE PROOF, because the pow panic is on no obligation the
// bridge sees. The verifier MUST now refuse it (exit 1): native typed-TrustIr
// lowering fails on the unmodeled panicking call, so full verification cannot be
// certified (an unverified panic path remains).
pub fn mixed_total_call(a: u8) -> u32 {
    let x = (a as u32) + 1;
    x.pow(20)
}
