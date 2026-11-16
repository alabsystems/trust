#![crate_type = "lib"]
// MUTANT (CAST-SIGNED-REDUCTION-TARGET-1, 2026-10-05): the twin of
// `proved/signed_accumulator.rs` with an UNSIGNED cast target. `-1i8 as u32` is
// 4294967295, so `[-1, -1, 0, 0]` overflows the second add. The signed-reduction
// lane returned the ELEMENT's range `[-128, 127]` as the ADDEND's without reading
// the cast target, and conjoined `t <= 508` and `t + addend <= 508`; the overflow
// row was kernel-certified (stage1-w15r, these gate flags: rc=0, "2 proved ... of
// which 2 kernel-certified"). With the lane requiring a value-preserving signed
// target this MUST fail closed (exit 1).
pub fn sum_u32(a: &[i8; 4]) -> u32 {
    let mut t: u32 = 0;
    for x in a {
        t += *x as u32;
    }
    t
}
