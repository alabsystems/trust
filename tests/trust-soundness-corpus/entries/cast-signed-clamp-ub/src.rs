// trust-soundness-corpus entry `cast-signed-clamp-ub` (CAST-SIGNED-CLAMP-UB-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn c2_index(v: i32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}

// Twin: the same clamp on an unsigned value is in bounds on every input.
pub fn ctl_u32(v: u32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}
