// trust-soundness-corpus entry `opaque-scalar-identity` (B (OPAQUE-SCALAR-ID-1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn cc_two_addrs(a: &u8, b: &u8) -> usize {
    let x = a as *const u8 as usize;
    let y = b as *const u8 as usize;
    if x != y {
        panic!("R1 addresses differ");
    }
    x
}

// Twin: one address compared with itself.
pub fn cc_one_addr(a: &u8) -> usize {
    let x = a as *const u8 as usize;
    let y = a as *const u8 as usize;
    if x != y {
        panic!("unreachable");
    }
    x
}
