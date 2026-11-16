// trust-soundness-corpus entry `h2-raw-const-store` (H2 (RAW-CONST-STORE)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn ce06_raw_const_store_index_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    unsafe { *(p as *mut usize) += 4 };
    t[k]
}

// Twin (h2c4): the guard is taken after the store and tests the stored value.
pub fn h2c4_guard_after_store_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    unsafe { *(p as *mut usize) = n };
    if k > 3 {
        return 0;
    }
    t[k]
}
