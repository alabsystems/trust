// trust-soundness-corpus entry `h1-stale-bound-call-rename` (H1 (STALE-BOUND-CALL-RENAME)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn pb04_folded_ref_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let z = &mut len;
    let r = ..*z;
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// Twin (pc02): a single-assignment bound read through `z = &len`.
pub fn pc02_folded_ssa_local_ctl(buf: &[u8; 8], m: usize) -> usize {
    let len = m.min(8);
    let z = &len;
    buf[..*z].len()
}
