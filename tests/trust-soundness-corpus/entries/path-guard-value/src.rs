// trust-soundness-corpus entry `path-guard-value` (A (PATH-GUARD-VALUE-1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn gs_one_arm_scalar_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        if c {
            len = n;
        }
        acc ^= buf[len];
    }
    acc
}

// Twin: the guard tests the value the index reads.
pub fn gs_guard_after_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        if c {
            len = n;
        }
        match len {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[len];
    }
    acc
}
