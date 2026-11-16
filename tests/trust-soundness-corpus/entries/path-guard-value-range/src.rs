// trust-soundness-corpus entry `path-guard-value-range` (A' (range twin of A)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn g01_range_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
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
        acc += buf[..len].len();
    }
    acc
}

// Twin: the range bound is the guarded value.
pub fn g01_range_ctl(buf: &[u8; 8], m: usize) -> usize {
    match m {
        3 => buf[..m].len(),
        _ => 0,
    }
}
