// trust-soundness-corpus entry `al07-laundered-alias-elide` (LAUNDERED-ALIAS-ELIDE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn al07_cast_store_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q: *const usize = p as *const usize;
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// Twin (al18): store through `p`, then the guard and the row both read through `q`.
pub fn al18_store_then_read_ctl(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        *p = n;
        if *q > 7 {
            return 0;
        }
        *q + 1
    }
}
