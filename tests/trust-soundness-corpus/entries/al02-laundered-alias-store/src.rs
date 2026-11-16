// trust-soundness-corpus entry `al02-laundered-alias-store` (al02 (LAUNDERED-ALIAS-STORE)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[inline(never)]
pub fn launder(p: *const usize) -> *const usize {
    p
}

pub fn al02_launder_store_read_bug(buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        buf[x]
    }
}

// Twin (al18 shape, index row): the guard and the read both follow the store.
pub fn al18_store_then_read_ctl(buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    unsafe {
        *p = n;
        let x = *q;
        if x > 7 {
            return 0;
        }
        buf[x]
    }
}
