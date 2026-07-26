// Trust (countdown-loop piece, P0 root-cause regression): the converging
// two-pointer per-block fact `lo < s.len()` survived a `bump(&mut lo)` reseat
// (`local_write_blocks` sees only visible defs) — false at runtime (s[100] on
// a 5-element slice, rc=101). The `local_mut_escapes` check must skip `lo`.
#[inline(never)]
fn bump(p: &mut usize) {
    *p = (*p).wrapping_add(100);
}
pub fn conv_reseat(s: &[u8]) -> u8 {
    let mut lo = 0usize;
    let mut hi = s.len();
    let mut acc = 0u8;
    while lo < hi {
        hi -= 1;
        bump(&mut lo);
        acc = acc.wrapping_add(s[lo]);
        lo += 1;
    }
    acc
}
