// Trust (countdown-loop piece, P0 root-cause regression): the PRE-EXISTING
// downward-induction fact `_t.0 < s.len()` was emitted even when the cursor is
// reseated through `&mut` AFTER the access — false at runtime on the second
// iteration (i = len+98 indexes OOB, rc=101), and it vacuously proved the
// bounds row. `local_mut_escapes` must disqualify the var entirely.
#[inline(never)]
fn bump(p: &mut usize) {
    *p = (*p).wrapping_add(100);
}
pub fn rev_reseat(s: &[u8]) -> u8 {
    let mut i = s.len();
    let mut acc = 0u8;
    while i > 0 {
        i -= 1;
        acc = acc.wrapping_add(s[i]);
        bump(&mut i);
    }
    acc
}
