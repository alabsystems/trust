// Trust (countdown-loop piece) MUTANT: the cursor escapes through `&mut` to a
// callee that reseats it (the call-arg &mut staleness class; the
// `local_mut_escapes` P0 fix). REAL bug: the reseated offset indexes far out
// of bounds on the 2nd trip.
#[inline(never)]
fn bump(p: &mut usize) {
    *p = (*p).wrapping_add(100);
}
pub fn cursor_reseat(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10_000;
        bump(&mut offset);
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
