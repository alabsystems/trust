// Trust (countdown-loop piece) MUTANT (B3 tightness): u32 with a 9-byte buffer
// — the post-loop `-=2` site bound is 9 - 8 - 2 < 0: NO fact, must refute.
// REAL bug: n = u32::MAX exits the loop at offset 1, `offset -= 2` underflows.
pub fn fmt_u32_short(n: u32, buf: &mut [u8; 9]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10_000;
        buf[offset] = (remain % 10) as u8;
    }
    if remain > 9 {
        offset -= 2;
        buf[offset] = ((remain / 10) % 10) as u8;
        buf[offset + 1] = (remain % 10) as u8;
    }
    offset
}
