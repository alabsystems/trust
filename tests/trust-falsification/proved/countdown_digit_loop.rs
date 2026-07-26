// Trust (countdown-loop piece) WIN: the itoa `Unsigned::fmt` countdown shape,
// u32 (T = 2). The loop-site bound is `_t.0 >= 10 - 4*2 = 2`; the post-loop
// `-=2` site is EXACTLY tight at 0 (K(10) = 2); the `-=1` site min-over-paths
// is 1 (reseat `/= 100` tightening + the `n == 0` zero-trip witness).
pub fn fmt_u32(n: u32, buf: &mut [u8; 10]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        let quad = remain % 10_000;
        remain /= 10_000;
        buf[offset] = (quad / 1000) as u8;
        buf[offset + 1] = ((quad / 100) % 10) as u8;
        buf[offset + 2] = ((quad / 10) % 10) as u8;
        buf[offset + 3] = (quad % 10) as u8;
    }
    if remain > 9 {
        offset -= 2;
        buf[offset] = ((remain / 10) % 10) as u8;
        buf[offset + 1] = (remain % 10) as u8;
        remain /= 100;
    }
    if remain != 0 || n == 0 {
        offset -= 1;
        buf[offset] = remain as u8;
    }
    offset
}
