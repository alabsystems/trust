// Trust (countdown-loop piece) MUTANT: one-smaller buffer — LEN 19, T 5:
// 19 - 20 < 0, so the loop-site SUB gets NO fact and must refute. REAL bug:
// n = u64::MAX underflows offset on the 5th trip (runtime rc=101).
pub fn fmt_u64_short(n: u64, buf: &mut [u8; 19]) -> usize {
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
    offset
}
