// Trust (countdown-loop piece) WIN, u64 twin — the EXACTLY-TIGHT case: T = 5
// and LEN = 20 consume the buffer to exactly offset 0 (`_t.0 >= 0`). u64::MAX
// (20 digits) runs the quad loop exactly 5 times writing offsets 16,12,8,4,0.
// The 19-byte mutant twin refutes (tests/trust-falsification/mutant/).
pub fn fmt_u64(n: u64, buf: &mut [u8; 20]) -> usize {
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
