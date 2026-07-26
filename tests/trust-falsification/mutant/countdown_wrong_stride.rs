// Trust (countdown-loop piece) MUTANT: stride 5 — 20 - 5*5 < 0: no fact, must
// refute. REAL bug: n = u64::MAX underflows on the 5th trip (20,15,10,5,0,-5).
pub fn wrong_stride(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 5;
        remain /= 10_000;
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
