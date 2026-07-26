// Trust (countdown-loop piece) MUTANT: divisor 10 with stride 4 — T(10,999,u64)
// = 17, 20 - 68 < 0: no fact, must refute. REAL bug at n = u64::MAX (trip 6).
pub fn wrong_divisor(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10;
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
