// Trust (countdown-loop piece) MUTANT: division by ONE — never shrinks
// (D >= 2 gate; also protects the analyzer's own trip simulation from
// non-termination). REAL bug: unbounded trips; offset underflows on trip 6.
pub fn div_by_one(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    let step = 1u64;
    while remain > 999 {
        offset -= 4;
        remain /= step;
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
