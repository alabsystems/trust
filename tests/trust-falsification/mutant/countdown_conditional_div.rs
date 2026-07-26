// Trust (countdown-loop piece) MUTANT: `if flag { remain /= D }` — THE
// unbounded-trip false-proof trap (gate 6: division must be unavoidable per
// iteration). REAL bug: flag = false never shrinks remain; offset underflows
// on the 6th trip at n = u64::MAX.
pub fn conditional_div(n: u64, flag: bool, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        if flag {
            remain /= 10_000;
        }
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
