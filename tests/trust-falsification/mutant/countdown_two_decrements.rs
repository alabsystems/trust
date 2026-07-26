// Trust (countdown-loop piece) MUTANT: a SECOND on-cycle decrement (gate 2:
// exactly one loop-site decrement, else the per-trip stride is under-counted).
// REAL bug: 5 trips consume 25 > 20; underflow on the 5th trip at u64::MAX.
pub fn two_decrements(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10_000;
        buf[offset] = (remain % 10) as u8;
        offset -= 1;
    }
    offset
}
