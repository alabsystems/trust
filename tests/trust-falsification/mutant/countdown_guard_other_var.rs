// Trust (countdown-loop piece) MUTANT: the loop guard tests a DIFFERENT
// variable than the divided companion (gate: the guarded variable must be the
// one that shrinks). REAL bug: `other` never changes, trips are unbounded;
// offset underflows on the 6th trip.
pub fn guard_other_var(n: u64, other: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while other > 999 {
        offset -= 4;
        remain /= 10_000;
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
