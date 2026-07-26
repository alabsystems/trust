// Trust (countdown-loop piece) MUTANT: the companion is re-inflated in the
// body (gate 5: a non-division def that can reach the guard). REAL bug: remain
// never stays below the guard; offset underflows on the 6th trip.
pub fn companion_reinflate(n: u64, buf: &mut [u8; 20]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10_000;
        remain = remain.wrapping_add(1_000_000);
        buf[offset] = (remain % 10) as u8;
    }
    offset
}
