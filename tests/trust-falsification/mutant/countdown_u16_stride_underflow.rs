// Trust (countdown-loop piece) MUTANT — the fuzzer-caught FALSE-PROOF pin:
// u16 companion, stride 4, buffer 3 (one below the exact 4). B - c = -1: the
// negative-constant Le fact this once minted collided with the VC lane's
// `result >= 0` type range into an UNSAT premise set, vacuously proving the
// underflow. The builder must emit NOTHING here; the SUB row must refute.
// REAL bug: n = u16::MAX runs one trip, 3 - 4 underflows (runtime rc=101).
pub fn fmt_u16_short(n: u16, buf: &mut [u8; 3]) -> usize {
    let mut offset = buf.len();
    let mut remain = n;
    while remain > 999 {
        offset -= 4;
        remain /= 10_000;
        buf[offset] = (remain & 0xff) as u8;
    }
    offset
}
