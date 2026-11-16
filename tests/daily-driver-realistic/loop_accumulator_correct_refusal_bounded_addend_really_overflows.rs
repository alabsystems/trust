// MUST STAY REFUTED — and it is the SHARP guard rail, because it has the exact
// shape of the two witnesses that must become provable: a manual `while` loop,
// a CONSTANT bound, a CONSTANT stride, one self-add.
//
// `c` is `u8` and the loop runs 100 times adding 3, so `c` reaches 300 and
// really does overflow (at `c == 253`, `c += 3` is 256 > u8::MAX).
//
// A trip-count bound must therefore be SELF-LIMITING: emitting `c <= 0 + 100*3`
// = `c <= 300` leaves `c + 3 <= 255` satisfiable, so the obligation still fails.
// An implementation that instead INTERSECTS the computed bound with the
// accumulator's own type range would emit `c <= 255` and falsely prove this
// program safe. That is the single most likely way to get this wrong, and this
// file is the probe for it.
pub fn f() -> u8 {
    let mut c = 0u8;
    let mut i = 0u32;
    while i < 100 {
        c += 3;
        i += 1;
    }
    c
}
