#![crate_type = "lib"]
// MUTANT of superiority/proved/adjacent_down_loop.rs: weakens the guard to `j > 0`.
// Now after `j -= 1`, `j` can be 0, so the secondary index `s[j - 1]` underflows
// (`0 - 1`) — a REAL out-of-bounds. The guard-derived lower bound is `(0+1)-1 = 0`,
// below the needed 1, so it is NOT emitted and default mode must NOT discharge the
// `j - 1` subtraction.
pub fn adjacent_down_loop(s: &[u8]) -> u8 {
    let mut x = 0u8;
    let mut j = s.len();
    while j > 0 {
        j -= 1;
        x ^= s[j] ^ s[j - 1];
    }
    x
}
