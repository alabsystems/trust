#![crate_type = "lib"]
// MUTANT of superiority/proved/two_pointer_reverse.rs: increments `lo` BEFORE the
// access. After `lo += 1` the converging bound `lo < s.len()` no longer holds (lo
// may equal s.len()), and the per-block fact is correctly NOT emitted past the
// increment — so `s[lo]` can be OUT OF BOUNDS and default mode must NOT discharge it.
pub fn two_pointer_reverse(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        lo += 1;
        s[lo] = 0;
        hi -= 1;
    }
}
