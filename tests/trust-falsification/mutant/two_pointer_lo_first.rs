#![crate_type = "lib"]
// MUTANT (TWO-POINTER-FALSE-REFUTE twin; the gated copy of
// `superiority/mutant/two_pointer_reverse.rs`): `lo += 1` runs BEFORE `s[lo]`, so
// `lo` may equal `s.len()`. The relational guard now certifies the `hi -= 1`
// decrement, but the converging `lo < s.len()` fact must still stop at the
// increment. Runtime oracle: `two_pointer_reverse(&mut [0])` indexes `s[1]`.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, refuted (`[bounds]`). AFTER (predicted): unchanged.
pub fn two_pointer_reverse(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        lo += 1;
        s[lo] = 0;
        hi -= 1;
    }
}
