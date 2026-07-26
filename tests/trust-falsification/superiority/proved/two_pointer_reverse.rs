#![crate_type = "lib"]
// In-place reversal by converging pointers: `lo` rises from 0, `hi` falls from
// s.len(), loop while `lo < hi`. BOTH `s[lo]` and `s[hi]` are in bounds, and the
// `hi -= 1` cannot underflow (`lo < hi` + `lo >= 0` ⟹ `hi >= 1`). `s[hi]` rides the
// downward-induction fact; `s[lo]` rides the converging fact `lo < hi <= s.len()`
// (emitted per-block only where `lo` is unchanged since the guard). Default mode
// must fully discharge all six obligations (4 bounds + sub + add).
pub fn two_pointer_reverse(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}
