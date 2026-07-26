#![crate_type = "lib"]
// Downward adjacent-element loop: `j` falls from s.len(), guarded by `j > 1`. After
// `j -= 1`, `j >= 1` (from the guard `j > 1` ⟹ `j_old >= 2`), so BOTH `s[j]` and the
// SECONDARY index `s[j - 1]` are in bounds (and `j - 1` does not underflow). `s[j]`
// rides the downward upper bound `j < s.len()`; `s[j-1]` additionally needs the
// guard-derived LOWER bound `j >= 1`. Default mode must fully discharge all checks.
pub fn adjacent_down_loop(s: &[u8]) -> u8 {
    let mut x = 0u8;
    let mut j = s.len();
    while j > 1 {
        j -= 1;
        x ^= s[j] ^ s[j - 1];
    }
    x
}
