#![crate_type = "lib"]
// Reverse manual index loop: `i` starts at `s.len()` and is only decremented, so
// after `i -= 1` (guarded by `i > 0`) the access `s[i]` is in bounds. The guard
// `i > 0` does NOT bound `i` above — the bound comes from the downward-induction
// invariant `i <= s.len()` (init + monotone decrement), so each decrement result
// `i - 1 < s.len()`. Default mode must fully discharge the bounds check.
pub fn reverse_index_loop(s: &[u8]) -> u8 {
    let mut t = 0u8;
    let mut i = s.len();
    while i > 0 {
        i -= 1;
        t ^= s[i];
    }
    t
}
