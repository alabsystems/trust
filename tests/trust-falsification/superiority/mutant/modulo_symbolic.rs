#![crate_type = "lib"]
// MUTANT of superiority/proved/modulo_symbolic.rs: indexes `s[k + 1]` past the
// modulo range. `n % s.len()` is in `[0, s.len())`, so `+ 1` can equal `s.len()`
// (when `k == s.len() - 1`) — OUT OF BOUNDS. Default mode must NOT eliminate the
// bounds check (the modulo bound discharges `k < len`, not `k + 1 < len`).
pub fn modulo_symbolic(s: &[u8], n: usize) -> u8 {
    if s.is_empty() {
        0
    } else {
        let k = n % s.len();
        s[k + 1]
    }
}
