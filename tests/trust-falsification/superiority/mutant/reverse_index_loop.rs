#![crate_type = "lib"]
// MUTANT of superiority/proved/reverse_index_loop.rs: indexes `s[i + 1]`. After the
// decrement `i ∈ [0, s.len()-1]`, so `i + 1 ∈ [1, s.len()]` — `i + 1 == s.len()` (when
// i == s.len()-1) is OUT OF BOUNDS. The downward-induction fact bounds `i < s.len()`,
// NOT `i + 1`, so default mode must NOT eliminate the bounds check.
pub fn reverse_index_loop(s: &[u8]) -> u8 {
    let mut t = 0u8;
    let mut i = s.len();
    while i > 0 {
        i -= 1;
        t ^= s[i + 1];
    }
    t
}
