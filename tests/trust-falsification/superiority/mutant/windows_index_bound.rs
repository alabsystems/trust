#![crate_type = "lib"]
// MUTANT of superiority/proved/windows_index_bound.rs: w[2] is OUT OF BOUNDS — a
// windows(2) sub-slice has length exactly 2, so index 2 never exists. Default mode
// must NOT eliminate the check.
pub fn windows_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for w in s.windows(2) {
        acc ^= w[0] ^ w[2];
    }
    acc
}
