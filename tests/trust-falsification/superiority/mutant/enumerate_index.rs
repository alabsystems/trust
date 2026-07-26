#![crate_type = "lib"]
// MUTANT of superiority/proved/enumerate_index.rs: indexes a DIFFERENT slice `t`
// with `s`'s enumerate index. `t[i]` is OUT OF BOUNDS whenever `t` is shorter than
// `s` (the index ranges over s.len(), not t.len()), so default mode must NOT
// eliminate the `t[i]` check.
pub fn enumerate_index(s: &[u32], t: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (i, _) in s.iter().enumerate() {
        acc = acc.wrapping_add(t[i]);
    }
    acc
}
