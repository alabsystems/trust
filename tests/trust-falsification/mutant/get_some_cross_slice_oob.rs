// MUTANT twin of proved/get_some_index_increment.rs: `a.get(i) == Some` must not
// discharge an index into a DIFFERENT slice `b` (`b = []` panics OOB at
// runtime) — the fact bounds `i` against `a`'s length symbol only.
#![crate_type = "lib"]

pub fn cross_index(a: &[u32], b: &[u32], i: usize) -> u32 {
    if let Some(_) = a.get(i) {
        return b[i];
    }
    0
}
