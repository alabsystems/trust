#![crate_type = "lib"]
// MUTANT of proved/r3_generic_alias_guarded_index.rs: `xs[i + 1]` under the
// `i < xs.len()` guard — off-by-one OOB at i == xs.len()-1 (and i+1 may also
// overflow at usize::MAX). Must REFUTE / fail closed; a pass here would mean
// the R3 alias relaxation manufactured a false bounds proof.
pub fn r3_pick<I: Iterator>(xs: &[I::Item], i: usize) -> Option<&I::Item> {
    if i < xs.len() { Some(&xs[i + 1]) } else { None }
}
