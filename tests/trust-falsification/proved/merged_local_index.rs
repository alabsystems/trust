#![crate_type = "lib"]
// A branch-merged local `step ∈ {1, 2}` — recovered by the PATH-DEFINITION lane's
// SwitchInt-join `Ite` fact (`step == Ite(c, 1, 2)`) — bounds an index: `step <= 2`,
// and under the dominating guard `s.len() > 2` that gives `step < s.len()`, so
// `s[step]` is statically in bounds and PROVES. No reassignment: the merge fact is
// LIVE, so it must reach the bounds VC. (Control for the staleness mutant.)
pub fn merged_local_index(c: bool, s: &[u32]) -> u32 {
    let step = if c { 1usize } else { 2usize };
    if s.len() > 2 { s[step] } else { 0 }
}
