#![crate_type = "lib"]
// MUTANT of proved/merged_local_index.rs: the branch-merged `step ∈ {1,2}` is
// REASSIGNED to the unbounded `idx` after the merge. A STALE branch-merge fact
// (`step <= 2`) kept past the reassignment would vacuously discharge the bounds
// check on the now-unbounded `step` — a false-PROVE of a real out-of-bounds access.
// The verifier MUST refuse it (the path-definition staleness kill / establish-point
// versioning drops the stale merge fact). Guards the branch-merge path-definition
// lane against false-proving a reassigned merged local.
pub fn merged_local_index(c: bool, idx: usize, s: &[u32]) -> u32 {
    let mut step = if c { 1usize } else { 2usize };
    step = idx;
    if s.len() > 2 { s[step] } else { 0 }
}
