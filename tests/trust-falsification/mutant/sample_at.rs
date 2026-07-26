#![crate_type = "lib"]
// MUTANT of proved/sample_at.rs: the `i < samples.len()` guard is dropped, so
// the index can exceed the slice length. MUST be refused (exit 1).
pub fn sample_at(samples: &[u32], i: usize) -> u32 {
    samples[i]
}
