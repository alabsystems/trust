#![crate_type = "lib"]
// Guarded slice index: reads stay below the slice length.
pub fn sample_at(samples: &[u32], i: usize) -> u32 {
    if i < samples.len() { samples[i] } else { 0 }
}
