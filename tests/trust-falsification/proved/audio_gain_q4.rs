#![crate_type = "lib"]
// Guarded SIGNED multiplication: a Q4 fixed-point gain of a sample bounded to
// [-1000, 1000] stays far inside i32 (|n * 4| <= 4000). Both dominating
// bounds — including the NEGATIVE one — must be BV-encoded for the
// arithmetic-safety obligation to be PROVED.
pub fn audio_gain_q4(n: i32) -> i32 {
    if n >= -1000 && n <= 1000 { n * 4 } else { 0 }
}
