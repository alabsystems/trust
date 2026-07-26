#![crate_type = "lib"]
// MUTANT of proved/audio_gain_q4.rs: the range guard is dropped, so the
// signed multiplication overflows for large |n| (e.g. n = i32::MAX / 2). The
// verifier MUST refuse this (exit 1).
pub fn audio_gain_q4(n: i32) -> i32 {
    n * 4
}
