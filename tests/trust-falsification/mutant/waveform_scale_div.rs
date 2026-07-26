#![crate_type = "lib"]
// MUTANT of proved/waveform_scale_div.rs: keeps the zero guard but drops the
// i32::MIN / -1 overflow exclusion — the SUBTLE signed-division failure mode.
// MUST be refused (exit 1).
pub fn waveform_scale_div(n: i32, d: i32) -> i32 {
    if d != 0 { n / d } else { 0 }
}
