#![crate_type = "lib"]
// Guarded SIGNED division: excludes both divide-by-zero and the i32::MIN / -1
// overflow, the only two failure modes of signed division.
pub fn waveform_scale_div(n: i32, d: i32) -> i32 {
    if d != 0 && !(n == i32::MIN && d == -1) { n / d } else { 0 }
}
