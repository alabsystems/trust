#![crate_type = "lib"]
// MUTANT of proved/led_pwm_duty.rs: the `n < 32` guard is dropped, so the
// shift amount can reach the type width (UB). MUST be refused (exit 1).
pub fn led_pwm_duty(n: u32) -> u32 {
    1u32 << n
}
