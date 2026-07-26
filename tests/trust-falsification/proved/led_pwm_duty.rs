#![crate_type = "lib"]
// Guarded shift: a PWM duty bit index below 32 keeps `1u32 << n` defined.
pub fn led_pwm_duty(n: u32) -> u32 {
    if n < 32 { 1u32 << n } else { 0 }
}
