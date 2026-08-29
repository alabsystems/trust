#![no_std]
//! MUTATION CONTROL B for clamp.rs: clause unchanged and TRUE-in-intent, body broken.
pub fn clamp100(n: u32) -> u32 ensures result <= 100 {
    n
}
