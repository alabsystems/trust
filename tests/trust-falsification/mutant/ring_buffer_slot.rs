#![crate_type = "lib"]
// MUTANT of proved/ring_buffer_slot.rs: the `cap != 0` guard is dropped, so
// the remainder divides by zero. MUST be refused (exit 1).
pub fn ring_buffer_slot(pos: u32, cap: u32) -> u32 {
    pos % cap
}
