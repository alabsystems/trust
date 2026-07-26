#![crate_type = "lib"]
// Guarded remainder: the wrap-around slot is only computed for a non-empty
// ring, so `pos % cap` never divides by zero.
pub fn ring_buffer_slot(pos: u32, cap: u32) -> u32 {
    if cap != 0 { pos % cap } else { 0 }
}
