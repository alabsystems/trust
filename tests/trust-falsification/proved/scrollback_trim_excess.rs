#![crate_type = "lib"]
// Guarded subtraction: trimming a scrollback buffer never underflows under
// the `len >= keep` guard. The arithmetic-safety obligation must be PROVED.
pub fn scrollback_trim_excess(len: u32, keep: u32) -> u32 {
    if len >= keep { len - keep } else { 0 }
}
