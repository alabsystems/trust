//! Ordinary integer arithmetic — the bread and butter of real code.
pub fn clamp_add(x: u32, lim: u32) -> u32 { if x < lim { x + 1 } else { lim } }
pub fn sub_guarded(a: u32, b: u32) -> u32 { if a >= b { a - b } else { 0 } }
pub fn scale_byte(b: u8) -> u16 { (b as u16) * 2 }
pub fn widen_add(b: u8) -> u16 { b as u16 + 1 }
pub fn halve(x: u32) -> u32 { x / 2 }
pub fn div_guarded(a: u32, b: u32) -> u32 { if b != 0 { a / b } else { 0 } }
pub fn div_cast(a: u32, b: usize) -> u32 { if b == 0 { 0 } else { a / b as u32 } }
pub fn percent(part: u32, whole: u32) -> u32 { if whole == 0 { 0 } else { part * 100 / whole } }
