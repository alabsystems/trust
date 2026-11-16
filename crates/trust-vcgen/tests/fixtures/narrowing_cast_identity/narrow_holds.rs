// VC-NARROW-CAST-FALSE-REFUTE-1 real-MIR fixture: a narrowing integer cast whose
// source the guard keeps inside the target type is the identity on that value.
pub fn a6(c: char) -> u8 { let arr = [0u8; 0x80]; if c.is_ascii() { arr[c as u8 as usize] } else { 0 } }
pub fn b1(x: u32) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { arr[x as u8 as usize] } else { 0 } }
pub fn n1(x: u32) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { arr[x as u16 as usize] } else { 0 } }
pub fn n2(x: u16) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { arr[x as u8 as usize] } else { 0 } }
pub fn n4(x: u32) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { let b = x as u8; arr[b as usize] } else { 0 } }
pub fn n6(x: u64) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { arr[x as u32 as usize] } else { 0 } }
pub fn i16n(x: i32) -> u8 { let arr = [0u8; 0x80]; if x >= 0 && x < 0x80 { arr[(x as i16) as usize] } else { 0 } }
pub fn i8n(x: i32) -> u8 { let arr = [0u8; 0x80]; if x >= 0 && x < 0x80 { arr[(x as u8) as usize] } else { 0 } }
pub fn us8(x: usize) -> u8 { let arr = [0u8; 0x80]; if x < 0x80 { arr[(x as u8) as usize] } else { 0 } }
pub fn add_u8(x: u32) -> u8 { if x < 0x80 { (x as u8) + 0x7f } else { 0 } }
pub fn shl_u8(x: u32) -> u32 { if x < 8 { 1u32 << (x as u8) } else { 0 } }
// The 8-bit edge: `0x80u8 + 0x7f == 0xff` fits.
pub fn add_edge(x: u32) -> u8 { if x <= 0x80 { (x as u8) + 0x7f } else { 0 } }
