//! Bit manipulation — parsers, checksums, codecs.
pub fn hi(x: u16) -> u8 { (x >> 8) as u8 }
pub fn lo(x: u16) -> u8 { (x & 0xff) as u8 }
pub fn join(h: u8, l: u8) -> u16 { ((h as u16) << 8) | (l as u16) }
pub fn mask(x: u32, bits: u32) -> u32 { if bits < 32 { x & ((1u32 << bits) - 1) } else { x } }
pub fn parity(x: u8) -> bool { x.count_ones() % 2 == 1 }
