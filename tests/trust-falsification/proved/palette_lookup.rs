#![crate_type = "lib"]
// Guarded array index: the 16-entry palette is only read below its length.
pub fn palette_lookup(palette: [u32; 16], i: usize) -> u32 {
    if i < 16 { palette[i] } else { 0 }
}
