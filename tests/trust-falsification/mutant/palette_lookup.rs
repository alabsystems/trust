#![crate_type = "lib"]
// MUTANT of proved/palette_lookup.rs: the `i < 16` guard is dropped, so the
// index can exceed the palette length. MUST be refused (exit 1).
pub fn palette_lookup(palette: [u32; 16], i: usize) -> u32 {
    palette[i]
}
