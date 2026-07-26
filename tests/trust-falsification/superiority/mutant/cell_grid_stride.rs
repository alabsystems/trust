#![crate_type = "lib"]
// MUTANT of proved/cell_grid_stride.rs: the `cols <= 4096` guard is dropped,
// so the multiplication overflows for large cols (e.g. cols = 2^26 gives
// 2^26 * 64 = 2^32 > u32::MAX). The verifier MUST refuse this (exit 1).
pub fn cell_grid_stride(cols: u32) -> u32 {
    cols * 64
}
