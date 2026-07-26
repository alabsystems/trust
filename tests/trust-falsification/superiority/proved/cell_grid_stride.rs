#![crate_type = "lib"]
// Guarded multiplication: a row stride of at most 4096 columns at 64 bytes
// per cell stays far inside u32 (4096 * 64 = 262144). The arithmetic-safety
// obligation must be PROVED.
pub fn cell_grid_stride(cols: u32) -> u32 {
    if cols <= 4096 { cols * 64 } else { 4096 * 64 }
}
