// Demonstrates the obligations Trust now emits for the HIGH-2 unsafe class.
// Compile with:
//   trustc -Z trust-verify-output=both --crate-type lib high2_demo.rs

use std::ptr;

/// Pattern A: build a slice from a raw pointer + length. Trust must emit a
/// CopyBoundsViolation obligation (`len <= alloc_size`), not the old vacuous
/// `len < 0` check.
pub unsafe fn make_slice(p: *const u8, len: usize) -> &'static [u8] {
    std::slice::from_raw_parts(p, len)
}

/// Pattern B: raw bulk copy. Trust must emit CopyBoundsViolation for BOTH the
/// source (read) and destination (write) allocations, not just an overlap check.
pub unsafe fn copy_bytes(src: *const u8, dst: *mut u8, n: usize) {
    ptr::copy_nonoverlapping(src, dst, n);
}

/// An externally-mutable memory map. The callee path contains `mmap`, so Trust
/// must emit an ExternallyMutableAllocationBounds obligation (the captured
/// mapped length must be re-validated against the live size — the SIGBUS case).
mod mmap {
    pub fn map_mut(len: usize) -> *mut u8 {
        // stand-in for an mmap of a file region of `len` bytes
        let _ = len;
        core::ptr::null_mut()
    }
}

pub fn open_mapping(len: usize) -> *mut u8 {
    mmap::map_mut(len)
}
