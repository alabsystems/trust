// CONTROL for interprocedural backing certification: the constructor claims a
// length ONE BYTE LARGER than the mapping (`len + 1`), so its establish
// obligation is `len < len + 1` — SATISFIABLE, i.e. NOT established. The struct
// is sealed (private `#[trust::backing]` fields) but NOT certified, so the
// use-site obligations must stay CAUGHT (fail-closed), never proved.
//
//   trustc -Z trust-verify-output=both --crate-type lib aterm_backing_oversized_control.rs
#![cfg_attr(trust_verify, feature(register_tool))]
#![cfg_attr(trust_verify, register_tool(trust))]
#![allow(dead_code)]

use std::slice;

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[cfg_attr(trust_verify, trust::backing)]
pub struct MmapMut {
    ptr: *const u8,
    len: usize,
}

impl MmapMut {
    // BUG: stores `len + 1` as the logical length over a `len`-byte mapping.
    // Establish `alloc_size(=len) >= len + 1` does NOT hold ⇒ not certified.
    pub unsafe fn map(len: usize) -> MmapMut {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        MmapMut { ptr: p as *const u8, len: len + 1 }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}
